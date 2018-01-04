from hashlib import blake2s, sha256

from ReferenceMerkleSet import *
LAZY = TRUNCATED

__all__ = ['confirm_included', 'confirm_included_already_hashed', 'confirm_not_included', 
        'confirm_not_included_already_hashed', 'MerkleSet']

"""
The behavior of this implementation is semantically identical to the one in ReferenceMerkleSet

Advantages of this merkle tree implementation:
Lazy root calculation
Few l1 and l2 cache misses
Good memory efficiency
Reasonable defense against malicious insertion attacks

TODO: Port to C
TODO: Add combining of proofs and looking up a whole multiproof at once

Branch memory allocation data format:

# The active child is the leaf where overflow is currently sent to
# When the active child is filled, a new empty one is made
# When a leaf overflows, the data is sent to the active child of the parent branch
# all unused should be zeroed out
branch: active_child 8 patricia[size]
patricia[n]: type 1 hash 32 type 1 hash 32 patricia[n-1] patricia[n-1]
type: EMPTY or TERMINAL or MIDDLE or LAZY
EMPTY: \x00
TERMINAL: \x01
MIDDLE: \x02
LAZY: \x03
# unused are zeroed out. If child is a branch pos is set to 0xFFFF
patricia[0]: child 8 pos 2

Leaf memory allocation data format:

# first_unused is the start of linked list, 0xFFFF for terminal
# num_inputs is the number of references from the parent branch into this leaf
leaf: first_unused 2 num_inputs 2 [node or emptynode]
# pos0 and pos1 are one based indexes to make it easy to detect if they are accidently cleared to zero
node: type 1 hash 32 type 1 hash 32 pos0 2 pos1 2
# next is a zero based index
emptynode: next 2 unused 68
"""

# Returned in branch updates when the terminal was unused
NOTSTARTED = 4
# Returned in removal when there's only one left
ONELEFT = 5
# Fragile is returned when there might be only two things below
# Bubbles upwards as long as there's an empty sibling
# When a non-empty sibling is hit, it calls catch on the layer below
# On catch, collapse is called on everything below
# Collapse returns None if it has more than two things, or both if both terminal
# If there is an empty child, collapse passes through the return of its non-empty child
# Collapse clears out if it's returning something other than None
FRAGILE = 6
INVALIDATING = 7
DONE = 8
FULL = 9

def from_bytes(f):
    return int.from_bytes(f, 'big')

def to_bytes(f, v):
    return int.to_bytes(f, v, 'big')

# Sanity checking on top of the hash function
def hashaudit(mystr):
    assert len(mystr) == 66
    t0, t1 = mystr[0:1], mystr[33:34]
    assert t0 != LAZY and t1 != LAZY
    if (t0 == EMPTY or t0 == TERMINAL) and (t1 == EMPTY or t1 == TERMINAL):
        assert t0 == TERMINAL and t1 == TERMINAL
        assert mystr[1:33] < mystr[34:]
    assert t0 != EMPTY or mystr[1:33] == BLANK
    assert t1 != EMPTY or mystr[34:] == BLANK
    return hashdown(mystr)

# Bounds checking for the win
class safearray(bytearray):
    def __setitem__(self, index, thing):
        if type(index) is slice:
            start = index.start
            if start is None:
                start = 0
            stop = index.stop
            if stop is None:
                stop = len(self)
            assert index.step is None
            assert start >= 0
            assert stop >= 0
            assert start < len(self)
            assert stop <= len(self)
            assert stop - start == len(thing)
        else:
            assert index >= 0
            assert index < len(self)
        bytearray.__setitem__(self, index, thing)

class MerkleSet:
    # depth sets the size of branches, it's power of two scale with a smallest value of 0
    # leaf_units is the size of leaves, its smallest possible value is 1
    # Optimal values for both of those are heavily dependent on the memory architecture of 
    # the particular machine
    def __init__(self, depth, leaf_units):
        self.subblock_lengths = [10]
        while len(self.subblock_lengths) <= depth:
            self.subblock_lengths.append(66 + 2 * self.subblock_lengths[-1])
        self.leaf_units = leaf_units
        self.root = safearray(33)
        # should be dumped completely on a port to C in favor of real dereferencing.
        self.pointers_to_arrays = {}
        self.rootblock = None

    # Only used by test code, makes sure internal state is consistent
    def _audit(self, hashes):
        newhashes = []
        t = self.root[:1]
        if t == EMPTY:
            assert self.root[1:] == BLANK
            assert self.rootblock == None
            assert len(self.pointers_to_arrays) == 0
        elif t == TERMINAL:
            assert self.rootblock == None
            assert len(self.pointers_to_arrays) == 0
            newhashes.append(self.root[1:])
        else:
            allblocks = set()
            self._audit_branch(self._deref(self.rootblock), 0, allblocks, self.root, newhashes, True)
            assert allblocks == set(self.pointers_to_arrays.keys())
        assert newhashes == sorted(hashes)

    def _audit_branch(self, branch, depth, allblocks, expected, hashes, can_terminate):
        assert branch not in allblocks
        allblocks.add(branch)
        outputs = {}
        branch = self._ref(branch)
        assert len(branch) == 8 + self.subblock_lengths[-1]
        self._audit_branch_inner(branch, 8, depth, len(self.subblock_lengths) - 1, outputs, allblocks, expected, hashes, can_terminate)
        active = branch[:8]
        if active != bytes(8):
            assert bytes(active) in outputs
        for leaf, positions in outputs.items():
            assert leaf not in allblocks
            allblocks.add(leaf)
            self._audit_whole_leaf(leaf, positions)

    def _audit_branch_inner(self, branch, pos, depth, moddepth, outputs, allblocks, expected, hashes, can_terminate):
        if moddepth == 0:
            newpos = from_bytes(branch[pos + 8:pos + 10])
            output = bytes(branch[pos:pos + 8])
            assert output in self.pointers_to_arrays
            if newpos == 0xFFFF:
                self._audit_branch(output, depth, allblocks, expected, hashes, can_terminate)
            else:
                outputs.setdefault(output, []).append((newpos, expected))
                self._add_hashes_leaf(self._ref(output), newpos, hashes, can_terminate)
            return
        assert expected[:1] == LAZY or hashaudit(branch[pos:pos + 66]) == expected[1:]
        t0 = branch[pos:pos + 1]
        t1 = branch[pos + 33:pos + 34]
        if t0 == EMPTY:
            assert t1 != EMPTY and t1 != TERMINAL
            assert branch[pos + 1:pos + 33] == BLANK
        elif t0 == TERMINAL:
            assert can_terminate or t1 != TERMINAL
            assert t1 != EMPTY
        if t1 == EMPTY:
            assert branch[pos + 34:pos + 66] == BLANK
        if t0 == EMPTY or t0 == TERMINAL:
            self._audit_branch_inner_empty(branch, pos + 66, moddepth - 1)
            if t0 == TERMINAL:
                hashes.append(branch[pos + 1:pos + 33])
        else:
            self._audit_branch_inner(branch, pos + 66, depth + 1, moddepth - 1, outputs, allblocks, 
                branch[pos:pos + 33], hashes, t1 != EMPTY)
        if t1 == EMPTY or t1 == TERMINAL:
            self._audit_branch_inner_empty(branch, pos + 66 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            if t1 == TERMINAL:
                hashes.append(branch[pos + 34:pos + 66])
        else:
            self._audit_branch_inner(branch, pos + 66 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1, outputs, allblocks, 
                branch[pos + 33:pos + 66], hashes, t0 != EMPTY)

    def _add_hashes_leaf(self, leaf, pos, hashes, can_terminate):
        assert pos >= 0
        rpos = 4 + pos * 70
        t0 = leaf[rpos:rpos + 1]
        t1 = leaf[rpos + 33:rpos + 34]
        if t0 == TERMINAL:
            hashes.append(leaf[rpos + 1:rpos + 33])
            assert can_terminate or t1 != TERMINAL
        elif t0 != EMPTY:
            self._add_hashes_leaf(leaf, from_bytes(leaf[rpos + 66:rpos + 68]) - 1, hashes, t1 != EMPTY)
        if t1 == TERMINAL:
            hashes.append(leaf[rpos + 34:rpos + 66])
        elif t1 != EMPTY:
            self._add_hashes_leaf(leaf, from_bytes(leaf[rpos + 68:rpos + 70]) - 1, hashes, t0 != EMPTY)

    def _audit_branch_inner_empty(self, branch, pos, moddepth):
        if moddepth == 0:
            assert branch[pos:pos + 10] == bytes(10)
            return
        assert branch[pos:pos + 66] == bytes(66)
        self._audit_branch_inner_empty(branch, pos + 66, moddepth - 1)
        self._audit_branch_inner_empty(branch, pos + 66 + self.subblock_lengths[moddepth - 1], moddepth - 1)

    def _audit_whole_leaf(self, leaf, inputs):
        leaf = self._ref(leaf)
        assert len(leaf) == 4 + self.leaf_units * 70
        assert len(inputs) == from_bytes(leaf[2:4])
        mycopy = safearray([ord('X')] * (4 + self.leaf_units * 70))
        for pos, expected in inputs:
            self._audit_whole_leaf_inner(leaf, mycopy, pos, expected)
        i = from_bytes(leaf[:2])
        while i != 0xFFFF:
            nexti = from_bytes(leaf[4 + i * 70:4 + i * 70 + 2])
            assert mycopy[4 + i * 70:4 + i * 70 + 70] == b'X' * 70
            mycopy[4 + i * 70:4 + i * 70 + 70] = bytes(70)
            mycopy[4 + i * 70:4 + i * 70 + 2] = to_bytes(nexti, 2)
            i = nexti
        assert mycopy[4:] == leaf[4:]

    def _audit_whole_leaf_inner(self, leaf, mycopy, pos, expected):
        assert pos >= 0
        rpos = 4 + pos * 70
        assert mycopy[rpos:rpos + 70] == b'X' * 70
        mycopy[rpos:rpos + 70] = leaf[rpos:rpos + 70]
        t0 = leaf[rpos:rpos + 1]
        t1 = leaf[rpos + 33:rpos + 34]
        assert expected[:1] == LAZY or hashaudit(leaf[rpos:rpos + 66]) == expected[1:]
        if t0 == EMPTY:
            assert t1 != EMPTY
            assert t1 != TERMINAL
            assert leaf[rpos + 1:rpos + 33] == BLANK
            assert leaf[rpos + 66:rpos + 68] == bytes(2)
        elif t0 == TERMINAL:
            assert t1 != EMPTY
            assert leaf[rpos + 66:rpos + 68] == bytes(2)
        else:
            assert t0 == MIDDLE or t0 == LAZY
            self._audit_whole_leaf_inner(leaf, mycopy, from_bytes(leaf[rpos + 66:rpos + 68]) - 1, 
                leaf[rpos:rpos + 33])
        if t1 == EMPTY:
            assert leaf[rpos + 34:rpos + 66] == BLANK
            assert leaf[rpos + 68:rpos + 70] == bytes(2)
        elif t1 == TERMINAL:
            assert leaf[rpos + 68:rpos + 70] == bytes(2)
        else:
            assert t1 == MIDDLE or t1 == LAZY
            self._audit_whole_leaf_inner(leaf, mycopy, from_bytes(leaf[rpos + 68:rpos + 70]) - 1, 
                leaf[rpos + 33:rpos + 66])

    # In C this should be malloc/new
    def _allocate_branch(self):
        b = safearray(8 + self.subblock_lengths[-1])
        self.pointers_to_arrays[self._deref(b)] = b
        return b

    # In C this should be malloc/new
    def _allocate_leaf(self):
        leaf = safearray(4 + self.leaf_units * 70)
        for i in range(self.leaf_units):
            p = 4 + i * 70
            leaf[p:p + 2] = to_bytes((i + 1) if i != self.leaf_units - 1 else 0xFFFF, 2)
        self.pointers_to_arrays[self._deref(leaf)] = leaf
        return leaf

    # In C this should be calloc/free
    def _deallocate(self, thing):
        del self.pointers_to_arrays[self._deref(thing)]

    # In C this should be *
    def _ref(self, ref):
        assert len(ref) == 8
        if ref == bytes(8):
            return None
        return self.pointers_to_arrays[bytes(ref)]

    # In C this should be &
    def _deref(self, thing):
        assert thing is not None
        return to_bytes(id(thing), 8)

    def get_root(self):
        if self.root[:1] == LAZY:
            self.root[:] = self._force_calculation_branch(self.rootblock, 8, len(self.subblock_lengths) - 1)
        return compress_root(self.root)

    def _force_calculation_branch(self, block, pos, moddepth):
        if moddepth == 0:
            block2 = self._ref(block[pos:pos + 8])
            pos = from_bytes(block[pos + 8:pos + 10])
            if pos == 0xFFFF:
                return self._force_calculation_branch(block2, 8, len(self.subblock_lengths) - 1)
            else:
                return self._force_calculation_leaf(block2, pos)
        if block[pos:pos + 1] == LAZY:
            block[pos:pos + 33] = self._force_calculation_branch(block, pos + 66, moddepth - 1)
        if block[pos + 33:pos + 34] == LAZY:
            block[pos + 33:pos + 66] = self._force_calculation_branch(block, pos + 66 + self.subblock_lengths[moddepth - 1], moddepth - 1)
        return MIDDLE + hashaudit(block[pos:pos + 66])

    def _force_calculation_leaf(self, block, pos):
        pos = 4 + pos * 70
        if block[pos:pos + 1] == LAZY:
            block[pos:pos + 33] = self._force_calculation_leaf(block, from_bytes(block[pos + 66:pos + 68]) - 1)
        if block[pos + 33:pos + 34] == LAZY:
            block[pos + 33:pos + 66] = self._force_calculation_leaf(block, from_bytes(block[pos + 68:pos + 70]) - 1)
        return MIDDLE + hashaudit(block[pos:pos + 66])

    # Convenience function
    def add(self, toadd):
        return self.add_already_hashed(sha256(toadd).digest())

    def add_already_hashed(self, toadd):
        t = self.root[:1]
        if t == EMPTY:
            self.root[:] = TERMINAL + toadd
        elif t == TERMINAL:
            if toadd == self.root[1:]:
                return
            self.rootblock = self._allocate_branch()
            self._insert_branch([self.root[1:], toadd], self.rootblock, 8, 0, len(self.subblock_lengths) - 1)
            self.root[:1] = LAZY
        else:
            if self._add_to_branch(toadd, self.rootblock, 0) == INVALIDATING:
                self.root[:1] = LAZY

    # returns INVALIDATING, DONE
    def _add_to_branch(self, toadd, block, depth):
        return self._add_to_branch_inner(toadd, block, 8, depth, len(self.subblock_lengths) - 1)

    # returns NOTSTARTED, INVALIDATING, DONE
    def _add_to_branch_inner(self, toadd, block, pos, depth, moddepth):
        if moddepth == 0:
            nextblock = self._ref(block[pos:pos + 8])
            if nextblock is None:
                return NOTSTARTED
            nextpos = from_bytes(block[pos + 8:pos + 10])
            if nextpos == 0xFFFF:
                return self._add_to_branch(toadd, nextblock, depth)
            else:
                return self._add_to_leaf(toadd, block, pos, nextblock, nextpos, depth)
        if get_bit(toadd, depth) == 0:
            r = self._add_to_branch_inner(toadd, block, pos + 66, depth + 1, moddepth - 1)
            if r == INVALIDATING:
                if block[pos:pos + 1] != LAZY:
                    block[pos:pos + 1] = LAZY
                    if block[pos + 33:pos + 34] != LAZY:
                        return INVALIDATING
                return DONE
            if r == DONE:
                return DONE
            t0 = block[pos:pos + 1]
            t1 = block[pos + 33:pos + 34]
            if t0 == EMPTY:
                if t1 == EMPTY:
                    return NOTSTARTED
                block[pos:pos + 1] = TERMINAL
                block[pos + 1:pos + 33] = toadd
                if t1 != LAZY:
                    return INVALIDATING
                else:
                    return DONE
            assert t0 == TERMINAL
            v0 = block[pos + 1:pos + 33]
            if v0 == toadd:
                return DONE
            if t1 == TERMINAL:
                v1 = block[pos + 34:pos + 66]
                if v1 == toadd:
                    return DONE
                block[pos + 33:pos + 66] = bytes(33)
                self._insert_branch([toadd, v0, v1], block, pos, depth, moddepth)
            else:
                self._insert_branch([toadd, v0], block, pos + 66, depth + 1, moddepth - 1)
                block[pos:pos + 1] = LAZY
            if t1 != LAZY:
                return INVALIDATING
            else:
                return DONE
        else:
            r = self._add_to_branch_inner(toadd, block, pos + 66 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
            if r == INVALIDATING:
                if block[pos + 33:pos + 34] != LAZY:
                    block[pos + 33:pos + 34] = LAZY
                    if block[pos:pos + 1] != LAZY:
                        return INVALIDATING
                return DONE
            if r == DONE:
                return DONE
            t0 = block[pos:pos + 1]
            t1 = block[pos + 33:pos + 34]
            if t1 == EMPTY:
                if t0 == EMPTY:
                    return NOTSTARTED
                block[pos + 33:pos + 34] = TERMINAL
                block[pos + 34:pos + 66] = toadd
                if t0 != LAZY:
                    return INVALIDATING
                else:
                    return DONE
            assert t1 == TERMINAL
            v1 = block[pos + 34:pos + 66]
            if v1 == toadd:
                return DONE
            if t0 == TERMINAL:
                v0 = block[pos + 1:pos + 33]
                if v0 == toadd:
                    return DONE
                block[pos:pos + 33] = bytes(33)
                self._insert_branch([toadd, v0, v1], block, pos, depth, moddepth)
            else:
                self._insert_branch([toadd, v1], block, pos + 66 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                block[pos + 33:pos + 34] = LAZY
            if t0 != LAZY:
                return INVALIDATING
            else:
                return DONE

    def _insert_branch(self, things, block, pos, depth, moddepth):
        assert 2 <= len(things) <= 3
        if moddepth == 0:
            child = self._ref(block[:8])
            r = FULL
            if child is not None:
                r, leafpos = self._insert_leaf(things, child, depth)
            if r == FULL:
                child = self._allocate_leaf()
                r, leafpos = self._insert_leaf(things, child, depth)
                if r == FULL:
                    self._deallocate(child)
                    newb = self._allocate_branch()
                    block[pos:pos + 8] = self._deref(newb)
                    block[pos + 8:pos + 10] = to_bytes(0xFFFF, 2)
                    self._insert_branch(things, newb, 8, depth, len(self.subblock_lengths) - 1)
                    return
                block[:8] = self._deref(child)
            # increment the number of inputs in the active child
            child[2:4] = to_bytes(from_bytes(child[2:4]) + 1, 2)
            block[pos:pos + 8] = self._deref(child)
            block[pos + 8:pos + 10] = to_bytes(leafpos, 2)
            return
        things.sort()
        if len(things) == 2:
            block[pos:pos + 1] = TERMINAL
            block[pos + 1:pos + 33] = things[0]
            block[pos + 33:pos + 34] = TERMINAL
            block[pos + 34:pos + 66] = things[1]
            return
        bits = [get_bit(thing, depth) for thing in things]
        if bits[0] == bits[1] == bits[2]:
            if bits[0] == 0:
                self._insert_branch(things, block, pos + 66, depth + 1, moddepth - 1)
                block[pos:pos + 1] = LAZY
            else:
                self._insert_branch(things, block, pos + 66 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                block[pos + 33:pos + 34] = LAZY
        else:
            if bits[0] == bits[1]:
                block[pos + 33:pos + 34] = TERMINAL
                block[pos + 34:pos + 66] = things[2]
                self._insert_branch(things[:2], block, pos + 66, depth + 1, moddepth - 1)
                block[pos:pos + 1] = LAZY
            else:
                block[pos:pos + 1] = TERMINAL
                block[pos + 1:pos + 33] = things[0]
                self._insert_branch(things[1:], block, pos + 66 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                block[pos + 33:pos + 34] = LAZY

    # returns INVALIDATING, DONE
    def _add_to_leaf(self, toadd, branch, branchpos, leaf, leafpos, depth):
        r = self._add_to_leaf_inner(toadd, leaf, leafpos, depth)
        if r != FULL:
            return r
        if from_bytes(leaf[2:4]) == 1:
            # leaf is full and only has one input
            # it cannot be split so it must be replaced with a branch
            newb = self._allocate_branch()
            self._copy_leaf_to_branch(newb, 8, len(self.subblock_lengths) - 1, leaf, leafpos)
            self._add_to_branch(toadd, newb, depth)
            branch[branchpos:branchpos + 8] = self._deref(newb)
            branch[branchpos + 8:branchpos + 10] = to_bytes(0xFFFF, 2)
            if branch[:8] == self._deref(leaf):
                branch[:8] = bytes(8)
            self._deallocate(leaf)
            return INVALIDATING
        active = self._ref(branch[:8])
        if active is None or active is leaf:
            active = self._allocate_leaf()
        r, newpos = self._copy_between_leafs(leaf, active, leafpos)
        if r != DONE:
            active = self._allocate_leaf()
            r, newpos = self._copy_between_leafs(leaf, active, leafpos)
            assert r == DONE
        branch[branchpos:branchpos + 8] = self._deref(active)
        if branch[:8] != self._deref(active):
            branch[:8] = self._deref(active)
        branch[branchpos + 8:branchpos + 10] = to_bytes(newpos, 2)
        self._delete_from_leaf(leaf, leafpos)
        return self._add_to_leaf(toadd, branch, branchpos, active, newpos, depth)

    # returns INVALIDATING, DONE, FULL
    def _add_to_leaf_inner(self, toadd, leaf, pos, depth):
        assert pos >= 0
        rpos = pos * 70 + 4
        if get_bit(toadd, depth) == 0:
            t = leaf[rpos:rpos + 1]
            if t == EMPTY:
                leaf[rpos:rpos + 1] = TERMINAL
                leaf[rpos + 1:rpos + 33] = toadd
                return INVALIDATING
            elif t == TERMINAL:
                oldval0 = leaf[rpos + 1:rpos + 33]
                if oldval0 == toadd:
                    return DONE
                t1 = leaf[rpos + 33:rpos + 34]
                if t1 == TERMINAL:
                    oldval1 = leaf[rpos + 34:rpos + 66]
                    if toadd == oldval1:
                        return DONE
                    nextpos = from_bytes(leaf[:2])
                    leaf[:2] = to_bytes(pos, 2)
                    leaf[rpos + 2:rpos + 66] = bytes(64)
                    leaf[rpos:rpos + 2] = to_bytes(nextpos, 2)
                    r, nextnextpos = self._insert_leaf([toadd, oldval0, oldval1], leaf, depth)
                    if r == FULL:
                        leaf[:2] = to_bytes(nextpos, 2)
                        leaf[rpos:rpos + 1] = TERMINAL
                        leaf[rpos + 1:rpos + 33] = oldval0
                        leaf[rpos + 33:rpos + 34] = TERMINAL
                        leaf[rpos + 34:rpos + 66] = oldval1
                        return FULL
                    assert nextnextpos == pos
                    return INVALIDATING
                r, newpos = self._insert_leaf([toadd, oldval0], leaf, depth + 1)
                if r == FULL:
                    return FULL
                leaf[rpos + 66:rpos + 68] = to_bytes(newpos + 1, 2)
                leaf[rpos:rpos + 1] = LAZY
                if t1 == LAZY:
                    return DONE
                return INVALIDATING
            else:
                r = self._add_to_leaf_inner(toadd, leaf, from_bytes(leaf[rpos + 66:rpos + 68]) - 1, depth + 1)
                if r == INVALIDATING:
                    if t == MIDDLE:
                        leaf[rpos:rpos + 1] = LAZY
                        return INVALIDATING
                    return DONE
                return r
        else:
            t = leaf[rpos + 33:rpos + 34]
            if t == EMPTY:
                leaf[rpos + 33:rpos + 34] = TERMINAL
                leaf[rpos + 34:rpos + 66] = toadd
                return INVALIDATING
            elif t == TERMINAL:
                oldval1 = leaf[rpos + 34:rpos + 66]
                if oldval1 == toadd:
                    return DONE
                t0 = leaf[rpos:rpos + 1]
                if t0 == TERMINAL:
                    oldval0 = leaf[rpos + 1:rpos + 33]
                    if toadd == oldval0:
                        return DONE
                    nextpos = from_bytes(leaf[:2])
                    leaf[:2] = to_bytes(pos, 2)
                    leaf[rpos + 2:rpos + 66] = bytes(64)
                    leaf[rpos:rpos + 2] = to_bytes(nextpos, 2)
                    r, nextnextpos = self._insert_leaf([toadd, oldval0, oldval1], leaf, depth)
                    if r == FULL:
                        leaf[:2] = to_bytes(nextpos, 2)
                        leaf[rpos:rpos + 1] = TERMINAL
                        leaf[rpos + 1:rpos + 33] = oldval0
                        leaf[rpos + 33:rpos + 34] = TERMINAL
                        leaf[rpos + 34:rpos + 66] = oldval1
                        return FULL
                    assert nextnextpos == pos
                    return INVALIDATING
                r, newpos = self._insert_leaf([toadd, oldval1], leaf, depth + 1)
                if r == FULL:
                    return FULL
                leaf[rpos + 68:rpos + 70] = to_bytes(newpos + 1, 2)
                leaf[rpos + 33:rpos + 34] = LAZY
                if t0 == LAZY:
                    return DONE
                return INVALIDATING
            else:
                r = self._add_to_leaf_inner(toadd, leaf, from_bytes(leaf[rpos + 68:rpos + 70]) - 1, depth + 1)
                if r == INVALIDATING:
                    if t == MIDDLE:
                        leaf[rpos + 33:rpos + 34] = LAZY
                        return INVALIDATING
                    return DONE
                return r

    # returns state, newpos
    # state can be FULL, DONE
    def _copy_between_leafs(self, fromleaf, toleaf, frompos):
        r, pos = self._copy_between_leafs_inner(fromleaf, toleaf, frompos)
        if r == DONE:
            toleaf[2:4] = to_bytes(from_bytes(toleaf[2:4]) + 1, 2)
            fromleaf[2:4] = to_bytes(from_bytes(fromleaf[2:4]) - 1, 2)
        return r, pos

    # returns state, newpos
    # state can be FULL, DONE
    def _copy_between_leafs_inner(self, fromleaf, toleaf, frompos):
        topos = from_bytes(toleaf[:2])
        if topos == 0xFFFF:
            return FULL, None
        rfrompos = 4 + frompos * 70
        rtopos = 4 + topos * 70
        toleaf[0:2] = toleaf[rtopos:rtopos + 2]
        t0 = fromleaf[rfrompos:rfrompos + 1]
        lowpos = None
        highpos = None
        if t0 == MIDDLE or t0 == LAZY:
            r, lowpos = self._copy_between_leafs_inner(fromleaf, toleaf, from_bytes(fromleaf[rfrompos + 66:rfrompos + 68]) - 1)
            if r == FULL:
                assert toleaf[:2] == toleaf[rtopos:rtopos + 2]
                toleaf[:2] = to_bytes(topos, 2)
                return FULL, None
        t1 = fromleaf[rfrompos + 33:rfrompos + 34]
        if t1 == MIDDLE or t1 == LAZY:
            r, highpos = self._copy_between_leafs_inner(fromleaf, toleaf, from_bytes(fromleaf[rfrompos + 68:rfrompos + 70]) - 1)
            if r == FULL:
                if t0 == MIDDLE or t0 == LAZY:
                    self._delete_from_leaf(toleaf, lowpos)
                assert toleaf[:2] == toleaf[rtopos:rtopos + 2]
                toleaf[:2] = to_bytes(topos, 2)
                return FULL, None
        toleaf[rtopos:rtopos + 66] = fromleaf[rfrompos:rfrompos + 66]
        if lowpos is not None:
            toleaf[rtopos + 66:rtopos + 68] = to_bytes(lowpos + 1, 2)
        if highpos is not None:
            toleaf[rtopos + 68:rtopos + 70] = to_bytes(highpos + 1, 2)
        return DONE, topos

    def _delete_from_leaf(self, leaf, pos):
        assert pos >= 0
        rpos = 4 + pos * 70
        t = leaf[rpos:rpos + 1]
        if t == MIDDLE or t == LAZY:
            self._delete_from_leaf(leaf, from_bytes(leaf[rpos + 66:rpos + 68]) - 1)
        t = leaf[rpos + 33:rpos + 34]
        if t == MIDDLE or t == LAZY:
            self._delete_from_leaf(leaf, from_bytes(leaf[rpos + 68:rpos + 70]) - 1)
        leaf[rpos + 2:rpos + 70] = bytes(68)
        leaf[rpos:rpos + 2] = leaf[:2]
        leaf[:2] = to_bytes(pos, 2)

    def _copy_leaf_to_branch(self, branch, branchpos, moddepth, leaf, leafpos):
        assert leafpos >= 0
        rleafpos = 4 + leafpos * 70
        if moddepth == 0:
            active = self._ref(branch[:8])
            if active is None:
                active = self._allocate_leaf()
                branch[0:8] = self._deref(active)
            r, newpos = self._copy_between_leafs_inner(leaf, active, leafpos)
            assert r == DONE
            active[2:4] = to_bytes(from_bytes(active[2:4]) + 1, 2)
            branch[branchpos:branchpos + 8] = self._deref(active)
            branch[branchpos + 8:branchpos + 10] = to_bytes(newpos, 2)
            return
        branch[branchpos:branchpos + 66] = leaf[rleafpos:rleafpos + 66]
        t = leaf[rleafpos:rleafpos + 1]
        if t == MIDDLE or t == LAZY:
            self._copy_leaf_to_branch(branch, branchpos + 66, moddepth - 1, leaf, from_bytes(leaf[rleafpos + 66:rleafpos + 68]) - 1)
        t = leaf[rleafpos + 33:rleafpos + 34]
        if t == MIDDLE or t == LAZY:
            self._copy_leaf_to_branch(branch, branchpos + 66 + self.subblock_lengths[moddepth - 1], moddepth - 1, leaf, from_bytes(leaf[rleafpos + 68:rleafpos + 70]) - 1)

    # returns (status, pos)
    # status can be INVALIDATING, FULL
    def _insert_leaf(self, things, leaf, depth):
        assert 2 <= len(things) <= 3
        pos = from_bytes(leaf[:2])
        if pos == 0xFFFF:
            return FULL, None
        lpos = pos * 70 + 4
        leaf[:2] = leaf[lpos:lpos + 2]
        things.sort()
        if len(things) == 2:
            leaf[lpos:lpos + 1] = TERMINAL
            leaf[lpos + 1:lpos + 33] = things[0]
            leaf[lpos + 33:lpos + 34] = TERMINAL
            leaf[lpos + 34:lpos + 66] = things[1]
            return INVALIDATING, pos
        bits = [get_bit(thing, depth) for thing in things]
        if bits[0] == bits[1] == bits[2]:
            r, laterpos = self._insert_leaf(things, leaf, depth + 1)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            if bits[0] == 0:
                leaf[lpos + 66:lpos + 68] = to_bytes(laterpos + 1, 2)
                leaf[lpos:lpos + 1] = LAZY
            else:
                leaf[lpos + 68:lpos + 70] = to_bytes(laterpos + 1, 2)
                leaf[lpos + 33:lpos + 34] = LAZY
                leaf[lpos:lpos + 2] = bytes(2)
            return INVALIDATING, pos
        elif bits[0] == bits[1]:
            r, laterpos = self._insert_leaf([things[0], things[1]], leaf, depth + 1)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            leaf[lpos + 34:lpos + 66] = things[2]
            leaf[lpos + 33:lpos + 34] = TERMINAL
            leaf[lpos + 66:lpos + 68] = to_bytes(laterpos + 1, 2)
            leaf[lpos:lpos + 1] = LAZY
        else:
            r, laterpos = self._insert_leaf([things[1], things[2]], leaf, depth + 1)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            leaf[lpos + 1:lpos + 33] = things[0]
            leaf[lpos:lpos + 1] = TERMINAL
            leaf[lpos + 68:lpos + 70] = to_bytes(laterpos + 1, 2)
            leaf[lpos + 33:lpos + 34] = LAZY
        return INVALIDATING, pos

    # Convenience function
    def remove(self, toremove):
        return self.remove_already_hashed(sha256(toremove).digest())

    def remove_already_hashed(self, toremove):
        t = self.root[:1]
        if t == EMPTY:
            return
        elif t == TERMINAL:
            if toremove == self.root[1:]:
                self.root[:] = bytes(33)
            return
        else:
            status, oneval = self._remove_branch(toremove, self.rootblock, 0)
        if status == INVALIDATING:
            self.root[:1] = LAZY
        elif status == ONELEFT:
            self.root[1:] = oneval
            self.root[:1] = TERMINAL
            self.rootblock = None
        elif status == FRAGILE:
            self._catch_branch(self.rootblock, 8, len(self.subblock_lengths) - 1)
            self.root[:1] = LAZY

    # returns (status, oneval)
    # status can be ONELEFT, FRAGILE, INVALIDATING, DONE
    def _remove_branch(self, toremove, block, depth):
        result, val = self._remove_branch_inner(toremove, block, 8, depth, len(self.subblock_lengths) - 1)
        assert result != NOTSTARTED
        if result == ONELEFT:
            self._deallocate(block)
        return result, val

    # returns (status, oneval)
    # status can be NOTSTARTED, ONELEFT, FRAGILE, INVALIDATING, DONE
    def _remove_branch_inner(self, toremove, block, pos, depth, moddepth):
        if moddepth == 0:
            if block[pos:pos + 8] == bytes(8):
                return NOTSTARTED, None
            p = from_bytes(block[pos + 8:pos + 10])
            if p == 0xFFFF:
                r, val = self._remove_branch(toremove, self._ref(block[pos:pos + 8]), depth)
            else:
                r, val = self._remove_leaf(toremove, self._ref(block[pos:pos + 8]), p, depth, block)
            if r == ONELEFT:
                block[pos:pos + 10] = bytes(10)
            return r, val
        if get_bit(toremove, depth) == 0:
            r, val = self._remove_branch_inner(toremove, block, pos + 66, depth + 1, moddepth - 1)
            if r == NOTSTARTED:
                t = block[pos:pos + 1]
                if t == EMPTY:
                    if block[pos + 33:pos + 34] == EMPTY:
                        return NOTSTARTED, None
                    return DONE, None
                assert t == TERMINAL
                if block[pos + 1:pos + 33] == toremove:
                    t1 = block[pos + 33:pos + 34]
                    if t1 == TERMINAL:
                        left = block[pos + 34:pos + 66]
                        block[pos:pos + 66] = bytes(66)
                        return ONELEFT, left
                    else:
                        assert t1 != EMPTY
                        block[pos:pos + 33] = bytes(33)
                        return FRAGILE, None
                elif block[pos + 34:pos + 66] == toremove:
                    left = block[pos + 1:pos + 33]
                    block[pos:pos + 66] = bytes(66)
                    return ONELEFT, left
                return DONE, None
            elif r == ONELEFT:
                was_invalid = block[pos:pos + 1] == LAZY
                block[pos + 1:pos + 33] = val
                block[pos:pos + 1] = TERMINAL
                if block[pos + 33:pos + 34] == TERMINAL:
                    return FRAGILE, None
                if not was_invalid:
                    return INVALIDATING, None
                else:
                    return DONE, None
            elif r == FRAGILE:
                t1 = block[pos + 33:pos + 34]
                # scan up the tree until the other child is non-empty
                if t1 == EMPTY:
                    block[pos:pos + 1] = LAZY
                    return FRAGILE, None
                # the other child is non-empty, if the tree can be collapsed
                # it will be up to the level below this one, so try that
                self._catch_branch(block, pos + 66, moddepth - 1)
                # done collasping, continue invalidating if neccessary
                if block[pos:pos + 1] == LAZY:
                    return DONE, None
                block[pos:pos + 1] = LAZY
                if t1 == LAZY:
                    return DONE, None
                return INVALIDATING, None
            elif r == INVALIDATING:
                t = block[pos:pos + 1]
                if t == LAZY:
                    return DONE, None
                else:
                    assert t == MIDDLE
                    block[pos:pos + 1] = LAZY
                    if block[pos + 33:pos + 34] == LAZY:
                        return DONE, None
                    return INVALIDATING, None
            assert r == DONE
            return r, val
        else:
            r, val = self._remove_branch_inner(toremove, block, pos + 66 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
            if r == NOTSTARTED:
                t = block[pos + 33:pos + 34]
                if t == EMPTY:
                    if block[pos:pos + 1] == EMPTY:
                        return NOTSTARTED, None
                    return DONE, None
                assert t == TERMINAL
                if block[pos + 34:pos + 66] == toremove:
                    if block[pos:pos + 1] == TERMINAL:
                        left = block[pos + 1:pos + 33]
                        block[pos:pos + 66] = bytes(66)
                        return ONELEFT, left
                    else:
                        block[pos + 33:pos + 66] = bytes(33)
                        return FRAGILE, None
                elif block[pos + 1:pos + 33] == toremove:
                    left = block[pos + 34:pos + 66]
                    block[pos:pos + 66] = bytes(66)
                    return ONELEFT, left
                return DONE, None
            elif r == ONELEFT:
                was_invalid = block[pos + 33:pos + 34] == LAZY
                block[pos + 34:pos + 66] = val
                block[pos + 33:pos + 34] = TERMINAL
                if block[pos:pos + 1] == TERMINAL:
                    return FRAGILE, None
                if not was_invalid:
                    return INVALIDATING, None
                return DONE, None
            elif r == FRAGILE:
                t0 = block[pos:pos + 1]
                if t0 == EMPTY:
                    block[pos + 33:pos + 34] = LAZY
                    return FRAGILE, None
                self._catch_branch(block, pos + 66 + self.subblock_lengths[moddepth - 1], moddepth - 1)
                if block[pos + 33:pos + 34] == LAZY:
                    return DONE, None
                block[pos + 33:pos + 34] = LAZY
                if t0 == LAZY:
                    return DONE, None
                return INVALIDATING, None
            elif r == INVALIDATING:
                t = block[pos + 33:pos + 34]
                if t == LAZY:
                    return DONE, None
                else:
                    assert t == MIDDLE
                    block[pos + 33:pos + 34] = LAZY
                    if block[pos:pos + 1] == LAZY:
                        return DONE, None
                    return INVALIDATING, None
            assert r == DONE
            return r, val

    # returns (status, oneval)
    # status can be ONELEFT, FRAGILE, INVALIDATING, DONE
    def _remove_leaf(self, toremove, block, pos, depth, branch):
        result, val = self._remove_leaf_inner(toremove, block, pos, depth)
        if result == ONELEFT:
            numin = from_bytes(block[2:4])
            if numin == 1:
                self._deallocate(block)
                if branch[:8] == self._deref(block):
                    branch[:8] = bytes(8)
            else:
                block[2:4] = to_bytes(numin - 1, 2)
        return result, val

    def _deallocate_leaf_node(self, leaf, pos):
        assert pos >= 0
        rpos = 4 + pos * 70
        next = leaf[:2]
        leaf[rpos:rpos + 2] = leaf[:2]
        leaf[rpos + 2:rpos + 70] = bytes(68)
        leaf[:2] = to_bytes(pos, 2)

    # returns (status, oneval)
    # status can be ONELEFT, FRAGILE, INVALIDATING, DONE
    def _remove_leaf_inner(self, toremove, block, pos, depth):
        assert pos >= 0
        rpos = 4 + pos * 70
        if get_bit(toremove, depth) == 0:
            t = block[rpos:rpos + 1]
            if t == EMPTY:
                return DONE, None
            if t == TERMINAL:
                t1 = block[rpos + 33:rpos + 34]
                if block[rpos + 1:rpos + 33] == toremove:
                    if t1 == TERMINAL:
                        left = block[rpos + 34:rpos + 66]
                        self._deallocate_leaf_node(block, pos)
                        return ONELEFT, left
                    block[rpos:rpos + 33] = bytes(33)
                    return FRAGILE, None
                if block[rpos + 34:rpos + 66] == toremove:
                    left = block[rpos + 1:rpos + 33]
                    self._deallocate_leaf_node(block, pos)
                    return ONELEFT, left
                return DONE, None
            else:
                r, val = self._remove_leaf_inner(toremove, block, from_bytes(block[rpos + 66:rpos + 68]) - 1, depth + 1)
                if r == DONE:
                    return DONE, None
                if r == INVALIDATING:
                    if t == MIDDLE:
                        block[rpos:rpos + 1] = LAZY
                        if block[rpos + 33:rpos + 34] != LAZY:
                            return INVALIDATING, None
                    return DONE, None
                if r == ONELEFT:
                    t1 = block[rpos + 33:rpos + 34]
                    assert t1 != EMPTY
                    block[rpos + 1:rpos + 33] = val
                    block[rpos:rpos + 1] = TERMINAL
                    block[rpos + 66:rpos + 68] = bytes(2)
                    if t1 == TERMINAL:
                        return FRAGILE, None
                    if t != LAZY and t1 != LAZY:
                        return INVALIDATING, None
                    return DONE, None
                assert r == FRAGILE
                t1 = block[rpos + 33:rpos + 34]
                if t1 == EMPTY:
                    if t != LAZY:
                        block[rpos:rpos + 1] = LAZY
                    return FRAGILE, None
                self._catch_leaf(block, from_bytes(block[rpos + 66:rpos + 68]) - 1)
                if t == LAZY:
                    return DONE, None
                block[rpos:rpos + 1] = LAZY
                if t1 == LAZY:
                    return DONE, None
                return INVALIDATING, None
        else:
            t = block[rpos + 33:rpos + 34]
            if t == EMPTY:
                return DONE, None
            elif t == TERMINAL:
                t0 = block[rpos:rpos + 1]
                if block[rpos + 34:rpos + 66] == toremove:
                    if t0 == TERMINAL:
                        left = block[rpos + 1:rpos + 33]
                        self._deallocate_leaf_node(block, pos)
                        return ONELEFT, left
                    block[rpos + 33:rpos + 66] = bytes(33)
                    return FRAGILE, None
                if block[rpos + 1:rpos + 33] == toremove:
                    left = block[rpos + 34:rpos + 66]
                    self._deallocate_leaf_node(block, pos)
                    return ONELEFT, left
                return DONE, None
            else:
                r, val = self._remove_leaf_inner(toremove, block, from_bytes(block[rpos + 68:rpos + 70]) - 1, depth + 1)
                if r == DONE:
                    return DONE, None
                if r == INVALIDATING:
                    if t == MIDDLE:
                        block[rpos + 33:rpos + 34] = LAZY
                        if block[rpos:rpos + 1] != LAZY:
                            return INVALIDATING, None
                    return DONE, None
                if r == ONELEFT:
                    t0 = block[rpos:rpos + 1]
                    assert t0 != EMPTY
                    block[rpos + 34:rpos + 66] = val
                    block[rpos + 33:rpos + 34] = TERMINAL
                    block[rpos + 68:rpos + 70] = bytes(2)
                    if t0 == TERMINAL:
                        return FRAGILE, None
                    if t != LAZY and t0 != LAZY:
                        return INVALIDATING, None
                    return DONE, None
                assert r == FRAGILE
                t0 = block[rpos:rpos + 1]
                if t0 == EMPTY:
                    if t != LAZY:
                        block[rpos + 33:rpos + 34] = LAZY
                    return FRAGILE, None
                self._catch_leaf(block, from_bytes(block[rpos + 68:rpos + 70]) - 1)
                if t == LAZY:
                    return DONE, None
                block[rpos + 33:rpos + 34] = LAZY
                if t0 == LAZY:
                    return DONE, None
                return INVALIDATING, None

    def _catch_branch(self, block, pos, moddepth):
        if moddepth == 0:
            leafpos = from_bytes(block[pos + 8:pos + 10])
            if leafpos == 0xFFFF:
                self._catch_branch(self._ref(block[pos:pos + 8]), 8, len(self.subblock_lengths) - 1)
            else:
                self._catch_leaf(self._ref(block[pos:pos + 8]), leafpos)
            return
        if block[pos:pos + 1] == EMPTY:
            assert block[pos + 33:pos + 34] != TERMINAL
            r = self._collapse_branch_inner(block, pos + 66 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            if r != None:
                block[pos:pos + 66] = r
            return
        if block[pos + 33:pos + 34] == EMPTY:
            assert block[pos:pos + 1] != TERMINAL
            r = self._collapse_branch_inner(block, pos + 66, moddepth - 1)
            if r != None:
                block[pos:pos + 66] = r

    # returns two hashes string or None
    def _collapse_branch(self, block):
        r = self._collapse_branch_inner(block, 8, len(self.subblock_lengths) - 1)
        if r != None:
            self._deallocate(block)
        return r

    # returns two hashes string or None
    def _collapse_branch_inner(self, block, pos, moddepth):
        if moddepth == 0:
            leafpos = from_bytes(block[pos + 8:pos + 10])
            if leafpos == 0xFFFF:
                r = self._collapse_branch(self._ref(block[pos:pos + 8]))
            else:
                r = self._collapse_leaf(self._ref(block[pos:pos + 8]), from_bytes(block[pos + 8:pos + 10]), block)
            if r != None:
                block[pos:pos + 10] = bytes(10)
            return r
        t0 = block[pos:pos + 1]
        t1 = block[pos + 33:pos + 34]
        if t0 == TERMINAL and t1 == TERMINAL:
            r = block[pos:pos + 66]
            block[pos:pos + 66] = bytes(66)
            return r
        if t0 == EMPTY:
            r = self._collapse_branch_inner(block, pos + 66 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            if r != None:
                block[pos + 33:pos + 66] = bytes(33)
            return r
        if t1 == EMPTY:
            r = self._collapse_branch_inner(block, pos + 66, moddepth - 1)
            if r != None:
                block[pos:pos + 33] = bytes(33)
            return r
        return None

    def _catch_leaf(self, leaf, pos):
        assert pos >= 0
        rpos = 4 + pos * 70
        t0 = leaf[rpos:rpos + 1]
        t1 = leaf[rpos + 33:rpos + 34]
        if t0 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[rpos + 68:rpos + 70]) - 1)
            if r != None:
                leaf[rpos + 68:rpos + 70] = bytes(2)
                leaf[rpos:rpos + 66] = r
        elif t1 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[rpos + 66:rpos + 68]) - 1)
            if r != None:
                leaf[rpos + 66:rpos + 68] = bytes(2)
                leaf[rpos:rpos + 66] = r

    # returns two hashes string or None
    def _collapse_leaf(self, leaf, pos, branch):
        assert pos >= 0
        r = self._collapse_leaf_inner(leaf, pos)
        if r != None:
            inputs = from_bytes(leaf[2:4])
            if inputs == 1:
                self._deallocate(leaf)
                if branch[:8] == self._deref(leaf):
                    branch[:8] = bytes(8)
                return r
            leaf[2:4] = to_bytes(inputs - 1, 2)
        return r

    # returns two hashes string or None
    def _collapse_leaf_inner(self, leaf, pos):
        assert pos >= 0
        rpos = 4 + pos * 70
        t0 = leaf[rpos:rpos + 1]
        t1 = leaf[rpos + 33:rpos + 34]
        r = None
        if t0 == TERMINAL and t1 == TERMINAL:
            r = leaf[rpos:rpos + 66]
        elif t0 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[rpos + 68:rpos + 70]) - 1)
        elif t1 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[rpos + 66:rpos + 68]) - 1)
        if r is not None:
            # this leaf node is being collapsed, deallocate it
            leaf[rpos + 2:rpos + 70] = bytes(68)
            leaf[rpos:rpos + 2] = leaf[:2]
            leaf[:2] = to_bytes(pos, 2)
        return r

    # Convenience function
    def is_included(self, tocheck):
        return self.is_included_already_hashed(sha256(tocheck).digest())

    # returns (boolean, proof string)
    def is_included_already_hashed(self, tocheck):
        buf = []
        self.get_root()
        t = self.root[:1]
        if t == EMPTY:
            return False, EMPTY
        if t == TERMINAL:
            return tocheck == self.root[1:], self.root
        assert t == MIDDLE
        r = self._is_included_branch(tocheck, self.rootblock, 8, 0, len(self.subblock_lengths) - 1, buf)
        return r, b''.join([bytes(x) for x in buf])

    # returns boolean, appends to buf
    def _is_included_branch(self, tocheck, block, pos, depth, moddepth, buf):
        if moddepth == 0:
            if block[pos + 8:pos + 10] == bytes([0xFF, 0xFF]):
                return self._is_included_branch(tocheck, self._ref(block[pos:pos + 8]), 8, depth, len(self.subblock_lengths) - 1, buf)
            else:
                return self._is_included_leaf(tocheck, self._ref(block[pos:pos + 8]), from_bytes(block[pos + 8:pos + 10]), depth, buf)
        buf.append(MIDDLE)
        if block[pos + 1:pos + 33] == tocheck or block[pos + 34:pos + 66] == tocheck:
            _finish_proof(block[pos:pos + 66], depth, buf)
            return True
        if get_bit(tocheck, depth) == 0:
            t = block[pos:pos + 1]
            if t == EMPTY or t == TERMINAL:
                _finish_proof(block[pos:pos + 66], depth, buf)
                return False
            assert t == MIDDLE
            r = self._is_included_branch(tocheck, block, pos + 66, depth + 1, moddepth - 1, buf)
            buf.append(_quick_summary(block[pos + 33:pos + 66]))
            return r
        else:
            t = block[pos + 33:pos + 34]
            if t == EMPTY or t == TERMINAL:
                _finish_proof(block[pos:pos + 66], depth, buf)
                return False
            assert t == MIDDLE
            buf.append(_quick_summary(block[pos:pos + 33]))
            return self._is_included_branch(tocheck, block, pos + 66 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1, buf)

    # returns boolean, appends to buf
    def _is_included_leaf(self, tocheck, block, pos, depth, buf):
        assert pos >= 0
        pos = 4 + pos * 70
        buf.append(MIDDLE)
        if block[pos + 1:pos + 33] == tocheck or block[pos + 34:pos + 66] == tocheck:
            _finish_proof(block[pos:pos + 66], depth, buf)
            return True
        if get_bit(tocheck, depth) == 0:
            t = block[pos:pos + 1]
            if t == EMPTY or t == TERMINAL:
                _finish_proof(block[pos:pos + 66], depth, buf)
                return False
            assert t == MIDDLE
            r = self._is_included_leaf(tocheck, block, from_bytes(block[pos + 66:pos + 68]) - 1, depth + 1, buf)
            buf.append(_quick_summary(block[pos + 33:pos + 66]))
            return r
        else:
            t = block[pos + 33:pos + 34]
            if t == EMPTY or t == TERMINAL:
                _finish_proof(block[pos:pos + 66], depth, buf)
                return False
            assert t == MIDDLE
            buf.append(_quick_summary(block[pos:pos + 33]))
            return self._is_included_leaf(tocheck, block, from_bytes(block[pos + 68:pos + 70]) - 1, depth + 1, buf)

def _finish_proof(val, depth, buf):
    assert len(val) == 66
    v0 = val[1:33]
    v1 = val[34:]
    if val[:1] == TERMINAL and val[33:34] == TERMINAL:
        b0 = get_bit(v0, depth)
        b1 = get_bit(v1, depth)
        if b0 == b1:
            if b0 == 0:
                buf.append(MIDDLE)
                _finish_proof(val, depth + 1, buf)
                buf.append(EMPTY)
            else:
                buf.append(EMPTY)
                buf.append(MIDDLE)
                _finish_proof(val, depth + 1, buf)
            return
    buf.append(_quick_summary(val[:33]))
    buf.append(_quick_summary(val[33:]))

def _quick_summary(val):
    assert len(val) == 33
    t = val[:1]
    if t == EMPTY:
        return EMPTY
    if t == TERMINAL:
        return val
    assert t == MIDDLE
    return LAZY + val[1:]
