from hashlib import blake2s, sha256
from os import urandom

def from_bytes(f):
    return int.from_bytes(f, 'big')

def to_bytes(f, v):
    return int.to_bytes(f, v, 'big')

__all__ = ['confirm_included', 'confirm_included_already_hashed', 'confirm_not_included', 
        'confirm_not_included_already_hashed', 'MerkleSet']

"""
Advantages of this merkle tree implementation:
Lazy root calculation
Few l1 and l2 cache misses
Low CPU requirements
Good memory efficiency
Good interaction with normal memory allocators
Small proofs of inclusion/exclusion
Reasonably simple implementation
Reasonable defense against malicious insertion attacks

TODO: Port to C
TODO: Optimize! Benchmark!
TODO: Make sure that data structures don't get garbled on an out of memory error
TODO: Add an iterator
TODO: add multi-threading support
TODO: add support for continuous self-auditing
TODO: Try heuristically calculating hashes non-lazily when they're likely to be needed later
TODO: Try unrolling all this recursivity to improve performance
TODO: Maybe add a size counter
TODO: Add combining of multiproofs and looking up a whole multiproof at once

# The active child is the leaf where overflow is currently sent to
# When the active child is filled, a new empty one is made
# When a leaf overflows, the data is sent to the active child of the parent branch
# all unused should be zeroed out
branch: active_child 8 patricia[size]
patricia[n]: modified_hash 32 modified_hash 32 patricia[n-1] patricia[n-1]
# unused are zeroed out. If child is a branch pos is set to 0xFFFF
patricia[0]: child 8 pos 2
# modified_hash[0] & 0xC0 is the type
type: EMPTY or TERMINAL or MIDDLE or INVALID

# first_unused is the start of linked list, 0xFFFF for terminal
# num_inputs is the number of references from the parent branch into this leaf
leaf: first_unused 2 num_inputs 2 [node or emptynode]
# pos0 and pos1 are one based indexes to make it easy to detect if they are accidently cleared to zero
node: modified_hash 32 modified_hash 32 pos0 2 pos1 2
# next is a zero based index
emptynode: next 2 unused 66

# Unvalidated means two or more children if the sibling isn't empty
# Unvalidated means more than two children if the sibling is empty
# For a proof of exclusion when the sibling contains two things they 
# must both be given so validation can be performed
multiproof: subtree
subtree: middle or terminal or unvalidated or empty
middle: MIDDLE 1 subtree subtree
terminal: hash (terminal type) 32
unvalidated: hash (invalid type) 32
empty: EMPTY 1
"""

EMPTY = 0
TERMINAL = 0x40
MIDDLE = 0x80
INVALID = TERMINAL | MIDDLE

# Returned in branch updates when the terminal was unused
NOTSTARTED = 2
# Returned in removal when there's only one left
ONELEFT = 3
# Returned when there might be only two things below
# Bubbles upwards as long as there's an empty sibling
# When a non-empty sibling is hit, it calls catch on the layer below
# On catch, collapse is called on everything below
# Collapse returns None if it has more than two things, or both if both terminal
# If there is an empty child, collapse passes through the return of its non-empty child
# Collapse clears out if it's returning something other than None
FRAGILE = 4
INVALIDATING = 5
DONE = 6
FULL = 7

ERROR = bytes([INVALID]) + urandom(31)
BLANK = bytes([0] * 32)

def flip_terminal(mystr):
    assert len(mystr) == 32
    return bytes([TERMINAL | (mystr[0] & 0x3F)]) + mystr[1:]

def flip_middle(mystr):
    assert len(mystr) == 32
    return bytes([MIDDLE | (mystr[0] & 0x3F)]) + mystr[1:]

def flip_invalid(mystr):
    assert len(mystr) == 32
    return bytes([INVALID | (mystr[0] & 0x3F)]) + mystr[1:]

def hasher(mystr):
    assert len(mystr) == 64
    t0, t1 = get_type(mystr, 0), get_type(mystr, 32)
    assert t0 != INVALID and t1 != INVALID
    if (t0 == EMPTY or t0 == TERMINAL) and (t1 == EMPTY or t1 == TERMINAL):
        assert t0 == TERMINAL and t1 == TERMINAL
        assert mystr[:32] < mystr[32:]
    assert t0 != EMPTY or mystr[:32] == BLANK
    assert t1 != EMPTY or mystr[32:] == BLANK
    r = blake2s(bytes(mystr)).digest()
    return bytes([MIDDLE | (r[0] & 0x3F)]) + r[1:]

def get_type(mybytes, pos):
    return mybytes[pos] & INVALID

def make_invalid(mybytes, pos):
    assert get_type(mybytes, pos) != INVALID
    mybytes[pos] |= INVALID

def get_bit(mybytes, pos):
    assert len(mybytes) == 32
    pos += 2
    return (mybytes[pos // 8] >> (7 - (pos % 8))) & 1

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
    def __init__(self, depth, leaf_units):
        self.subblock_lengths = [10]
        while len(self.subblock_lengths) <= depth:
            self.subblock_lengths.append(64 + 2 * self.subblock_lengths[-1])
        self.leaf_units = leaf_units
        self.root = bytearray(32)
        # should be dumped completely on a port to C in favor of real dereferencing.
        self.pointers_to_arrays = {}
        self.rootblock = None

    def audit(self, hashes):
        newhashes = []
        t = get_type(self.root, 0)
        if t == EMPTY:
            assert self.root == BLANK
            assert self.rootblock == None
            assert len(self.pointers_to_arrays) == 0
        elif t == TERMINAL:
            assert self.rootblock == None
            assert len(self.pointers_to_arrays) == 0
            newhashes.append(self.root)
        else:
            allblocks = set()
            e = (self.root if t == MIDDLE else None)
            self._audit_branch(self._deref(self.rootblock), 0, allblocks, e, newhashes, True)
            assert allblocks == set(self.pointers_to_arrays.keys())
        s = sorted([flip_terminal(x) for x in hashes])
        assert newhashes == s

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
            assert bytes(output) in self.pointers_to_arrays
            if newpos == 0xFFFF:
                self._audit_branch(output, depth, allblocks, expected, hashes, can_terminate)
            else:
                outputs.setdefault(output, []).append((newpos, expected))
                self._add_hashes_leaf(self._ref(output), newpos, hashes, can_terminate)
            return
        t0 = get_type(branch, pos)
        t1 = get_type(branch, pos + 32)
        if expected is not None:
            assert t0 != INVALID and t1 != INVALID and hasher(branch[pos:pos + 64]) == expected
        if t0 == EMPTY:
            assert t1 != EMPTY and t1 != TERMINAL
            assert branch[pos:pos + 32] == BLANK
            self._audit_branch_inner_empty(branch, pos + 64, moddepth - 1)
        elif t0 == TERMINAL:
            assert can_terminate or t1 != TERMINAL
            assert t1 != EMPTY
            self._audit_branch_inner_empty(branch, pos + 64, moddepth - 1)
            hashes.append(branch[pos:pos + 32])
        else:
            e = (branch[pos:pos + 32] if t0 == MIDDLE else None)
            self._audit_branch_inner(branch, pos + 64, depth + 1, moddepth - 1, outputs, allblocks, e, hashes, t1 != EMPTY)
        if t1 == EMPTY:
            assert branch[pos + 32:pos + 64] == BLANK
            self._audit_branch_inner_empty(branch, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
        elif t1 == TERMINAL:
            self._audit_branch_inner_empty(branch, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            hashes.append(branch[pos + 32:pos + 64])
        else:
            e = (branch[pos + 32:pos + 64] if t1 == MIDDLE else None)
            self._audit_branch_inner(branch, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1, outputs, allblocks, e, hashes, t0 != EMPTY)

    def _add_hashes_leaf(self, leaf, pos, hashes, can_terminate):
        assert pos >= 0
        rpos = 4 + pos * 68
        t0 = get_type(leaf, rpos)
        t1 = get_type(leaf, rpos + 32)
        if t0 == TERMINAL:
            hashes.append(leaf[rpos:rpos + 32])
            assert can_terminate or t1 != TERMINAL
        elif t0 != EMPTY:
            self._add_hashes_leaf(leaf, from_bytes(leaf[rpos + 64:rpos + 66]) - 1, hashes, t1 != EMPTY)
        if t1 == TERMINAL:
            hashes.append(leaf[rpos + 32:rpos + 64])
        elif t1 != EMPTY:
            self._add_hashes_leaf(leaf, from_bytes(leaf[rpos + 66:rpos + 68]) - 1, hashes, t0 != EMPTY)

    def _audit_branch_inner_empty(self, branch, pos, moddepth):
        if moddepth == 0:
            assert branch[pos:pos + 10] == bytes(10)
            return
        assert branch[pos:pos + 64] == bytes(64)
        self._audit_branch_inner_empty(branch, pos + 64, moddepth - 1)
        self._audit_branch_inner_empty(branch, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)

    def _audit_whole_leaf(self, leaf, inputs):
        leaf = self._ref(leaf)
        assert len(leaf) == 4 + self.leaf_units * 68
        assert len(inputs) == from_bytes(leaf[2:4])
        # 88 is the ASCII value for 'X'
        mycopy = bytearray([88] * (4 + self.leaf_units * 68))
        for pos, expected in inputs:
            self._audit_whole_leaf_inner(leaf, mycopy, pos, expected)
        i = from_bytes(leaf[:2])
        while i != 0xFFFF:
            nexti = from_bytes(leaf[4 + i * 68:4 + i * 68 + 2])
            assert mycopy[4 + i * 68:4 + i * 68 + 68] == b'X' * 68
            mycopy[4 + i * 68:4 + i * 68 + 68] = bytes(68)
            mycopy[4 + i * 68:4 + i * 68 + 2] = to_bytes(nexti, 2)
            i = nexti
        assert mycopy[4:] == leaf[4:]

    def _audit_whole_leaf_inner(self, leaf, mycopy, pos, expected):
        assert pos >= 0
        rpos = 4 + pos * 68
        assert mycopy[rpos:rpos + 68] == b'X' * 68
        mycopy[rpos:rpos + 68] = leaf[rpos:rpos + 68]
        t0 = get_type(leaf, rpos)
        t1 = get_type(leaf, rpos + 32)
        if expected is not None:
            assert t0 != INVALID and t1 != INVALID and hasher(leaf[rpos:rpos + 64]) == expected
        if t0 == EMPTY:
            assert t1 != EMPTY
            assert t1 != TERMINAL
            assert leaf[rpos:rpos + 32] == BLANK
            assert leaf[rpos + 64:rpos + 66] == bytes(2)
        elif t0 == TERMINAL:
            assert t1 != EMPTY
            assert leaf[rpos + 64:rpos + 66] == bytes(2)
        else:
            e = (leaf[rpos:rpos + 32] if t0 == MIDDLE else None)
            self._audit_whole_leaf_inner(leaf, mycopy, from_bytes(leaf[rpos + 64:rpos + 66]) - 1, e)
        if t1 == EMPTY:
            assert leaf[rpos + 32:rpos + 64] == BLANK
            assert leaf[rpos + 66:rpos + 68] == bytes(2)
        elif t1 == TERMINAL:
            assert leaf[rpos + 66:rpos + 68] == bytes(2)
        else:
            e = (leaf[rpos + 32:rpos + 64] if t1 == MIDDLE else None)
            self._audit_whole_leaf_inner(leaf, mycopy, from_bytes(leaf[rpos + 66:rpos + 68]) - 1, e)

    def _allocate_branch(self):
        b = safearray(8 + self.subblock_lengths[-1])
        self.pointers_to_arrays[self._deref(b)] = b
        return b

    def _allocate_leaf(self):
        leaf = safearray(4 + self.leaf_units * 68)
        for i in range(self.leaf_units):
            p = 4 + i * 68
            leaf[p:p + 2] = to_bytes((i + 1) if i != self.leaf_units - 1 else 0xFFFF, 2)
        self.pointers_to_arrays[self._deref(leaf)] = leaf
        return leaf

    def _deallocate(self, thing):
        del self.pointers_to_arrays[self._deref(thing)]

    def _ref(self, ref):
        assert len(ref) == 8
        if ref == bytes(8):
            return None
        return self.pointers_to_arrays[bytes(ref)]

    def _deref(self, thing):
        assert thing is not None
        return to_bytes(id(thing), 8)

    def get_root(self):
        if get_type(self.root, 0) == INVALID:
            self.root[0:] = self._force_calculation_branch(self.rootblock, 8, len(self.subblock_lengths) - 1)
        return bytes(self.root)

    def _force_calculation_branch(self, block, pos, moddepth):
        if moddepth == 0:
            block2 = self._ref(block[pos:pos + 8])
            pos = from_bytes(block[pos + 8:pos + 10])
            if pos == 0xFFFF:
                return self._force_calculation_branch(block2, 8, len(self.subblock_lengths) - 1)
            else:
                return self._force_calculation_leaf(block2, pos)
        if get_type(block, pos) == INVALID:
            block[pos:pos + 32] = self._force_calculation_branch(block, pos + 64, moddepth - 1)
        if get_type(block, pos + 32) == INVALID:
            block[pos + 32:pos + 64] = self._force_calculation_branch(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
        return hasher(block[pos:pos + 64])

    def _force_calculation_leaf(self, block, pos):
        pos = 4 + pos * 68
        if get_type(block, pos) == INVALID:
            block[pos:pos + 32] = self._force_calculation_leaf(block, from_bytes(block[pos + 64:pos + 66]) - 1)
        if get_type(block, pos + 32) == INVALID:
            block[pos + 32:pos + 64] = self._force_calculation_leaf(block, from_bytes(block[pos + 66:pos + 68]) - 1)
        return hasher(block[pos:pos + 64])

    def add(self, toadd):
        return self.add_already_hashed(sha256(toadd).digest())

    def add_already_hashed(self, toadd):
        self._add(flip_terminal(toadd))

    def _add(self, toadd):
        t = get_type(self.root, 0)
        if t == EMPTY:
            self.root[0:] = toadd
        elif t == TERMINAL:
            if toadd == self.root:
                return
            self.rootblock = self._allocate_branch()
            self._insert_branch([self.root, toadd], self.rootblock, 8, 0, len(self.subblock_lengths) - 1)
            make_invalid(self.root, 0)
        else:
            if self._add_to_branch(toadd, self.rootblock, 0) == INVALIDATING and get_type(self.root, 0) != INVALID:
                make_invalid(self.root, 0)

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
            r = self._add_to_branch_inner(toadd, block, pos + 64, depth + 1, moddepth - 1)
            if r == INVALIDATING:
                if get_type(block, pos) != INVALID:
                    make_invalid(block, pos)
                    if get_type(block, pos + 32) != INVALID:
                        return INVALIDATING
                return DONE
            if r == DONE:
                return DONE
            t0 = get_type(block, pos)
            t1 = get_type(block, pos + 32)
            if t0 == EMPTY:
                if t1 == EMPTY:
                    return NOTSTARTED
                block[pos:pos + 32] = toadd
                if t1 != INVALID:
                    return INVALIDATING
                else:
                    return DONE
            assert t0 == TERMINAL
            v0 = block[pos:pos + 32]
            if v0 == toadd:
                return DONE
            if t1 == TERMINAL:
                v1 = block[pos + 32:pos + 64]
                if v1 == toadd:
                    return DONE
                block[pos + 32:pos + 64] = bytes(32)
                self._insert_branch([toadd, v0, v1], block, pos, depth, moddepth)
            else:
                self._insert_branch([toadd, v0], block, pos + 64, depth + 1, moddepth - 1)
                make_invalid(block, pos)
            if t1 != INVALID:
                return INVALIDATING
            else:
                return DONE
        else:
            r = self._add_to_branch_inner(toadd, block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
            if r == INVALIDATING:
                if get_type(block, pos + 32) != INVALID:
                    make_invalid(block, pos + 32)
                    if get_type(block, pos) != INVALID:
                        return INVALIDATING
                return DONE
            if r == DONE:
                return DONE
            t0 = get_type(block, pos)
            t1 = get_type(block, pos + 32)
            if t1 == EMPTY:
                if t0 == EMPTY:
                    return NOTSTARTED
                block[pos + 32:pos + 64] = toadd
                if t0 != INVALID:
                    return INVALIDATING
                else:
                    return DONE
            assert t1 == TERMINAL
            v1 = block[pos + 32:pos + 64]
            if v1 == toadd:
                return DONE
            if t0 == TERMINAL:
                v0 = block[pos:pos + 32]
                if v0 == toadd:
                    return DONE
                block[pos:pos + 32] = bytes(32)
                self._insert_branch([toadd, v0, v1], block, pos, depth, moddepth)
            else:
                self._insert_branch([toadd, v1], block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                make_invalid(block, pos + 32)
            if t0 != INVALID:
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
            block[pos:pos + 32] = things[0]
            block[pos + 32:pos + 64] = things[1]
            return
        bits = [get_bit(thing, depth) for thing in things]
        if bits[0] == bits[1] == bits[2]:
            if bits[0] == 0:
                self._insert_branch(things, block, pos + 64, depth + 1, moddepth - 1)
                make_invalid(block, pos)
            else:
                self._insert_branch(things, block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                make_invalid(block, pos + 32)
        else:
            if bits[0] == bits[1]:
                block[pos + 32:pos + 64] = things[2]
                self._insert_branch(things[:2], block, pos + 64, depth + 1, moddepth - 1)
                make_invalid(block, pos)
            else:
                block[pos:pos + 32] = things[0]
                self._insert_branch(things[1:], block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                make_invalid(block, pos + 32)

    # state can be INVALIDATING, DONE
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
        rpos = pos * 68 + 4
        if get_bit(toadd, depth) == 0:
            t = get_type(leaf, rpos)
            if t == EMPTY:
                leaf[rpos:rpos + 32] = toadd
                return INVALIDATING
            elif t == TERMINAL:
                oldval0 = leaf[rpos:rpos + 32]
                if oldval0 == toadd:
                    return DONE
                t1 = get_type(leaf, rpos + 32)
                if t1 == TERMINAL:
                    oldval1 = leaf[rpos + 32:rpos + 64]
                    if toadd == oldval1:
                        return DONE
                    nextpos = from_bytes(leaf[:2])
                    leaf[:2] = to_bytes(pos, 2)
                    leaf[rpos:rpos + 64] = bytes(64)
                    leaf[rpos:rpos + 2] = to_bytes(nextpos, 2)
                    r, nextnextpos = self._insert_leaf([toadd, oldval0, oldval1], leaf, depth)
                    if r == FULL:
                        leaf[:2] = to_bytes(nextpos, 2)
                        leaf[rpos:rpos + 32] = oldval0
                        leaf[rpos + 32:rpos + 64] = oldval1
                        return FULL
                    assert nextnextpos == pos
                    return INVALIDATING
                r, newpos = self._insert_leaf([toadd, oldval0], leaf, depth + 1)
                if r == FULL:
                    return FULL
                leaf[rpos + 64:rpos + 66] = to_bytes(newpos + 1, 2)
                make_invalid(leaf, rpos)
                if get_type(leaf, rpos + 32) == INVALID:
                    return DONE
                return INVALIDATING
            else:
                r = self._add_to_leaf_inner(toadd, leaf, from_bytes(leaf[rpos + 64:rpos + 66]) - 1, depth + 1)
                if r == INVALIDATING:
                    if t == MIDDLE:
                        make_invalid(leaf, rpos)
                        return INVALIDATING
                    return DONE
                return r
        else:
            t = get_type(leaf, rpos + 32)
            if t == EMPTY:
                leaf[rpos + 32:rpos + 64] = toadd
                return INVALIDATING
            elif t == TERMINAL:
                oldval1 = leaf[rpos + 32:rpos + 64]
                if oldval1 == toadd:
                    return DONE
                t0 = get_type(leaf, rpos)
                if t0 == TERMINAL:
                    oldval0 = leaf[rpos:rpos + 32]
                    if toadd == oldval0:
                        return DONE
                    nextpos = from_bytes(leaf[:2])
                    leaf[:2] = to_bytes(pos, 2)
                    leaf[rpos:rpos + 64] = bytes(64)
                    leaf[rpos:rpos + 2] = to_bytes(nextpos, 2)
                    r, nextnextpos = self._insert_leaf([toadd, oldval0, oldval1], leaf, depth)
                    if r == FULL:
                        leaf[:2] = to_bytes(nextpos, 2)
                        leaf[rpos:rpos + 32] = oldval0
                        leaf[rpos + 32:rpos + 64] = oldval1
                        return FULL
                    assert nextnextpos == pos
                    return INVALIDATING
                r, newpos = self._insert_leaf([toadd, oldval1], leaf, depth + 1)
                if r == FULL:
                    return FULL
                leaf[rpos + 66:rpos + 68] = to_bytes(newpos + 1, 2)
                make_invalid(leaf, rpos + 32)
                if get_type(leaf, rpos) == INVALID:
                    return DONE
                return INVALIDATING
            else:
                r = self._add_to_leaf_inner(toadd, leaf, from_bytes(leaf[rpos + 66:rpos + 68]) - 1, depth + 1)
                if r == INVALIDATING:
                    if t == MIDDLE:
                        make_invalid(leaf, rpos + 32)
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
        rfrompos = 4 + frompos * 68
        rtopos = 4 + topos * 68
        toleaf[0:2] = toleaf[rtopos:rtopos + 2]
        t0 = get_type(fromleaf, rfrompos)
        lowpos = None
        highpos = None
        if t0 == MIDDLE or t0 == INVALID:
            r, lowpos = self._copy_between_leafs_inner(fromleaf, toleaf, from_bytes(fromleaf[rfrompos + 64:rfrompos + 66]) - 1)
            if r == FULL:
                assert toleaf[:2] == toleaf[rtopos:rtopos + 2]
                toleaf[:2] = to_bytes(topos, 2)
                return FULL, None
        t1 = get_type(fromleaf, rfrompos + 32)
        if t1 == MIDDLE or t1 == INVALID:
            r, highpos = self._copy_between_leafs_inner(fromleaf, toleaf, from_bytes(fromleaf[rfrompos + 66:rfrompos + 68]) - 1)
            if r == FULL:
                if t0 == MIDDLE or t0 == INVALID:
                    self._delete_from_leaf(toleaf, lowpos)
                assert toleaf[:2] == toleaf[rtopos:rtopos + 2]
                toleaf[:2] = to_bytes(topos, 2)
                return FULL, None
        toleaf[rtopos:rtopos + 64] = fromleaf[rfrompos:rfrompos + 64]
        if lowpos is not None:
            toleaf[rtopos + 64:rtopos + 66] = to_bytes(lowpos + 1, 2)
        if highpos is not None:
            toleaf[rtopos + 66:rtopos + 68] = to_bytes(highpos + 1, 2)
        return DONE, topos

    def _delete_from_leaf(self, leaf, pos):
        assert pos >= 0
        rpos = 4 + pos * 68
        t = get_type(leaf, rpos)
        if t == MIDDLE or t == INVALID:
            self._delete_from_leaf(leaf, from_bytes(leaf[rpos + 64:rpos + 66]) - 1)
        t = get_type(leaf, rpos + 32)
        if t == MIDDLE or t == INVALID:
            self._delete_from_leaf(leaf, from_bytes(leaf[rpos + 66:rpos + 68]) - 1)
        leaf[rpos + 2:rpos + 68] = bytes(66)
        leaf[rpos:rpos + 2] = leaf[:2]
        leaf[:2] = to_bytes(pos, 2)

    def _copy_leaf_to_branch(self, branch, branchpos, moddepth, leaf, leafpos):
        assert leafpos >= 0
        rleafpos = 4 + leafpos * 68
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
        branch[branchpos:branchpos + 64] = leaf[rleafpos:rleafpos + 64]
        t = get_type(leaf, rleafpos)
        if t == MIDDLE or t == INVALID:
            self._copy_leaf_to_branch(branch, branchpos + 64, moddepth - 1, leaf, from_bytes(leaf[rleafpos + 64:rleafpos + 66]) - 1)
        t = get_type(leaf, rleafpos + 32)
        if t == MIDDLE or t == INVALID:
            self._copy_leaf_to_branch(branch, branchpos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1, leaf, from_bytes(leaf[rleafpos + 66:rleafpos + 68]) - 1)

    # returns (status, pos)
    # status can be INVALIDATING, FULL
    def _insert_leaf(self, things, leaf, depth):
        assert 2 <= len(things) <= 3
        for thing in things:
            assert len(thing) == 32
        pos = from_bytes(leaf[:2])
        if pos == 0xFFFF:
            return FULL, None
        lpos = pos * 68 + 4
        leaf[:2] = leaf[lpos:lpos + 2]
        things.sort()
        if len(things) == 2:
            leaf[lpos:lpos + 32] = things[0]
            leaf[lpos + 32:lpos + 64] = things[1]
            return INVALIDATING, pos
        bits = [get_bit(thing, depth) for thing in things]
        if bits[0] == bits[1] == bits[2]:
            r, laterpos = self._insert_leaf(things, leaf, depth + 1)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            if bits[0] == 0:
                leaf[lpos + 64:lpos + 66] = to_bytes(laterpos + 1, 2)
                make_invalid(leaf, lpos)
            else:
                leaf[lpos + 66:lpos + 68] = to_bytes(laterpos + 1, 2)
                make_invalid(leaf, lpos + 32)
                leaf[lpos:lpos + 2] = bytes(2)
            return INVALIDATING, pos
        elif bits[0] == bits[1]:
            r, laterpos = self._insert_leaf([things[0], things[1]], leaf, depth + 1)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            leaf[lpos + 32:lpos + 64] = things[2]
            leaf[lpos + 64:lpos + 66] = to_bytes(laterpos + 1, 2)
            make_invalid(leaf, lpos)
        else:
            r, laterpos = self._insert_leaf([things[1], things[2]], leaf, depth + 1)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            leaf[lpos:lpos + 32] = things[0]
            leaf[lpos + 66:lpos + 68] = to_bytes(laterpos + 1, 2)
            make_invalid(leaf, lpos + 32)
        return INVALIDATING, pos

    def remove(self, toremove):
        return self.remove_already_hashed(sha256(toremove).digest())

    def remove_already_hashed(self, toremove):
        return self._remove(flip_terminal(toremove))

    def _remove(self, toremove):
        t = get_type(self.root, 0)
        if t == EMPTY:
            return
        elif t == TERMINAL:
            if toremove == self.root:
                self.root[0:] = BLANK
            return
        else:
            status, oneval = self._remove_branch(toremove, self.rootblock, 0)
        if status == INVALIDATING:
            make_invalid(self.root, 0)
        elif status == ONELEFT:
            self.root[0:] = oneval
            self.rootblock = None
        elif status == FRAGILE:
            self._catch_branch(self.rootblock, 8, len(self.subblock_lengths) - 1)
            if get_type(self.root, 0) != INVALID:
                make_invalid(self.root, 0)

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
            r, val = self._remove_branch_inner(toremove, block, pos + 64, depth + 1, moddepth - 1)
            if r == NOTSTARTED:
                t = get_type(block, pos)
                if t == EMPTY:
                    if get_type(block, pos + 32) == EMPTY:
                        return NOTSTARTED, None
                    return DONE, None
                assert t == TERMINAL
                if block[pos:pos + 32] == toremove:
                    t1 = get_type(block, pos + 32)
                    if t1 == TERMINAL:
                        left = block[pos + 32:pos + 64]
                        block[pos:pos + 64] = bytes(64)
                        return ONELEFT, left
                    else:
                        assert t1 != EMPTY
                        block[pos:pos + 32] = bytes(32)
                        return FRAGILE, None
                elif block[pos + 32:pos + 64] == toremove:
                    left = block[pos:pos + 32]
                    block[pos:pos + 64] = bytes(64)
                    return ONELEFT, left
                return DONE, None
            elif r == ONELEFT:
                was_invalid = get_type(block, pos) == INVALID
                block[pos:pos + 32] = val
                if get_type(block, pos + 32) == TERMINAL:
                    return FRAGILE, None
                if not was_invalid:
                    return INVALIDATING, None
                else:
                    return DONE, None
            elif r == FRAGILE:
                t1 = get_type(block, pos + 32)
                # scan up the tree until the other child is non-empty
                if t1 == EMPTY:
                    if get_type(block, pos) != INVALID:
                        make_invalid(block, pos)
                    return FRAGILE, None
                # the other child is non-empty, if the tree can be collapsed
                # it will be up to the level below this one, so try that
                self._catch_branch(block, pos + 64, moddepth - 1)
                # done collasping, continue invalidating if neccessary
                if get_type(block, pos) == INVALID:
                    return DONE, None
                make_invalid(block, pos)
                if t1 == INVALID:
                    return DONE, None
                return INVALIDATING, None
            elif r == INVALIDATING:
                t = get_type(block, pos)
                if t == INVALID:
                    return DONE, None
                else:
                    assert t == MIDDLE
                    make_invalid(block, pos)
                    if get_type(block, pos + 32) == INVALID:
                        return DONE, None
                    return INVALIDATING, None
            assert r == DONE
            return r, val
        else:
            r, val = self._remove_branch_inner(toremove, block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
            if r == NOTSTARTED:
                t = get_type(block, pos + 32)
                if t == EMPTY:
                    if get_type(block, pos) == EMPTY:
                        return NOTSTARTED, None
                    return DONE, None
                assert t == TERMINAL
                if block[pos + 32:pos + 64] == toremove:
                    if get_type(block, pos) == TERMINAL:
                        left = block[pos:pos + 32]
                        block[pos:pos + 64] = bytes(64)
                        return ONELEFT, left
                    else:
                        block[pos + 32:pos + 64] = bytes(32)
                        return FRAGILE, None
                elif block[pos:pos + 32] == toremove:
                    left = block[pos + 32:pos + 64]
                    block[pos:pos + 64] = bytes(64)
                    return ONELEFT, left
                return DONE, None
            elif r == ONELEFT:
                was_invalid = get_type(block, pos + 32) == INVALID
                block[pos + 32:pos + 64] = val
                if get_type(block, pos) == TERMINAL:
                    return FRAGILE, None
                if not was_invalid:
                    return INVALIDATING, None
                return DONE, None
            elif r == FRAGILE:
                t0 = get_type(block, pos)
                if t0 == EMPTY:
                    if get_type(block, pos + 32) != INVALID:
                        make_invalid(block, pos + 32)
                    return FRAGILE, None
                self._catch_branch(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
                if get_type(block, pos + 32) == INVALID:
                    return DONE, None
                make_invalid(block, pos + 32)
                if t0 == INVALID:
                    return DONE, None
                return INVALIDATING, None
            elif r == INVALIDATING:
                t = get_type(block, pos + 32)
                if t == INVALID:
                    return DONE, None
                else:
                    assert t == MIDDLE
                    make_invalid(block, pos + 32)
                    if get_type(block, pos) == INVALID:
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
        rpos = 4 + pos * 68
        next = leaf[:2]
        leaf[rpos:rpos + 2] = leaf[:2]
        leaf[rpos + 2:rpos + 68] = bytes(66)
        leaf[:2] = to_bytes(pos, 2)

    # returns (status, oneval)
    # status can be ONELEFT, FRAGILE, INVALIDATING, DONE
    def _remove_leaf_inner(self, toremove, block, pos, depth):
        assert pos >= 0
        rpos = 4 + pos * 68
        if get_bit(toremove, depth) == 0:
            t = get_type(block, rpos)
            if t == EMPTY:
                return DONE, None
            if t == TERMINAL:
                t1 = get_type(block, rpos + 32)
                if block[rpos:rpos + 32] == toremove:
                    if t1 == TERMINAL:
                        left = block[rpos + 32:rpos + 64]
                        self._deallocate_leaf_node(block, pos)
                        return ONELEFT, left
                    block[rpos:rpos + 32] = bytes(32)
                    return FRAGILE, None
                if block[rpos + 32:rpos + 64] == toremove:
                    left = block[rpos:rpos + 32]
                    self._deallocate_leaf_node(block, pos)
                    return ONELEFT, left
                return DONE, None
            else:
                r, val = self._remove_leaf_inner(toremove, block, from_bytes(block[rpos + 64:rpos + 66]) - 1, depth + 1)
                if r == DONE:
                    return DONE, None
                if r == INVALIDATING:
                    if t == MIDDLE:
                        make_invalid(block, rpos)
                        if get_type(block, rpos + 32) != INVALID:
                            return INVALIDATING, None
                    return DONE, None
                if r == ONELEFT:
                    t1 = get_type(block, rpos + 32)
                    assert t1 != EMPTY
                    block[rpos:rpos + 32] = val
                    block[rpos + 64:rpos + 66] = bytes(2)
                    if t1 == TERMINAL:
                        return FRAGILE, None
                    if t != INVALID and t1 != INVALID:
                        return INVALIDATING, None
                    return DONE, None
                assert r == FRAGILE
                t1 = get_type(block, rpos + 32)
                if t1 == EMPTY:
                    if t != INVALID:
                        make_invalid(block, rpos)
                    return FRAGILE, None
                self._catch_leaf(block, from_bytes(block[rpos + 64:rpos + 66]) - 1)
                if t == INVALID:
                    return DONE, None
                make_invalid(block, rpos)
                if t1 == INVALID:
                    return DONE, None
                return INVALIDATING, None
        else:
            t = get_type(block, rpos + 32)
            if t == EMPTY:
                return DONE, None
            elif t == TERMINAL:
                t0 = get_type(block, rpos)
                if block[rpos + 32:rpos + 64] == toremove:
                    if t0 == TERMINAL:
                        left = block[rpos:rpos + 32]
                        self._deallocate_leaf_node(block, pos)
                        return ONELEFT, left
                    block[rpos + 32:rpos + 64] = bytes(32)
                    return FRAGILE, None
                if block[rpos:rpos + 32] == toremove:
                    left = block[rpos + 32:rpos + 64]
                    self._deallocate_leaf_node(block, pos)
                    return ONELEFT, left
                return DONE, None
            else:
                r, val = self._remove_leaf_inner(toremove, block, from_bytes(block[rpos + 66:rpos + 68]) - 1, depth + 1)
                if r == DONE:
                    return DONE, None
                if r == INVALIDATING:
                    if t == MIDDLE:
                        make_invalid(block, rpos + 32)
                        if get_type(block, rpos) != INVALID:
                            return INVALIDATING, None
                    return DONE, None
                if r == ONELEFT:
                    t0 = get_type(block, rpos)
                    assert t0 != EMPTY
                    block[rpos + 32:rpos + 64] = val
                    block[rpos + 66:rpos + 68] = bytes(2)
                    if t0 == TERMINAL:
                        return FRAGILE, None
                    if t != INVALID and t0 != INVALID:
                        return INVALIDATING, None
                    return DONE, None
                assert r == FRAGILE
                t0 = get_type(block, rpos)
                if t0 == EMPTY:
                    if t != INVALID:
                        make_invalid(block, rpos + 32)
                    return FRAGILE, None
                self._catch_leaf(block, from_bytes(block[rpos + 66:rpos + 68]) - 1)
                if get_type(block, rpos + 32) == INVALID:
                    return DONE, None
                make_invalid(block, rpos + 32)
                if t0 == INVALID:
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
        if get_type(block, pos) == EMPTY:
            assert get_type(block, pos + 32) != TERMINAL
            r = self._collapse_branch_inner(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            if r != None:
                block[pos:pos + 64] = r
            return
        if get_type(block, pos + 32) == EMPTY:
            assert get_type(block, pos) != TERMINAL
            r = self._collapse_branch_inner(block, pos + 64, moddepth - 1)
            if r != None:
                block[pos:pos + 64] = r

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
        t0 = get_type(block, pos)
        t1 = get_type(block, pos + 32)
        if t0 == TERMINAL and t1 == TERMINAL:
            r = block[pos:pos + 64]
            block[pos:pos + 64] = bytes(64)
            return r
        if t0 == EMPTY:
            r = self._collapse_branch_inner(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            if r != None:
                block[pos + 32:pos + 64] = bytes(32)
            return r
        if t1 == EMPTY:
            r = self._collapse_branch_inner(block, pos + 64, moddepth - 1)
            if r != None:
                block[pos:pos + 32] = bytes(32)
            return r
        return None

    def _catch_leaf(self, leaf, pos):
        assert pos >= 0
        rpos = 4 + pos * 68
        t0 = get_type(leaf, rpos)
        t1 = get_type(leaf, rpos + 32)
        if t0 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[rpos + 66:rpos + 68]) - 1)
            if r != None:
                leaf[rpos + 66:rpos + 68] = bytes(2)
                leaf[rpos:rpos + 64] = r
            return
        if t1 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[rpos + 64:rpos + 66]) - 1)
            if r != None:
                leaf[rpos + 64:rpos + 66] = bytes(2)
                leaf[rpos:rpos + 64] = r
            return

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
        rpos = 4 + pos * 68
        t0 = get_type(leaf, rpos)
        t1 = get_type(leaf, rpos + 32)
        r = None
        if t0 == TERMINAL and t1 == TERMINAL:
            r = leaf[rpos:rpos + 64]
        elif t0 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[rpos + 66:rpos + 68]) - 1)
        elif t1 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[rpos + 64:rpos + 66]) - 1)
        if r is not None:
            # this leaf node is being collapsed, deallocate it
            leaf[rpos + 2:rpos + 68] = bytes(66)
            leaf[rpos:rpos + 2] = leaf[:2]
            leaf[:2] = to_bytes(pos, 2)
        return r

    # returns (boolean, proof string)
    def is_included(self, tocheck):
        return self.is_included_already_hashed(sha256(tocheck).digest())

    # returns (boolean, proof string)
    def is_included_already_hashed(self, tocheck):
        return self._is_included(flip_terminal(tocheck))

    # returns (boolean, proof string)
    def _is_included(self, tocheck):
        buf = []
        self.get_root()
        t = get_type(self.root, 0)
        if t == EMPTY:
            return False, bytes([EMPTY])
        if t == TERMINAL:
            return tocheck == self.root, self.root
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
        buf.append(bytes([MIDDLE]))
        if block[pos:pos + 32] == tocheck or block[pos + 32:pos + 64] == tocheck:
            _finish_proof(block[pos:pos + 64], depth, buf)
            return True
        if get_bit(tocheck, depth) == 0:
            t = get_type(block, pos)
            if t == EMPTY or t == TERMINAL:
                _finish_proof(block[pos:pos + 64], depth, buf)
                return False
            assert t == MIDDLE
            r = self._is_included_branch(tocheck, block, pos + 64, depth + 1, moddepth - 1, buf)
            buf.append(_quick_summary(block[pos + 32:pos + 64]))
            return r
        else:
            t = get_type(block, pos + 32)
            if t == EMPTY or t == TERMINAL:
                _finish_proof(block[pos:pos + 64], depth, buf)
                return False
            assert t == MIDDLE
            buf.append(_quick_summary(block[pos:pos + 32]))
            return self._is_included_branch(tocheck, block, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1, buf)

    # returns boolean, appends to buf
    def _is_included_leaf(self, tocheck, block, pos, depth, buf):
        assert pos >= 0
        pos = 4 + pos * 68
        buf.append(bytes([MIDDLE]))
        if block[pos:pos + 32] == tocheck or block[pos + 32:pos + 64] == tocheck:
            _finish_proof(block[pos:pos + 64], depth, buf)
            return True
        if get_bit(tocheck, depth) == 0:
            t = get_type(block, pos)
            if t == EMPTY or t == TERMINAL:
                _finish_proof(block[pos:pos + 64], depth, buf)
                return False
            assert t == MIDDLE
            r = self._is_included_leaf(tocheck, block, from_bytes(block[pos + 64:pos + 66]) - 1, depth + 1, buf)
            buf.append(_quick_summary(block[pos + 32:pos + 64]))
            return r
        else:
            t = get_type(block, pos + 32)
            if t == EMPTY or t == TERMINAL:
                _finish_proof(block[pos:pos + 64], depth, buf)
                return False
            assert t == MIDDLE
            buf.append(_quick_summary(block[pos:pos + 32]))
            return self._is_included_leaf(tocheck, block, from_bytes(block[pos + 66:pos + 68]) - 1, depth + 1, buf)

def _finish_proof(val, depth, buf):
    v0 = val[:32]
    v1 = val[32:]
    if get_type(v0, 0) == TERMINAL and get_type(v1, 0) == TERMINAL:
        b0 = get_bit(v0, depth)
        b1 = get_bit(v1, depth)
        if b0 == b1:
            if b0 == 0:
                buf.append(bytes([MIDDLE]))
                _finish_proof(val, depth + 1, buf)
                buf.append(bytes([EMPTY]))
            else:
                buf.append(bytes([EMPTY]))
                buf.append(bytes([MIDDLE]))
                _finish_proof(val, depth + 1, buf)
            return
    buf.append(_quick_summary(v0))
    buf.append(_quick_summary(v1))

def _quick_summary(val):
    t = get_type(val, 0)
    if t == EMPTY:
        return bytes([EMPTY])
    if t == TERMINAL:
        return val
    assert t == MIDDLE
    return flip_invalid(val)

def confirm_included(root, val, proof):
    return confirm_not_included_already_hashed(root, sha256(val).digest(), proof)

def confirm_included_already_hashed(root, val, proof):
    return _confirm(root, val, proof, True)

def confirm_not_included(root, val, proof):
    return confirm_not_included_already_hashed(root, sha256(val).digest(), proof)

def confirm_not_included_already_hashed(root, val, proof):
    return _confirm(root, val, proof, False)

class SetError(BaseException):
    pass

def _confirm(root, val, proof, expected):
    try:
        p = deserialize_proof(proof)
        if p.get_root() != root:
            return False
        r, junk = p.is_included_already_hashed(val)
        return r == expected
    except SetError:
        return False

def deserialize_proof(proof):
    try:
        r, pos = _deserialize(proof, 0, [])
        if pos != len(proof):
            raise SetError()
        return ReferenceMerkleSet(r)
    except IndexError:
        raise SetError()

def _deserialize(proof, pos, bits):
    t = proof[pos] & INVALID
    if t == EMPTY:
        if proof[pos] != EMPTY:
            raise SetError()
        return _empty, pos + 1
    if t == TERMINAL:
        return TerminalNode(proof[pos:pos + 32], bits), pos + 32
    if t == INVALID:
        return UnknownNode(flip_middle(proof[pos:pos + 32])), pos + 32
    if proof[pos] != MIDDLE:
        raise SetError()
    v0, pos = _deserialize(proof, pos + 1, bits + [0])
    v1, pos = _deserialize(proof, pos, bits + [1])
    return MiddleNode([v0, v1]), pos

class ReferenceMerkleSet:
    def __init__(self, root = None):
        self.root = root
        if root is None:
            self.root = _empty

    def get_root(self):
        return self.root.hash

    def add_already_hashed(self, toadd):
        self.root = self.root.add(flip_terminal(toadd), 0)

    def remove_already_hashed(self, toremove):
        self.root = self.root.remove(flip_terminal(toremove), 0)

    def is_included_already_hashed(self, tocheck):
        tocheck = flip_terminal(tocheck)
        p = []
        r = self.root.is_included(tocheck, 0, p)
        return r, b''.join(p)

    def audit(self, hashes):
        newhashes = []
        self.root.audit(newhashes, [])
        assert newhashes == sorted(newhashes)
        assert newhashes == sorted([flip_terminal(x) for x in hashes])

class EmptyNode:
    def __init__(self):
        self.hash = BLANK

    def is_empty(self):
        return True

    def is_terminal(self):
        return False

    def is_double(self):
        raise SetError()

    def add(self, toadd, depth):
        return TerminalNode(toadd)

    def remove(self, toremove, depth):
        return self

    def is_included(self, tocheck, depth, p):
        p.append(bytes([EMPTY]))
        return False

    def other_included(self, tocheck, depth, p, collapse):
        p.append(bytes([EMPTY]))

    def audit(self, hashes, bits):
        pass

_empty = EmptyNode()

class TerminalNode:
    def __init__(self, hash, bits = None):
        assert len(hash) == 32
        self.hash = hash
        if bits is not None:
            self.audit([], bits)

    def is_empty(self):
        return False

    def is_terminal(self):
        return True

    def is_double(self):
        raise SetError()

    def add(self, toadd, depth):
        if toadd == self.hash:
            return self
        return self._make_middle([TerminalNode(min(self.hash, toadd)), TerminalNode(max(self.hash, toadd))], depth)

    def _make_middle(self, children, depth):
        cbits = [get_bit(children[i].hash, depth) for i in range(2)]
        if cbits[0] != cbits[1]:
            return MiddleNode(children)
        nextvals = [None, None]
        nextvals[cbits[0] ^ 1] = _empty
        nextvals[cbits[0]] = self._make_middle(children, depth + 1)
        return MiddleNode(nextvals)

    def remove(self, toremove, depth):
        if toremove == self.hash:
            return _empty
        return self

    def is_included(self, tocheck, depth, p):
        p.append(self.hash)
        return tocheck == self.hash

    def other_included(self, tocheck, depth, p, collapse):
        p.append(self.hash)

    def audit(self, hashes, bits):
        hashes.append(self.hash)
        for pos, v in enumerate(bits):
            assert get_bit(self.hash, pos) == v

class MiddleNode:
    def __init__(self, children):
        self.children = children
        for i in range(2):
            if self.children[i^1].is_empty() and self.children[i].is_double():
                self.hash = self.children[i].hash
                break
        else:
            if (children[0].is_empty() or children[0].is_terminal()) and (children[1].is_empty() or children[1].is_terminal()):
                if children[0].is_empty() or children[1].is_empty():
                    raise SetError()
                if children[0].hash >= children[1].hash:
                    raise SetError()
            r = blake2s(children[0].hash + children[1].hash).digest()
            self.hash = bytes([MIDDLE | (r[0] & 0x3F)]) + r[1:]

    def is_empty(self):
        return False

    def is_terminal(self):
        return False

    def is_double(self):
        for i in range(2):
            if self.children[i^1].is_empty():
                return self.children[i].is_double()
        return self.children[0].is_terminal() and self.children[1].is_terminal()

    def add(self, toadd, depth):
        bit = get_bit(toadd, depth)
        child = self.children[bit]
        newchild = child.add(toadd, depth + 1)
        if newchild is child:
            return self
        newvals = [x for x in self.children]
        newvals[bit] = newchild
        return MiddleNode(newvals)

    def remove(self, toremove, depth):
        bit = get_bit(toremove, depth)
        child = self.children[bit]
        newchild = child.remove(toremove, depth + 1)
        if newchild is child:
            return self
        otherchild = self.children[bit ^ 1]
        if newchild.is_empty() and otherchild.is_terminal():
            return otherchild
        if newchild.is_terminal() and otherchild.is_empty():
            return newchild
        newvals = [x for x in self.children]
        newvals[bit] = newchild
        return MiddleNode(newvals)

    def is_included(self, tocheck, depth, p):
        p.append(bytes([MIDDLE]))
        bit = get_bit(tocheck, depth)
        r = None
        for i in range(2):
            if bit == i:
                r = self.children[i].is_included(tocheck, depth + 1, p)
            else:
                self.children[i].other_included(tocheck, depth + 1, p, not self.children[i ^ 1].is_empty())
        return r

    def other_included(self, tocheck, depth, p, collapse):
        if collapse or not self.is_double():
            p.append(flip_invalid(self.hash))
        else:
            self.is_included(tocheck, depth, p)

    def audit(self, hashes, bits):
        for i in range(2):
            self.children[i].audit(hashes, bits + [i])

class UnknownNode:
    def __init__(self, hash):
        self.hash = hash

    def is_empty(self):
        return False

    def is_terminal(self):
        return False

    def is_double(self):
        return False

    def is_included(self, tocheck, depth, p):
        raise SetError()

    def other_included(self, tocheck, depth, p, collapse):
        p.append(flip_invalid(self.hash))

def _testlazy(numhashes, mset, roots, proofss):
    hashes = [blake2s(to_bytes(i, 10)).digest() for i in range(numhashes)]
    checkpoint = numhashes // 2
    for i in range(numhashes - 1):
        if i == checkpoint:
            r, proof = mset.is_included_already_hashed(hashes[checkpoint // 2])
            assert r
            assert proof == proofss[i][checkpoint // 2]
        mset.add_already_hashed(hashes[i])
        mset.audit(hashes[:i + 1])
    r, proof = mset.is_included_already_hashed(hashes[checkpoint])
    assert r
    assert proof == proofss[-1][checkpoint]
    for i in range(numhashes - 1, -1, -1):
        mset.remove_already_hashed(hashes[i])
        mset.audit(hashes[:i])
        if i == checkpoint or i == 0:
            assert roots[i] == mset.get_root()
            for j in range(numhashes):
                r, proof = mset.is_included_already_hashed(hashes[j])
                assert r == (j < i)
                assert proof == proofss[i][j]

def _testmset(numhashes, mset, oldroots = None, oldproofss = None):
    hashes = [blake2s(to_bytes(i, 10)).digest() for i in range(numhashes)]
    if oldroots is None:
        making_new = True
        roots = []
        proofss = []
    else:
        making_new = False
        roots = oldroots
        proofss = oldproofss
    assert mset.get_root() == BLANK
    mset.audit([])
    for i in range(numhashes):
        if not making_new:
            assert roots[i] == mset.get_root()
            proofs = proofss[i]
        else:
            roots.append(mset.get_root())
            proofs = []
        for j in range(numhashes):
            r, proof = mset.is_included_already_hashed(hashes[j])
            assert r == (j < i)
            if not making_new:
                assert proofss[i][j] == proof
            else:
                proofs.append(proof)
                if r:
                    assert confirm_included_already_hashed(roots[i], hashes[j], proof)
                else:
                    assert confirm_not_included_already_hashed(roots[i], hashes[j], proof)
        if i > 0:
            mset.add_already_hashed(hashes[i-1])
            mset.audit(hashes[:i])
            assert mset.get_root() == roots[i]
            for j in range(numhashes):
                r, proof = mset.is_included_already_hashed(hashes[j])
                assert proof == proofs[j]
                assert r == (j < i)
        mset.add_already_hashed(hashes[i])
        mset.audit(hashes[:i+1])
        proofss.append(proofs)
    mset.get_root()
    mset.audit(hashes)
    for i in range(numhashes - 1, -1, -1):
        for k in range(2):
            mset.remove_already_hashed(hashes[i])
            mset.audit(hashes[:i])
            assert roots[i] == mset.get_root()
            for j in range(numhashes):
                r, proof = mset.is_included_already_hashed(hashes[j])
                assert r == (j < i)
                assert proof == proofss[i][j]
    return roots, proofss

def testall():
    num = 200
    roots, proofss = _testmset(num, ReferenceMerkleSet())
    for i in range(1, 5):
        for j in range(6):
            _testmset(num, MerkleSet(i, 2 ** j), roots, proofss)
            _testlazy(num, MerkleSet(i, 2 ** j), roots, proofss)
