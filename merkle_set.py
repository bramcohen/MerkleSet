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
TODO: add multi-threading support
TODO: add support for continuous self-auditing
TODO: Try heuristically calculating hashes non-lazily when they're likely to be needed later
TODO: Try unrolling all this recursivity to improve performance
TODO: Maybe add a size counter

# all unused should be zeroed out
branch: active_child 8 patricia[size]
patricia[n]: modified_hash 32 modified_hash 32 patricia[n-1] patricia[n-1]
# unused are zeroed out. If child is a branch pos is set to 0xFFFF
patricia[0]: child 8 pos 2
# modified_hash[0] & 0xC0 is the type
type: EMPTY or TERMINAL or MIDDLE or INVALID

# first_unused is the start of linked list, 0xFFFF for terminal
leaf: first_unused 2 num_inputs 2 [node or emptynode]
node: modified_hash 32 modified_hash 32 pos0 2 pos1 2
emptynode: next 2 unused 66

# empty and singleton always have proofs of length 0
clusion_proof: [unit]
unit: give0 or give1 or empty0 or empty1 or giveboth
give0: GIVE0 1 modified_hash 32
give1: GIVE1 1 modified_hash 32
# optional hash included at end of proof of exclusion
empty0: EMPTY0 1 (modified_hash 32)
empty1: EMPTY1 1 (modified_hash 32)
giveboth: GIVEBOTH 1 modified_hash 32 modified_hash 32
"""

EMPTY = 0
TERMINAL = 0x40
MIDDLE = 0x80
INVALID = TERMINAL | MIDDLE

GIVE0 = 0
GIVE1 = 1
GIVEBOTH = 2
EMPTY0 = 3
EMPTY1 = 4

NOTSTARTED = 2
ONELEFT = 3
FRAGILE = 4
INVALIDATING = 5
DONE = 6
FULL = 7

ERROR = bytes([INVALID]) + urandom(31)
BLANK = bytes([0] * 32)
JUNK = bytes([INVALID] * 32)

def flip_terminal(mystr):
    assert len(mystr) == 32
    return bytes([TERMINAL | (mystr[0] & 0x3F)]) + mystr[1:]

def hasher(mystr, can_terminate = True, bits = None, can_fail = False):
    assert len(mystr) == 64
    if mystr[:32] == ERROR or mystr[32:] == ERROR:
        return ERROR
    t0, t1 = get_type(mystr, 0), get_type(mystr, 32)
    if t0 == INVALID or t1 == INVALID:
        assert can_fail
        return ERROR
    if bits is not None:
        if t0 == TERMINAL:
            s0 = mystr[:32]
            for pos, v in enumerate(bits):
                if get_bit(s0, pos) != v:
                    assert can_fail
                    return ERROR
            if t1 != TERMINAL:
                if get_bit(s0, len(bits)) != 0:
                    assert can_fail
                    return ERROR
        if t1 == TERMINAL:
            s1 = mystr[32:]
            for pos, v in enumerate(bits):
                if get_bit(s1, pos) != v:
                    assert can_fail
                    return ERROR
            if t0 != TERMINAL:
                if get_bit(s1, len(bits)) != 1:
                    assert can_fail
                    return ERROR
    if t0 == TERMINAL and t1 == TERMINAL and (mystr[:32] >= mystr[32:] or not can_terminate):
        assert can_fail
        return ERROR
    if (t0 == TERMINAL and t1 == EMPTY) or (t0 == EMPTY and t1 == TERMINAL):
        assert can_fail
        return ERROR
    if t0 == EMPTY:
        if mystr[:32] != BLANK or t1 == EMPTY:
            assert can_fail
            return ERROR
        v = mystr[63] & 0xF
        if v == 0 or v == 0xF:
            v = mystr[63] & 0xF0
            if v != 0 and v != 0xF0:
                return mystr[32:63] + bytes([mystr[63] & 0x0F])
        else:
            return mystr[32:63] + bytes([mystr[63] & 0xF0])
    elif t1 == EMPTY:
        if mystr[32:] != BLANK:
            assert can_fail
            return ERROR
        v = mystr[31] & 0xF
        if v == 0 or v == 0xF:
            v = mystr[31] & 0xF0
            if v != 0 and v != 0xF0:
                return mystr[:31] + bytes([mystr[31] | 0xF0])
        else:
            return mystr[:31] + bytes([mystr[31] | 0x0F])
    r = blake2s(mystr).digest()
    return bytes([MIDDLE | (r[0] & 0x3F)]) + r[1:]

def get_type(mybytes, pos):
    return mybytes[pos] & INVALID

def make_invalid(mybytes, pos):
    mybytes[pos] |= INVALID

def get_bit(mybytes, pos):
    pos += 2
    return (mybytes[pos // 8] >> (7 - (pos % 8))) & 1

def confirm_included(root, val, proof):
    return confirm_included_already_hashed(root, sha256(val).digest(), proof)

def confirm_included_already_hashed(root, val, proof):
    return _confirm_included(root, flip_terminal(val), proof)

def _confirm_included(root, val, proof):
    assert len(root) == 32
    a = get_type(root, 0)
    if a == TERMINAL:
        if len(proof) != 0:
            return False
        return root == val
    elif a == MIDDLE:
        return root == _find_implied_root_inclusion([], proof, val)
    else:
        return False

def _find_implied_root_inclusion(bits, proof, val, can_terminate = True):
    if len(bits) > 240:
        return ERROR
    if len(proof) == 0:
        return ERROR
    t = proof[0]
    if t == GIVE0:
        if get_bit(val, len(bits)) == 0:
            if len(proof) != 33:
                return ERROR
            return hasher(proof[1:] + val, can_terminate, bits, True)
        if len(proof) < 33:
            return ERROR
        if len(proof) == 33:
            return hasher(proof[1:33] + val, can_terminate, bits, True)
        return hasher(proof[1:33] + _find_implied_root_inclusion(bits + [1], proof[33:], val), False, bits, True)
    elif t == GIVE1:
        if get_bit(val, len(bits)) == 1:
            if len(proof) != 33:
                return ERROR
            return hasher(val + proof[1:], can_terminate, bits, True)
        if len(proof) < 33:
            return ERROR
        if len(proof) == 33:
            return hasher(val + proof[1:33], can_terminate, bits, True)
        return hasher(_find_implied_root_inclusion(bits + [0], proof[33:], val) + proof[1:33], False, bits, True)
    elif t == EMPTY0:
        return hasher(BLANK + _find_implied_root_inclusion(bits + [1], proof[1:], val, False), False, bits, True)
    elif t == EMPTY1:
        return hasher(_find_implied_root_inclusion(bits + [0], proof[1:], val, False) + BLANK, False, bits, True)
    else:
        return ERROR

def confirm_not_included(root, val, proof):
    return confirm_not_included_already_hashed(root, sha256(val).digest(), proof)

def confirm_not_included_already_hashed(root, val, proof):
    return _confirm_not_included(root, flip_terminal(val), proof)

def _confirm_not_included(root, val, proof):
    assert len(root) == 32 and len(val) == 32
    a = get_type(root, 0)
    if a == TERMINAL:
        if len(proof) != 0:
            return False
        return root != val
    elif a == EMPTY:
        if len(proof) != 0:
            return False
        return True
    elif a == MIDDLE:
        return root == _find_implied_root_exclusion([], proof, val)
    else:
        return False

def _find_implied_root_exclusion(bits, proof, val, can_terminate = True):
    if len(bits) > 240:
        return ERROR
    if len(proof) == 0:
        return ERROR
    t = proof[0]
    if t == GIVE0:
        if len(proof) < 33 or get_bit(val, len(bits)) == 0:
            return ERROR
        return hasher(proof[1:33] + _find_implied_root_exclusion(bits + [1], proof[33:], val), can_terminate, bits, True)
    elif t == GIVE1:
        if len(proof) < 33 or get_bit(val, len(bits)) == 1:
            return ERROR
        return hasher(_find_implied_root_exclusion(bits + [0], proof[33:], val) + proof[1:33], can_terminate, bits, True)
    elif t == GIVEBOTH:
        if len(proof) != 65:
            return ERROR
        if val == proof[1:33] or val == proof[33:]:
            return ERROR
        if get_bit(val, len(bits)) == 0:
            if get_type(proof, 1) != TERMINAL:
                return ERROR
        else:
            if get_type(proof, 33) != TERMINAL:
                return ERROR
        return hasher(proof[1:], can_terminate, bits, True)
    elif t == EMPTY0:
        if get_bit(val, len(bits)) == 0:
            if len(proof) != 33:
                return ERROR
            return hasher(BLANK + proof[1:33], False, bits, True)
        else:
            return hasher(BLANK + _find_implied_root_exclusion(bits + [1], proof[1:], val, False), False, bits, True)
    elif t == EMPTY1:
        if get_bit(val, len(bits)) == 1:
            if len(proof) != 33:
                return ERROR
            return hasher(proof[1:] + BLANK, False, bits, True)
        else:
            return hasher(_find_implied_root_exclusion(bits + [0], proof[1:], val, False) + BLANK, False, bits, True)
    else:
        return ERROR

class MerkleSet:
    def __init__(self, depth, leaf_units):
        self.subblock_lengths = [10]
        while len(self.subblock_lengths) <= depth:
            self.subblock_lengths.append(64 + 2 * self.subblock_lengths[-1])
        self.leaf_units = leaf_units
        self.root = BLANK
        # should be dumped completely on a port to C in favor of real dereferencing.
        self.pointers_to_arrays = {}
        self.rootblock = None

    def audit(self):
        t = get_type(self.root, 0)
        if t == EMPTY:
            assert self.root == BLANK
            assert self.rootblock == None
            assert len(self.pointers_to_arrays) == 0
        elif t == TERMINAL:
            assert self.rootblock == None
            assert len(self.pointers_to_arrays) == 0
        else:
            allblocks = set()
            e = (self.root if t == MIDDLE else None)
            self._audit_branch(self._deref(self.rootblock), 0, allblocks, e)
            assert allblocks == set(self.pointers_to_arrays.keys())

    def _audit_branch(self, branch, depth, allblocks, expected):
        assert branch not in allblocks
        allblocks.add(branch)
        outputs = {}
        branch = self._ref(branch)
        self._audit_branch_inner(branch, 8, depth, len(self.subblock_lengths) - 1, outputs, allblocks, expected)
        active = branch[:8]
        if active != bytes(8):
            assert active in outputs
        for leaf, positions in outputs.items():
            assert leaf not in allblocks
            allblocks.add(leaf)
            self._audit_whole_leaf(leaf, positions)

    def _audit_branch_inner(self, branch, pos, depth, moddepth, outputs, allblocks, expected):
        if moddepth == 0:
            pos = from_bytes(branch[pos + 8:pos + 10])
            output = branch[pos:pos + 8]
            if pos == 0xFF:
                self._audit_branch(output, depth, allblocks, expected)
            else:
                outputs.get(output, []).append((pos, expected))
        t0 = get_type(branch, pos)
        t1 = get_type(branch, pos + 32)
        if t0 != INVALID and t1 != INVALID:
            assert expected is None or hasher(branch[pos:pos + 64]) == expected
        else:
            assert expected is None
        if t0 == EMPTY:
            assert t1 != EMPTY and t1 != TERMINAL
            assert branch[pos:pos + 32] == BLANK
            self._audit_branch_inner_empty(branch, pos + 64, moddepth - 1)
        elif t0 == TERMINAL:
            assert t1 != EMPTY
            self._audit_branch_inner_empty(branch, pos + 64, moddepth - 1)
        else:
            e = (branch[pos:pos + 32] if t0 == MIDDLE else None)
            self._audit_branch_inner(branch, pos + 64, depth + 1, moddepth - 1, outputs, allblocks, e)
        if t1 == EMPTY:
            assert branch[pos + 32:pos + 64] == BLANK
            self._audit_branch_inner_empty(branch, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
        elif t1 == TERMINAL:
            self._audit_branch_inner_empty(branch, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
        else:
            e = (branch[pos + 32:pos + 64] if t1 == MIDDLE else None)
            assert self._audit_branch_inner(branch, pos + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1, outputs, allblocks, e)

    def _audit_branch_inner_empty(self, branch, pos, moddepth):
        if moddepth == 0:
            assert branch[pos:pos + 10] == bytes(10)
            return
        assert branch[pos:pos + 64] == bytes(64)
        self._audit_branch_inner_empty(branch, pos + 64, moddepth - 1)
        self._audit_branch_inner_empty(branch, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)

    def _audit_whole_leaf(self, leaf, inputs):
        leaf = self._ref(leaf)
        assert len(inputs) == from_bytes(leaf[2:4])
        mycopy = self.allocate_leaf()
        for pos, expected in inputs:
            self._audit_whole_leaf_inner(leaf, mycopy, pos, expected)
        i = from_bytes(leaf[:2])
        while i != 0xFF:
            nexti = from_bytes(leaf[4 + i * 68:4 + i * 68 + 2])
            assert mycopy[4 + i * 68:4 + i * 68 + 68] == bytes(68)
            mycopy[4 + i * 68:4 + i * 68 + 2] = to_bytes(i, 2)
            i = nexti
        assert mycopy[4:] == leaf[4:]
        self._deallocate(mycopy)

    def _audit_whole_leaf_inner(self, leaf, mycopy, pos, expected):
        rpos = 4 + pos * 68
        assert mycopy[rpos:rpos + 68] == bytes(68)
        mycopy[rpos:rpos + 68] = leaf[rpos:rpos + 68]
        t0 = get_type(leaf, rpos)
        t1 = get_type(leaf, rpos + 32)
        if t0 != INVALID and t1 != INVALID:
            assert hasher(leaf[rpos:rpos + 64]) == expected
        else:
            assert expected == None
        if t0 == EMPTY:
            assert t1 != EMPTY
            assert t1 != MIDDLE
            assert leaf[rpos:rpos + 32] == BLANK
            assert leaf[rpos + 64:rpos + 66] == bytes(2)
        elif t0 == TERMINAL:
            assert t1 != EMPTY
            assert leaf[rpos + 64:rpos + 66] == bytes(2)
        else:
            e = (leaf[rpos:rpos + 32] if t0 == MIDDLE else None)
            self._audit_whole_leaf_inner(leaf, mycopy, from_bytes(leaf[rpos + 64:rpos + 66]), e)
        if t1 == EMPTY:
            assert leaf[rpos + 32:rpos + 64] == BLANK
            assert leaf[rpos + 66:rpos + 68] == bytes(2)
        elif t1 == TERMINAL:
            assert leaf[rpos + 66:rpos + 68] == bytes(2)
        else:
            e = (leaf[rpos + 32:rpos + 64] if t1 == MIDDLE else None)
            self._audit_whole_leaf_inner(leaf, mycopy, from_bytes(leaf[rpos + 66:rpos + 68]), e)

    def _allocate_branch(self):
        b = bytearray(8 + self.subblock_lengths[-1])
        self.pointers_to_arrays[self._deref(b)] = b
        return b

    def _allocate_leaf(self):
        leaf = bytearray(4 + self.leaf_units * 68)
        for i in range(self.leaf_units):
            p = 4 + i * 68
            leaf[p:p + 2] = to_bytes((i + 1) if i != self.leaf_units - 1 else 0xFFFF, 2)
        self.pointers_to_arrays[self._deref(leaf)] = leaf
        return leaf

    def _deallocate(self, thing):
        del self.pointers_to_arrays[self._deref(branch)]

    def _ref(self, ref):
        assert len(ref) == 8
        if ref == bytes(8):
            return None
        return self.pointers_to_arrays[ref]

    def _deref(self, thing):
        if thing is None:
            return bytes(8)
        return to_bytes(id(thing), 8)

    def get_root(self):
        if get_type(self.root, 0) == INVALID:
            self.root = self._force_calculation_branch(self.rootblock, 8, len(self.subblock_lengths) - 1)
        return bytes(self.root)

    def _force_calculation_branch(self, block, pos, moddepth):
        if moddepth == 0:
            block = self._deref(block[pos:pos + 8])
            pos = from_bytes(posref[4:6])
            if pos == 0xFFFF:
                return self._force_calculation_branch(block, 8, len(self.subblock_lengths) - 1)
            else:
                return self._force_calculation_leaf(block, pos)
        if get_type(block, pos) == INVALID:
            block[pos:pos + 32] = self._force_calculation_branch(block, pos + 64, moddepth - 1)
        if get_type(block, pos + 32) == INVALID:
            block[pos + 32:pos + 64] = self._force_calculation_branch(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
        return hasher(block[pos:pos + 64])

    def _force_calculation_leaf(self, block, pos):
        pos = 4 + pos * 68
        if get_type(block, pos) == INVALID:
            block[pos:pos + 32] = self._force_calculation_leaf(block, from_bytes(block[pos + 64:pos + 66]))
        if get_type(block, pos + 32) == INVALID:
            block[pos + 32:pos + 64] = self._force_calculation_leaf(block, from_bytes(block[pos + 66:pos + 68]))
        return hasher(block[pos:pos + 64])

    def add(self, toadd):
        return self.add_already_hashed(sha256(toadd).digest())

    def add_already_hashed(self, toadd):
        self._add(flip_terminal(toadd))

    def _add(self, toadd):
        t = get_type(self.root, 0)
        if t == EMPTY:
            self.root = toadd
        elif t == TERMINAL:
            if toadd == self.root:
                return
            self.rootblock = self._allocate_branch()
            self._insert_branch([self.root, toadd], self.rootblock, 8, 0, len(self.subblock_lengths) - 1)
            self.root = JUNK
        else:
            if self._add_to_branch(toadd, self.rootblock, 0) == INVALIDATING:
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
                self._insert_branch([toadd, v1], block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
                make_invalid(block, pos + 32)
            if t0 != INVALID:
                return INVALIDATING
            else:
                return DONE

    def _insert_branch(self, things, block, pos, depth, moddepth):
        if moddepth == 0:
            child = self._ref(block[:8])
            if child is None:
                child = self._allocate_leaf()
                block[:8] = self._deref(child)
            r, leafpos = self._insert_leaf(things, child, depth)
            if r == FULL:
                child = self._allocate_leaf()
                block[:8] = self._deref(child)
                r, leafpos = self._insert_leaf(things, child, depth)
                assert r == INVALIDATING
            child[2:4] = to_bytes(from_bytes(child[2:4]) + 1, 2)
            block[pos:pos + 8] = self._deref(child)
            block[pos + 8:pos + 10] = to_bytes(leafpos, 2)
            return
        things.sort()
        if len(things) == 2:
            block[pos:pos + 32] = things[0]
            block[pos + 32:pos + 64] = things[1]
            return
        bits = [get_type(thing, 0) for thing in things]
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
                self._insert_branch(things[1:], block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
                make_invalid(block, pos + 32)

    # state can be INVALIDATING, DONE
    def _add_to_leaf(self, toadd, branch, branchpos, leaf, leafpos, depth):
        r = self._add_to_leaf_inner(toadd, leaf, pos, depth)
        if r != FULL:
            return r
        was_invalid = get_type(leaf[leafpos]) == INVALID or get_type(leaf[leafpos + 32]) == INVALID
        if from_bytes(leaf[2:4]) == 1:
            newb = self._allocate_branch()
            self._copy_leaf_to_branch(newb, 8, len(self.subblock_lengths) - 1, leaf, leafpos)
            self._add_to_branch(toadd, newb, depth)
            branch[branchpos:branchpos + 8] = self._deref(newb)
            branch[branchpos + 8:branchpos + 10] = to_bytes(0xFFFF, 2)
            self._deallocate(leaf)
            if was_invalid:
                return DONE
            return INVALIDATING
        active = self._ref(branch[:8])
        if active is not None and active is not leaf:
            r, newpos = self._copy_between_leafs(leaf, active, leafpos)
            if r == DONE:
                self._delete_from_leaf(leaf, leafpos)
                branch[branchpos:branchpos + 8] = self._deref(active)
                branch[branchpos + 8:branchpos + 10] = to_bytes(newpos, 2)
                r = self._add_to_leaf_inner(toadd, active, newpos, depth)
                assert r == INVALIDATING
                if was_invalid:
                    return DONE
                return INVALIDATING
        active = self._allocate_branch()
        r, newpos = self._copy_between_leafs(leaf, active, leafpos)
        assert r == DONE
        self._delete_from_leaf(leaf, leafpos)
        branch[branchpos:branchpos + 8] = self._deref(active)
        branch[branchpos + 8:branchpos + 10] = to_bytes(newpos, 2)
        r = self._add_to_leaf_inner(toadd, active, newpos, depth)
        assert r == INVALIDATING
        if was_invalid:
            return DONE
        return INVALIDATING

    # returns INVALIDATING, DONE, FULL
    def _add_to_leaf_inner(self, toadd, leaf, pos, depth):
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
                    oldval1 = leaf[rpos + 32:pos + 64]
                    if toadd == oldval1:
                        return DONE
                    nextpos = from_bytes(leaf[:2])
                    leaf[:2] = to_bytes(pos, 2)
                    leaf[rpos:rpos + 64] = bytes(64)
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
                leaf[rpos + 64:rpos + 66] = to_bytes(newpos, 2)
                make_invalid(leaf, rpos)
                if get_type(leaf, rpos + 32) == INVALID:
                    return DONE
                return INVALIDATING
            else:
                r = self._add_to_leaf_inner(toadd, leaf, from_bytes(leaf[rpos + 64:rpos + 66]), depth + 1)
                if r == INVALIDATING:
                    if t == MIDDLE:
                        make_invalid(leaf, rpos)
                        return INVALIDATING
                    return DONE
                return r
        else:
            t = get_type(leaf, rpos)
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
                leaf[rpos + 66:rpos + 68] = to_bytes(newpos, 2)
                make_invalid(leaf, rpos + 32)
                if get_type(leaf, rpos) == INVALID:
                    return DONE
                return INVALIDATING
            else:
                r = self._add_to_leaf_inner(toadd, leaf, from_bytes(leaf[rpos + 66:rpos + 68]), depth + 1)
                if r == INVALIDATING:
                    if t == MIDDLE:
                        make_invalid(leaf, rpos + 32)
                        return INVALIDATING
                    return DONE
                return r

    # returns state, newpos
    # state can be FULL, DONE
    def _copy_between_leafs(self, fromleaf, toleaf, frompos):
        topos = from_bytes(toleaf[:2])
        if topos == 0xFFFF:
            return FULL, None
        rfrompos = 4 + frompos * 68
        rtopos = 4 + topos * 68
        toleaf[0:2] = toleaf[rtopos:rtopos + 2]
        t0 = get_type(fromleaf, rfrompos)
        lowpos = None
        if t0 == MIDDLE or t0 == INVALID:
            r, lowpos = self._copy_between_leafs(fromleaf, toleaf, from_bytes(fromleaf[rfrompos + 64:rfrompos + 66]))
            if r == FULL:
                assert toleaf[:2] == toleaf[rtopos:rtopos + 2]
                toleaf[:2] = to_bytes(topos, 2)
                return FULL, None
        t1 = get_type(fromleaf, rfrompos + 32)
        if t1 == MIDDLE or t1 == INVALID:
            r, highpos = self._copy_between_leafs(fromleaf, toleaf, from_bytes(fromleaf[rfrompos + 66:rfrompos + 68]))
            if r == FULL:
                if t0 == MIDDLE or t0 == INVALID:
                    self._delete_from_leaf(toleaf, lowpos)
                assert toleaf[:2] == toleaf[rtopos:rtopos + 2]
                toleaf[:2] = to_bytes(topos, 2)
                return FULL, None
        toleaf[rtopos:rtopos + 64] = fromleaf[rfrompos:rfrompos + 64]
        toleaf[rtopos + 64:rtopos + 66] = to_bytes(lowpos, 2)
        toleaf[rtopos + 66:rtopos + 68] = to_bytes(highpos, 2)
        return DONE, topos

    def _delete_from_leaf(self, leaf, pos):
        t = get_type(leaf, pos)
        if t == MIDDLE or t == INVALID:
            self._delete_from_leaf(leaf, from_bytes(leaf[pos + 64:pos + 66]))
        t = get_type(leaf, pos + 32)
        if t == MIDDLE or t == INVALID:
            self._delete_from_leaf(leaf, from_bytes(leaf[pos + 66:pos + 68]))
        leaf[pos + 2:pos + 68] = bytes(68)
        leaf[pos:pos + 2] = leaf[:2]
        leaf[:2] = to_bytes(pos, 2)

    def _copy_leaf_to_branch(self, branch, branchpos, moddepth, leaf, leafpos):
        rleafpos = 4 + leafpos * 68
        if moddepth == 0:
            active = self._ref(branch[:8])
            if active is None:
                active = self._allocate_branch()
                branch[0:8] = self._deref(active)
            r, newpos = self._copy_between_leafs(leaf, active, leafpos)
            if r == FULL:
                active = self._allocate_branch()
                branch[0:8] = self._deref(active)
                r, newpos = self._copy_between_leafs(leaf, active, leafpos)
                assert r == DONE
            branch[branchpos:branchpos + 8] = self._ref(active)
            branch[branchpos + 8:branchpos + 10] = to_bytes(newpos, 2)
            return
        branch[branchpos:branchpos + 64] = leaf[rleafpos:rleafpos + 64]
        t = get_type(leaf, rleafpos)
        if t == MIDDLE or t == INVALID:
            self._copy_leaf_to_branch(branch, branchpos + 64, moddepth - 1, leaf, from_bytes(leaf[rleafpos + 64:rleafpos + 66]))
        t = get_type(leaf, rleafpos + 32)
        if t == MIDDLE or t == INVALID:
            self._copy_leaf_to_branch(branch, branchpos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1, leaf, from_bytes(leaf[rleafpos + 66:rleafpos + 68]))

    # returns (status, pos)
    # status can be INVALIDATING, FULL
    def _insert_leaf(self, things, leaf, depth):
        pos = from_bytes(leaf[:2])
        if pos == 0xFFFF:
            return FULL, None
        lpos = pos * 68 + 4
        leaf[:2] = leaf[lpos:lpos + 2]
        things.sort()
        if len(things) == 2:
            leaf[lpos:lpos + 32] = things[0]
            leaf[lpos + 32:lpos + 64] = things[1]
            return INVALIDATING
        bits = [get_type(thing, 0) for thing in things]
        if bits[0] == bits[1] == bits[2]:
            r, laterpos = self._insert_leaf(things, leaf, depth + 1)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            if bits[0] == 0:
                leaf[lpos + 64:lpos + 66] = to_bytes(laterpos, 2)
                make_invalid(leaf, lpos)
            else:
                leaf[lpos + 66:lpos + 68] = to_bytes(laterpos, 2)
                make_invalid(leaf, lpos + 32)
                leaf[lpos:lpos + 2] = bytes(2)
            return INVALIDATING, pos
        elif bits[0] == bits[1]:
            r, laterpos = self._insert_leaf([things[0], things[1]], leaf)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            leaf[lpos + 32:lpos + 64] = things[2]
            leaf[lpos + 64:lpos + 66] = to_bytes(laterpos, 2)
            make_invalid(leaf, lpos)
        else:
            r, laterpos = self._insert_leaf([things[1], things[2]], leaf)
            if r == FULL:
                leaf[:2] = to_bytes(pos, 2)
                return FULL, None
            leaf[lpos:lpos + 32] = things[0]
            leaf[lpos + 66:lpos + 68] = to_bytes(laterpos, 2)
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
                self.root = BLANK
            return
        else:
            status, oneval = self._remove_branch(toremove, self.rootblock, 0)
        if status == INVALIDATING:
            make_invalid(self.root, 0)
        elif status == ONELEFT:
            self.root = oneval
        elif status == FRAGILE:
            self._catch_branch(self.rootblock, 8, len(self.subblock_lengths) - 1)

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
                r, val = self._remove_leaf(toremove, self._ref(block[pos:pos + 8]), p, depth)
            if r == ONELEFT:
                block[pos:pos + 10] = bytes(10)
            return r, val
        if get_bit(block, pos) == 0:
            r, val = self._remove_branch_inner(toremove, block, pos + 64, depth + 1, moddepth - 1)
            if r == NOTSTARTED:
                t = get_type(block, pos)
                if t == EMPTY:
                    if get_type(block, pos + 32) == EMPTY:
                        return NOTSTARTED, None
                    return DONE, None
                assert t == TERMINAL
                if block[pos:pos + 32] == toremove:
                    if get_type(block, pos + 32) == TERMINAL:
                        left = block[pos + 32:pos + 64]
                        block[pos:pos + 64] = bytes(64)
                        return ONELEFT, left
                    else:
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
                if t1 == EMPTY:
                    return FRAGILE, None
                self._catch_branch(block, pos + 64, moddepth - 1)
                if t1 == INVALID:
                    return DONE, None
                assert t1 == MIDDLE
                make_invalid(block, pos)
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
                was_invalid = get_type(block + 32) == INVALID
                block[pos + 32:pos + 64] = val
                if get_type(block, pos) == TERMINAL:
                    return FRAGILE, None
                if not was_invalid:
                    return INVALIDATING, None
                return DONE, None
            elif r == FRAGILE:
                t0 = get_type(block)
                if t0 == EMPTY:
                    return FRAGILE, None
                self._catch_branch(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
                if t0 == INVALID:
                    return DONE, None
                assert t0 == MIDDLE
                make_invalid(block, pos + 32)
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
    def _remove_leaf(self, toremove, block, pos, depth):
        result, val = self._remove_leaf_inner(toremove, block, pos, depth)
        if result == ONELEFT:
            numin = from_bytes(block[2:4])
            if numin == 1:
                self._deallocate(block)
            else:
                block[2:4] = to_bytes(numin - 1, 2)
        return result, val

    def _deallocate_leaf_node(self, leaf, pos):
        rpos = 4 + pos * 68
        next = leaf[:2]
        leaf[rpos:rpos + 2] = leaf[:2]
        leaf[rpos + 2:rpos + 68] = bytes(68)
        leaf[:2] = to_bytes(pos, 2)

    # returns (status, oneval)
    # status can be ONELEFT, FRAGILE, INVALIDATING, DONE
    def _remove_leaf_inner(self, toremove, block, pos, depth):
        rpos = 4 + pos * 68
        if get_bit(toremove, depth) == 0:
            t = get_type(block[rpos])
            if t == EMPTY:
                return DONE
            if t == TERMINAL:
                t1 = get_type(block, rpos + 32)
                if block[rpos:rpos + 32] == toremove:
                    if t1 == TERMINAL:
                        left = block[rpos + 32:rpos + 64]
                        self._deallocate_leaf_node(block, pos)
                        return ONELEFT, left
                    block[rpos:rpos + 32] = bytes(32)
                    if t1 == MIDDLE:
                        return INVALIDATING, None
                    else:
                        assert t1 == INVALID
                        return DONE, None
                if block[rpos + 32:rpos + 64] == toremove:
                    left = block[rpos:rpos + 32]
                    self._deallocate_leaf_node(block, pos)
                    return ONELEFT, left
                return DONE, None
            else:
                r, val = self._remove_leaf_inner(toremove, block, from_bytes(block[rpos + 64:rpos + 66]), depth + 1)
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
                    if t1 == TERMINAL:
                        return FRAGILE, None
                    if t1 == MIDDLE and t != INVALID:
                        return INVALIDATING, None
                    return DONE, None
                assert r == FRAGILE
                t1 = get_type(block, rpos + 32)
                if t1 == EMPTY:
                    return FRAGILE, None
                self._catch_leaf(block, from_bytes(block[rpos + 64:rpos + 66]))
        else:
            t = get_type(block[rpos + 32])
            if t == EMPTY:
                return DONE
            elif t == TERMINAL:
                t0 = get_type(block, rpos)
                if block[rpos + 32:rpos + 64] == toremove:
                    if t0 == TERMINAL:
                        left = block[rpos + 32:rpos + 64]
                        self._deallocate_leaf_node(block, pos)
                        return ONELEFT, left
                    block[rpos + 32:rpos + 64] = bytes(32)
                    if t1 == MIDDLE:
                        return INVALIDATING, None
                    else:
                        assert t0 == INVALID
                        return DONE, None
                if block[rpos:rpos + 32] == toremove:
                    left = block[rpos + 32:rpos + 64]
                    self._deallocate_leaf_node(node, pos)
                    return ONELEFT, left
                return DONE, None
            else:
                r, val = self._remove_leaf_inner(toremove, block, from_bytes(block[rpos + 66:rpos + 68]), depth + 1)
                if r == DONE:
                    return DONE, None
                if r == INVALIDATING:
                    if t == MIDDLE:
                        make_invalid(block, rpos + 32)
                        if get_type(block, rpos + 32) != INVALID:
                            return INVALIDATING, None
                    return DONE, None
                if r == ONELEFT:
                    t0 = get_type(block, rpos)
                    assert t0 != EMPTY
                    block[rpos + 32:rpos + 64] = val
                    if t0 == TERMINAL:
                        return FRAGILE, None
                    if t0 == MIDDLE and t != INVALID:
                        return INVALIDATING, None
                    return DONE, None
                assert r == FRAGILE
                t0 = get_type(block, rpos)
                if t0 == EMPTY:
                    return FRAGILE, None
                self._catch_leaf(block, from_bytes(block[rpos + 66:rpos + 68]))

    def _catch_branch(self, block, pos, moddepth):
        if moddepth == 0:
            leafpos = from_bytes(block[pos + 8:pos + 10])
            if leafpos == 0xFFFF:
                self._catch_branch(self._ref(block[pos:pos + 8]), 8, len(self.subblock_lengths) - 1)
            else:
                self._catch_leaf(self._ref(block[pos:pos + 8], leafpos))
            return
        if get_type(block, pos) == EMPTY:
            r = self._collapse_branch(block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            if r != None:
                block[pos:pos + 64] = r
            return
        if get_type(block, pos + 32) == EMPTY:
            r = self._collapse_branch(block, pos + 64, moddepth - 1)
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
                r = self._collapse_leaf(self._ref(block[pos:pos + 8]))
            if r != None:
                block[pos:pos + 10] = bytes(10)
            return r
        t0 = get_type(block[pos])
        t1 = get_type(block[pos + 32])
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
        rpos = 4 + pos * 68
        t0 = get_type(leaf, rpos)
        t1 = get_type(leaf, rpos + 32)
        if t0 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[rpos + 66:rpos + 68]))
            if r != None:
                leaf[rpos + 66:rpos + 68] = bytes(2)
                leaf[rpos:rpos + 64] = r
            return
        if t1 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[rpos + 64:rpos + 66]))
            if r != None:
                leaf[rpos + 64:rpos + 66] = bytes(2)
                leaf[rpos:rpos + 64] = r
            return

    # returns two hashes string or None
    def _collapse_leaf(self, leaf, pos):
        r = self._collapse_leaf_inner(leaf, pos)
        if r != None:
            inputs = from_bytes(leaf[2:4])
            if inputs == 1:
                self._deallocate(leaf)
                return r
            leaf[2:4] = to_bytes(inputs - 1, 2)
        return r

    # returns two hashes string or None
    def _collapse_leaf_inner(self, leaf, pos):
        rpos = 4 + pos * 68
        t0 = get_type(leaf, rpos)
        t1 = get_type(leaf, rpos + 32)
        r = None
        if t0 == TERMINAL and t1 == TERMINAL:
            r = leaf[rpos:rpos + 64]
        elif t0 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[pos + 66:pos + 68]))
        elif t1 == EMPTY:
            r = self._collapse_leaf_inner(leaf, from_bytes(leaf[pos + 64:pos + 66]))
        if r is not None:
            leaf[rpos + 2:rpos + 68] = bytes(66)
            leaf[rpos:rpos + 2] = leaf[:2]
            leaf[:2] = to_bytes(pos, 2)
        return r

    def batch_add_and_remove(self, toadd, toremove):
        self.batch_add_and_remove_already_hashed([sha256(x).digest() for x in toadd], [sha256(x).digest() for x in toremove])

    def batch_add_and_remove_already_hashed(self, toadd, toremove):
        self._batch_add_and_remove([flip_terminal(x) for x in toadd], [flip_terminal(x) for x in toremove])

    def _batch_add_and_remove(self, toadd, toremove):
        toadd.sort()
        toremove.sort()
        addpos = 0
        removepos = 0
        while addpos < len(toadd) and removepos < len(toremove):
            if toadd[addpos] == toremove[removepos]:
                last = toadd[addpos]
                while addpos < len(toadd) and toadd[addpos] == last:
                    addpos += 1
                while removepos < len(toremove) and toremove[removepos] == last:
                    removepos += 1
            elif toadd[addpos] < toremove[removepos]:
                self._add(toadd[addpos])
                addpos += 1
            else:
                self._remove(toremove)
                removepos += 1
        while removepos < len(toremove):
            self._remove(toremove)
            removepos += 1
        while addpos < len(toadd):
            self._add(toadd[addpos])
            addpos += 1

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
            return False, b''
        if t == TERMINAL:
            return tocheck == self.root, b''
        assert t == MIDDLE
        r = self._is_included_branch(tocheck, self.rootblock, 8, 0, len(self.subblock_lengths) - 1, buf)
        return r, b''.join(buf)

    # returns boolean, appends to buf
    def _is_included_branch(self, tocheck, block, pos, depth, moddepth, buf):
        if moddepth == 0:
            if block[pos + 8:pos + 10] == bytes([0xFF, 0xFF]):
                return self._is_included_branch(tocheck, self._ref(block[pos:pos + 8]), 8, depth + 1, len(self.subblock_lengths) - 1, buf)
            else:
                return self._is_included_leaf(tocheck, self._ref(block[pos:pos + 8]), from_bytes(block[pos + 8:pos + 10]), buf)
        if block[pos:pos + 32] == tocheck:
            buf.append(bytes([GIVE1]))
            buf.append(block[pos + 32:pos + 64])
            return True
        if block[pos + 32:pos + 64] == tocheck:
            buf.append(bytes([GIVE0]))
            buf.append(block[pos:pos + 32])
            return True
        if get_bit(tocheck, depth) == 0:
            t = get_type(block, pos)
            if t == EMPTY:
                buf.append(bytes([EMPTY0]))
                buf.append(block[pos + 32:pos + 64])
                return False
            if t == TERMINAL:
                buf.append(bytes([GIVEBOTH]))
                buf.append(block[pos:pos + 64])
                return False
            assert t == MIDDLE
            buf.append(bytes([GIVE1]))
            buf.append(block[pos + 32:pos + 64])
            return self._is_included_branch(tocheck, block, pos + 64, depth + 1, moddepth - 1, buf)
        else:
            t = get_type(block, pos + 32)
            if t == EMPTY:
                buf.append(bytes([EMPTY1]))
                buf.append(block[pos:pos + 32])
                return False
            if t == TERMINAL:
                buf.append(bytes([GIVEBOTH]))
                buf.append(block[pos:pos + 64])
                return False
            assert t == MIDDLE
            buf.append(bytes([GIVE0]))
            buf.append(block[pos:pos + 32])
            return self._is_included_branch(tocheck, block, pos + 64 + self.subblock_lengths[moddepth], depth + 1, moddepth - 1, buf)

    # returns boolean, appends to buf
    def _is_included_leaf(self, tocheck, block, pos, depth, buf):
        pos = 4 + pos * 68
        if block[pos:pos + 32] == tocheck:
            buf.append(bytes([GIVE1]))
            buf.append(block[pos + 32:pos + 64])
            return True
        if block[pos + 32:pos + 64] == tocheck:
            buf.append(bytes([GIVE0]))
            buf.append(block[pos:pos + 32])
            return True
        if get_bit(tocheck, depth) == 0:
            t = get_type(block, pos)
            if t == EMPTY:
                buf.append(bytes([EMPTY0]))
                buf.append(block[pos + 32:pos + 64])
                return False
            if t == TERMINAL:
                buf.append(bytes([GIVEBOTH]))
                buf.append(block[pos:pos + 64])
                return False
            assert t == MIDDLE
            buf.append(bytes([GIVE1]))
            buf.append(block[pos + 32:pos + 64])
            return self._is_included_leaf(tocheck, block, from_bytes(block[pos + 64:pos + 66]), depth + 1, buf)
        else:
            t = get_type(block, pos + 32)
            if t == EMPTY:
                buf.append(bytes([EMPTY1]))
                buf.append(block[pos:pos + 32])
                return False
            if t == TERMINAL:
                buf.append(bytes([GIVEBOTH]))
                buf.append(block[pos:pos + 64])
                return False
            assert t == MIDDLE
            buf.append(bytes([GIVE0]))
            buf.append(block[pos:pos + 32])
            return self._is_included_leaf(tocheck, block, from_bytes(block[pos + 66:pos + 68]), depth + 1, buf)

class ReferenceMerkleSet:
    def __init__(self):
        self.root = EmptyNode(0)

    def get_root(self):
        return self.root.hash

    def add_already_hashed(self, toadd):
        toadd = flip_terminal(toadd)
        self.root = self.root.add(toadd)

    def remove_already_hashed(self, toremove):
        toremove = flip_terminal(toremove)
        self.root = self.root.remove(toremove)

    def is_included_already_hashed(self, tocheck):
        tocheck = flip_terminal(tocheck)
        if self.root.size == 0:
            return False, b''
        if self.root.size == 1:
            return tocheck == self.root.hash, b''
        return self.root.is_included(tocheck)

    def audit(self):
        assert self.root.depth == 0
        self.root.audit()

class EmptyNode:
    def __init__(self, depth):
        self.hash = BLANK
        self.size = 0
        self.depth = depth

    def add(self, toadd):
        return TerminalNode(toadd, self.depth)

    def remove(self, toremove):
        return self

    def audit(self):
        pass

class TerminalNode:
    def __init__(self, hash, depth):
        assert len(hash) == 32
        self.hash = hash
        self.depth = depth
        self.size = 1

    def add(self, toadd):
        if toadd == self.hash:
            return self
        return self._make_middle(self.hash, toadd, self.depth)

    def _make_middle(self, thinga, thingb, depth):
        ta = get_bit(thinga, depth)
        tb = get_bit(thingb, depth)
        if ta == tb:
            if ta == 0:
                return MiddleNode(self._make_middle(thinga, thingb, depth + 1), EmptyNode(depth + 1), depth)
            return MiddleNode(EmptyNode(depth + 1), self._make_middle(thinga, thingb, depth + 1), depth)
        else:
            if ta == 0:
                return MiddleNode(TerminalNode(thinga, depth + 1), TerminalNode(thingb, depth + 1), depth)
            return MiddleNode(TerminalNode(thingb, depth + 1), TerminalNode(thinga, depth + 1), depth)

    def remove(self, toremove):
        if toremove == self.hash:
            return EmptyNode(self.depth)
        return self

    def audit(self):
        pass

class MiddleNode:
    def __init__(self, low, high, depth):
        assert low.depth == depth + 1
        assert high.depth == depth + 1
        self.depth = depth
        self.low = low
        self.high = high
        self.size = low.size + high.size
        if low.size == 0 and high.size == 2:
            self.hash = high.hash
        elif high.size == 0 and low.size == 2:
            self.hash = low.hash
        else:
            self.hash = hasher(low.hash + high.hash)

    def add(self, toadd):
        if get_bit(toadd, self.depth) == 0:
            r = self.low.add(toadd)
            if r == self.low:
                return self
            return MiddleNode(r, self.high, self.depth)
        else:
            r = self.high.add(toadd)
            if r == self.high:
                return self
            return MiddleNode(self.low, r, self.depth)

    def remove(self, toremove):
        if get_bit(toremove, self.depth) == 0:
            r = self.low.remove(toremove)
            if r == self.low:
                return self
            a, b = r, self.high
        else:
            r = self.high.remove(toremove)
            if r == self.high:
                return self
            a, b = self.low, r
        if a.size == 0 and b.size == 1:
            return TerminalNode(b.hash, self.depth)
        if b.size == 0 and a.size == 1:
            return TerminalNode(a.hash, self.depth)
        return MiddleNode(a, b, self.depth)

    def is_included(self, tocheck):
        if self.size == 2:
            if self.low.size == 0:
                return self.high.is_included(tocheck)
            if self.high.size == 0:
                return self.low.is_included(tocheck)
            if tocheck == self.low.hash:
                return True, bytes([GIVE1]) + self.high.hash
            if tocheck == self.high.hash:
                return True, bytes([GIVE0]) + self.low.hash
            return False, bytes([GIVEBOTH]) + self.low.hash + self.high.hash
        b = get_bit(tocheck, self.depth)
        if b == 0:
            if self.low.size == 0:
                return False, bytes([EMPTY0]) + self.high.hash
            if self.low.size == 1:
                if tocheck == self.low.hash:
                    return True, bytes([GIVE1]) + self.high.hash
                return False, bytes([GIVEBOTH]) + self.low.hash + self.high.hash
            r, p = self.low.is_included(tocheck)
            if self.high.size == 0:
                return r, bytes([EMPTY1]) + p
            return r, bytes([GIVE1]) + self.high.hash + p
        else:
            if self.high.size == 0:
                return False, bytes([EMPTY1]) + self.low.hash
            if self.high.size == 1:
                if tocheck == self.high.hash:
                    return True, bytes([GIVE0]) + self.low.hash
                return False, bytes([GIVEBOTH]) + self.low.hash + self.high.hash
            r, p = self.high.is_included(tocheck)
            if self.low.size == 0:
                return r, bytes([EMPTY0]) + p
            return r, bytes([GIVE0]) + self.low.hash + p

    def audit(self):
        assert self.low.depth == self.depth + 1
        assert self.high.depth == self.depth + 1
        assert self.size == self.low.size + self.high.size
        assert self.size >= 2
        self.low.audit()
        self.high.audit()            

def _testmset(numhashes, mset, oldroots = None, oldproofss = None):
    hashes = [blake2s(to_bytes(i, 10)).digest() for i in range(numhashes)]
    roots = []
    proofss = []
    assert mset.get_root() == BLANK
    mset.audit()
    for i in range(numhashes):
        roots.append(mset.get_root())
        if oldroots is not None:
            assert oldroots[i] == roots[i]
        proofs = []
        for j in range(numhashes):
            r, proof = mset.is_included_already_hashed(hashes[j])
            if oldproofss is not None:
                assert oldproofss[i][j] == proof
            proofs.append(proof)
            assert r == (j < i)
            assert confirm_included_already_hashed(roots[-1], hashes[j], proof) == r
            assert confirm_not_included_already_hashed(roots[-1], hashes[j], proof) == (not r)
        if i > 0:
            mset.add_already_hashed(hashes[i-1])
            mset.audit()
            assert mset.get_root() == roots[i]
            for j in range(numhashes):
                r, proof = mset.is_included_already_hashed(hashes[j])
                assert proof == proofs[j]
                assert r == (j < i)
        mset.add_already_hashed(hashes[i])
        mset.audit()
        proofss.append(proofs)
    for i in range(numhashes - 1, -1, -1):
        for k in range(2):
            mset.remove_already_hashed(hashes[i])
            assert roots[i] == mset.get_root()
            mset.audit()
            for j in range(numhashes):
                r, proof = mset.is_included_already_hashed(hashes[j])
                assert r == (j < i)
                assert proof == proofss[i][j]
    return roots, proofss

def testboth(num):
    roots, proofss = _testmset(num, ReferenceMerkleSet())
    _testmset(num, MerkleSet(6, 64), roots, proofss)

testboth(100)
