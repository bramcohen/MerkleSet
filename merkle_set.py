from hashlib import sha256
from blake2 import blake2
from binascii import b2a_hex

def hasher(mystr):
    # It also may be faster to change the metadata bits so only 32 bytes need 
    # to be hashed if one of the children is missing
    assert len(mystr) == 64
    return b2a_hex(blake2(mystr, hashSize = 32))

def shahash(mystr):
    return sha256(mystr).digest()

from_bytes = int.from_bytes
to_bytes = int.to_bytes

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
TODO: Address Blake2 subtleties
TODO: Make sure that data structures don't get garbled on an out of memory error
TODO: add multi-threading support
TODO: add support for continuous self-auditing
TODO: Try heuristically calculating hashes non-lazily when they're likely to be needed later
TODO: Try unrolling all this recursivity to improve performance

# all unused should be zeroed out
branch: active_child 8 patricia[size]
patricia[n]: modified_hash 32 modified_hash 32 patricia[n-1] patricia[n-1]
# unused are zeroed out
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
empty0: EMPTY0 1
empty1: EMPTY1 1
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
INVALIDATING = 4
DONE = 5
FULL = 6

def confirm_included(root, val, proof):
    return confirm_included_already_hashed(root, shahash(val), proof)

def confirm_included_already_hashed(root, val, proof):
    assert len(root) == 31
    assert len(val) == 32
    val = val[:-1]
    if root == EMPTY:
        return False
    if proof == SINGULAR:
        return hasher(SINGULAR + val[:31] + bytes(31)) == root
    possible, newroot = self._confirm_included(0, proof, 0, val)
    return possible and newroot == root

def _get_bit(mybytes, pos):
    return (mybytes[pos // 8] >> (7 - (pos % 8))) & 1

def _to_bits(mybytes):
    r = []
    for c in mybytes:
        for i in range(8):
            if c & (0x80 >> i):
                r.append(1)
            else:
                r.append(0)
    return r

def _confirm_included(depth, proof, pos, val):
    if depth > 220:
        return False, None
    if len(proof) <= pos:
        return False, None
    t = proof[pos:pos + 1]
    if t == ONLY0:
        if _get_bit(val, depth) != 0:
            return False, None
        p, v = self._confirm_included(depth + 1, proof, pos + 1, val)
        if not p:
            return False, None
        return True, hasher(ONLY0 + v + bytes(31))
    elif t == ONLY1:
        if _get_bit(val, depth) != 1:
            return False, None
        p, v = self._confirm_included(depth + 1, proof, pos + 1, val)
        if not p:
            return False, None
        return True, hasher(ONLY1 + bytes(31) + v)
    elif t == TERM0:
        if len(proof) != pos + 1 + 31:
            return False, None
        if _get_bit(val, depth) == 0:
            return True, hasher(TERM0 + val + proof[pos + 1:])
        else:
            v0 = proof[pos + 1:pos + 1 + 31]
            if _to_bits(v0)[:depth + 1] != bits[:depth] + [0]:
                return False, None
            possible, v1 = _confirm_included(depth + 1, proof, pos + 1 + 31, val)
            if not possible:
                return False, None
            return True, hasher(TERM0 + v0 + v1)
    elif t == TERM1:
        if len(proof) != pos + 1 + 31:
            return False, None
        if _get_bit(val, depth) == 1:
            return True, hasher(TERM1 + proof[pos + 1:] + val)
        else:
            v1 = proof[pos + 1:pos + 1 + 31]
            if _to_bits(v1)[:depth + 1] != bits[depth] + [1]:
                return False, None
            possible, v0 = _confirm_included(depth + 1, proof, pos + 1 + 31, val)
            if not possible:
                return False, None
            return True, hasher(TERM1 + v0 + v1)
    elif t == TERMBOTH:
        if len(proof) != pos + 1 + 31:
            return False, None
        other = proof[pos + 1:pos + 1 + 31]
        if _to_bits(other)[:depth] != _to_bits(val)[:depth]:
            return False, None
        if other == val:
            return False, None
        if val < other:
            return True, hasher(TERMBOTH + val + other)
        else:
            return True, hasher(TERMBOTH + other + val)
    elif t == MIDDLE:
        if len(proof) < pos + 1 + 31:
            return False, None
        if _get_bit(val, depth) == 0:
            v1 = proof[pos + 1:pos + 1 + 31]
            possible, v0 = _confirm_included(depth + 1, proof, pos + 1 + 31, val)
        else:
            v0 = proof[pos + 1:pos + 1 + 31]
            possible, v1 = _confirm_included(depth + 1, proof, pos + 1 + 31, val)
        if not possible:
            return False, None
        return True, hasher(MIDDLE + v0 + v1)
    else:
        return False, None

def confirm_not_included(root, val, proof):
    return confirm_included_already_hashed(root, shahash(val), proof)

def confirm_not_included_already_hashed(root, val, proof):
    assert len(root) == 31
    assert len(val) == 32
    val = val[:-1]
    if root == EMPTY:
        return len(proof) == 0
    if len(proof) > 0 and proof[0:1] == SINGULAR:
        return len(proof) == 1 + 31 and proof[1:] != val and hasher(proof + bytes(31)) == root
    possible, newroot = self._confirm_not_included(0, proof, 0, val)
    return possible and newroot == root

def _confirm_not_included(depth, proof, pos, val):
    if depth > 220:
        return False, None
    if len(proof) <= pos:
        return False, None
    t = proof[pos:pos + 1]
    if t == ONLY0:
        if _get_bit(val, depth) == 0:
            p, v = self._confirm_not_included(depth + 1, proof, pos + 1, val)
            if not p:
                return False, None
            return True, hasher(ONLY0 + v + bytes(31))
        else:
            if len(proof) != pos + 1 + 31:
                return False, None
            return True, hasher(ONLY0 + proof[pos + 1:] + bytes(31))
    elif t == ONLY1:
        if _get_bit(val, depth) == 1:
            p, v = self._confirm_not_included(depth + 1, proof, pos + 1, val)
            if not p:
                return False, None
            return True, hasher(ONLY1 + bytes(31) + v)
        else:
            if len(proof) != pos + 1 + 31:
                return False, None
            return True, hasher(ONLY1 + bytes(31) + proof[pos + 1:])
    elif t == TERM0:
        if bits[depth] == 0:
            if len(proof) != pos + 1 + 31 + 31:
                return False, None
            if proof[pos + 1 + 31:] == val:
                return False, None
            if _to_bits(proof[pos + 1:pos + 1 + 31])[:depth + 1] != _to_bits(val)[:depth + 1]:
                return False, None
            return True, hasher(proof[pos:])
        else:
            if len(proof) < pos + 1 + 31:
                return False, None
            v0 = proof[pos + 1:pos + 1 + 31]
            if _to_bits(v0)[:depth + 1] != _to_bits(val)[:depth] + [0]:
                return False, None
            possible, v1 = _confirm_included(depth + 1, proof, pos + 1 + 31, val)
            if not possible:
                return False, None
            return True, hasher(TERM0 + v0 + v1)
    elif t == TERM1:
        if bits[depth] == 1:
            if len(proof) != pos + 1 + 31 + 31:
                return False, None
            if proof[pos + 1 + 31:] == val:
                return False, None
            if _to_bits(proof[pos + 1:pos + 1 + 31])[:depth + 1] != _to_bits(val)[depth + 1]:
                return False, None
            return True, hasher(proof[pos:])
        else:
            if len(proof) < pos + 1 + 31:
                return False, None
            v1 = proof[pos + 1:pos + 1 + 31]
            if _to_bits(v1)[:depth + 1] != _to_bits(val)[:depth] + [0]:
                return False, None
            possible, v0 = _confirm_not_included(depth + 1, proof, pos + 1 + 31, val)
            if not possible:
                return False, None
            return True, hasher(TERM1 + v0 + v1)
    elif t == TERMBOTH:
        if len(proof) != pos + 1 + 31 + 31:
            return False, None
        v0 = proof[pos + 1:pos + 1 + 31]
        v1 = proof[pos + 1 + 31:pos + 1 + 31 + 31]
        if v0 == val:
            return False, None
        if v1 == val:
            return False, None
        if _to_bits(v0)[:depth] != _to_bits(val)[:depth]:
            return False, None
        if _to_bits(v1)[:depth] != _to_bits(val)[:depth]:
            return False, None
        if not v0 < v1:
            return False, None
        return True, hasher(proof[pos:])
    elif t == MIDDLE:
        if len(proof) != pos + 1 + 31:
            return False, None
        if bits[depth] == 0:
            v1 = proof[pos + 1:pos + 1 + 31]
            possible, v0 = _confirm_not_included(depth + 1, proof, pos + 1 + 31, val)
        else:
            v0 = proof[pos + 1:pos + 1 + 31]
            possible, v1 = _confirm_not_included(depth + 1, proof, pos + 1 + 31, val)
        if not possible:
            return False, None
        return True, hasher(MIDDLE + v0 + v1)

class MerkleSet:
    def __init__(self, size, depth, leaf_units):
        self.size = 0
        self.subblock_lengths = [12]
        while len(subblock_lengths) < depth:
            self.subblock_lengths.append(65 + 2 * self.subblock_lengths[-1])
        self.block_size = self.subblock_lengths[-1] + 4
        self.leaf_units = leaf_units
        self.rootval = EMPTY
        # should be dumped completely on a port to C in favor of real dereferencing.
        self.pointers_to_arrays = {}
        self.spare_leaf = None
        self.rootblock = None

    def _allocate_branch(self):
        b = bytearray(self.blocksize)
        self.pointers_to_arrays[self._deref_branch(branch)] = b
        return b

    def _deallocate_branch(self, branch):
        del self.pointers_to_arrays[self._deref_branch(branch)]

    def _ref_branch(self, ref):
        assert len(ref) == 8
        if ref == bytes(8):
            return None
        return self.pointers_to_arrays[ref]

    def _deref_branch(self, branch):
        if branch is None:
            return bytes(8)
        return to_bytes(id(b), 6)

    def _allocate_leaf(self):
        if self.spare_leaf is not None:
            leaf = self.spare_leaf
            self.spare_leaf = None
            # porting to C, okay?
            leaf[:] = bytes(len(leaf))
        else:
            leaf = bytearray(4 + self.leaf_units * (1 + 31 + 31 + 2 + 2))
        for i in range(self.leaf_units):
            p = 5 + i * (1 + 31 + 31 + 2 + 2)
            leaf[p:p + 2] = to_bytes((i + 1) if i != self.leaf_units - 1 else 0xFFFF, 2)
        self.pointers_to_arrays[self._deref_leaf(leaf)] = leaf
        return leaf

    def _deallocate_leaf(self, leaf):
        del self.pointers_to_arrays[self._deref_leaf(leaf)]

    def _ref_leaf(self, ref):
        assert len(ref) == 8
        if ref == bytes(8):
            return None
        return self.pointers_to_arrays[ref]

    def _deref_leaf(self, leaf):
        return to_bytes(id(leaf), 6)

    def get_root(self):
        if self.size == 0:
            return EMPTY
        if self.size == 1:
            return hasher(SINGULAR + self.root + self.root)
        if self.root == INVALID:
            self.root = self._force_calculation(self.rootblock + 5, len(self.subblock_lengths)-1)
        return self.root

    def get_size(self):
        return self.size

    def _force_calculation_branch(self, posref, moddepth):
        if moddepth == 0:
            block = posref[0:4]
            pos = from_bytes(posref[4:6])
            if pos == 0:
                return self._force_calculation(self.block_size * block + 4, len(self.subblock_lengths))
            else:
                return self._force_calculation_leaf(self.allocator.get_block(block), pos)
        t = posref[0:1][0]
        hit = False
        if t & INVALID0:
            posref[1:1 + 31] = self._force_calculation(posref + 63, moddepth - 1)
            hit = True
        if t & INVALID1:
            posref[1 + 31:1 + 62] = self._force_calculation(pos + 63 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            hit = True
        if hit:
            posref[0:1] = t & 0x0F
        return hasher(posref[0:1 + 62])

    def _force_calculation_leaf(self, block, pos):
        p = block + pos
        t = p[:1][0]
        hit = False
        if t & INVALID0:
            p[1:1 + 31] = self._force_calculation_leaf(block, from_bytes(p[1 + 31 + 31:1 + 31 + 31 + 2]))
            hit = True
        if t & INVALID1:
            p[1 + 31:1 + 31 + 31] = self._force_calculation_leaf(block, from_bytes(p[1 + 31 + 31 + 2:1 + 31 + 31 + 4]))
            hit = True
        if hit:
            p[:1] = bytes([t & 0x0F])
        return hasher(p[:1 + 62])

    def add(self, toadd):
        return self.add_already_hashed(shahash(toadd))

    def add_already_hashed(self, toadd):
        assert len(toadd) == 32
        toadd = toadd[:-1]
        if self.size == 0:
            self.root = toadd
            self.size = 1
        elif self.size == 1:
            self.rootblock = self._allocate_branch()
            self._insert_branch_two(self.root, toadd, 0, 4, 0, len(self.subblock_lengths) - 1)
            self.root = INVALID
        else:
            if self._add_to_branch(toadd, _to_bits(toadd), 0, 4, 0, len(self.subblock_lengths) - 1) == INVALIDATING:
                self.root = INVALID

    # returns INVALIDATING, DONE
    def _add_to_branch(self, toadd, block, depth):
        return self._add_to_branch_inner(toadd, block, 8, depth, len(self.subblock_lengths))

    # returns NOTSTARTED, INVALIDATING, DONE
    def _add_to_branch_inner(self, toadd, block, pos, depth, moddepth):
        if moddepth == 0:
            newblock = from_bytes(self.memory[pos:pos + 4])
            pos = from_bytes(self.memory[pos + 4:pos + 6])
            if pos == 0:
                return self._add_branch_one(toadd_bits, toadd_bits, newblock, newblock * self.block_size + 4, depth, len(self.subblock_lengths) - 1)
            else:
                state, oneval = self._add_leaf_one(toadd, toadd_bits, block, newblock * self.blocksize, pos, depth)
                if oneval != 0:
                    self.memory[pos + 4:pos + 6] = to_bytes(oneval)
                return state
        if moddepth == 1:
            if self.memory[pos:pos + 1] == NOTHING:
                return NOTSTARTED
        newpos = pos + 1 + 64
        if toadd_bits[depth] == 1:
            newpos += self.subblock_lengths[moddepth - 1]
        r = self._add_branch_one(toadd, toadd_bits, block, newpos, depth + 1, moddepth - 1)
        if r == DONE:
            return DONE
        elif r == INVALIDATING:
            npos = pos + 1
            if toadd_bits[depth] == 1:
                npos += 32
            if self.memory[npos:npos + 32] == INVALID:
                return DONE
            self.memory[npos:npos + 32] = INVALID
            return INVALIDATING
        t = self.memory[pos:pos + 1]
        if t == NOTHING:
            return NOTSTARTED
        if toadd_bits[depth] == 0:
            if t in (MIDDLE, ONLY0, TERM1):
                r = self._add_branch_one(toadd, toadd_bits, block, pos + 1 + 64, depth + 1, moddepth - 1)
                if r == DONE:
                    return DONE
                elif r == INVALIDATING:
                    if self.memory[pos + 1:pos + 1 + 32] == INVALID:
                        return DONE
                    self.memory[pos + 1:pos + 1 + 32] = INVALID
                    return INVALIDATING
            elif t == ONLY1:
                self.memory[pos:pos + 1] = TERM0
                self.memory[pos + 1:pos + 1 + 32] = toadd
                self.size += 1
                return INVALIDATING
            elif t == TERM0:
                if self.memory[pos + 1:pos + 1 + 32] == toadd:
                    return DONE
                r = self._add_branch_two(self.memory[pos + 1:pos + 1 + 32], toadd, toadd_bits, block, pos + 1 + 64, depth + 1, moddepth - 1)
                if r == DONE:
                    return DONE
                else:
                    assert r == INVALIDATING
                    self.memory[pos:pos + 1] = MIDDLE
                    self.memory[pos + 1:pos + 1 + 32] = INVALID
                    return INVALIDATING
            elif t == TERMBOTH:
                if self.memory[pos + 1:pos + 1 + 32] == toadd:
                    return DONE
                r = self._add_branch_two(self.memory[pos + 1:pos + 1 + 32], toadd, toadd_bits, block, pos + 1 + 64, depth + 1, moddepth - 1)
                if r == DONE:
                    return DONE
                else:
                    assert r == INVALIDATING
                    self.memory[pos:pos + 1] = TERM1
                    self.memory[pos + 1:pos + 1 + 32] = INVALID
                    return INVALIDATING
            else:
                assert False
        else:
            if t in (MIDDLE, ONLY1, TERM0):
                r = self._add_branch_one(toadd, toadd_bits, block, pos + 1 + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                if r == DONE:
                    return DONE
                elif r == INVALIDATING:
                    if self.memory[pos + 1 + 32:pos + 1 + 64] == INVALID:
                        return DONE
                    self.memory[pos + 1 + 32:pos + 1 + 64] = INVALID
                    return INVALIDATING
            elif t == ONLY0:
                self.memory[pos:pos + 1] = TERM1
                self.memory[pos + 1 + 32:pos + 1 + 64] = toadd
                self.size += 1
                return INVALIDATING
            elif t == TERM1:
                if self.memory[pos + 1 + 32:pos + 1 + 64] == toadd:
                    return DONE
                r = self._add_branch_two(self.memory[pos + 1 + 32:pos + 1 + 64], toadd, toadd_bits, block, pos + 1 + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                if r == DONE:
                    return DONE
                else:
                    assert r == INVALIDATING
                    self.memory[pos:pos + 1] = MIDDLE
                    self.memory[pos + 1 + 32:pos + 1 + 64] = INVALID
                    return INVALIDATING
            elif t == TERMBOTH:
                if self.memory[pos + 1 + 32:pos + 1 + 64] == toadd:
                    return DONE
                r = self._add_branch_two(self.memory[pos + 1 + 32:pos + 1 + 64], toadd, toadd_bits, block, pos + 1 + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                if r == DONE:
                    return DONE
                else:
                    assert r == INVALIDATING
                    self.memory[pos:pos + 1] = TERM0
                    self.memory[pos + 1 + 32:pos + 1 + 64] = INVALID
                    return INVALIDATING
            else:
                assert False

    # returns INVALIDATING
    def _insert_branch_three(self, things, block, pos, depth, moddepth):
        if moddepth == 0:
            self._insert_leaf_three(things, block, pos, depth)
            return INVALIDATING
        assert pos nulled out
        if all bits are the same:
            put data in block
            newpos = booga booga
            self._insert_branch_three(things, block, newpos, depth + 1, moddepth - 1)
        else:
            put data in block
            newpos = booga booga
            self._insert_branch_two(newthings, block, newpos, depth + 1, moddepth - 1)
        return INVALIDATING

    # returns INVALIDATING
    def _insert_branch_two(self, things, block, pos, depth, moddepth):
        if moddepth == 0:
            if necessary, make a new active child
            self._insert_leaf_two(things, active child, beginning)
            return INVALIDATING
        insert TERMBOTH directly
        return INVALIDATING

    def _delete_section_from_leaf(self, leaf, pos):
        if there is anything below in high bit:
            self._delete_section_from_leaf(high bit area)
        if there is anything below in low bit:
            self._delete_section_from_leaf(low bit area)
        make pos cell point to firstpos
        reset firstpos to pos

    # returns whether succeeded
    def _copy_section_between_leafs(self, from, to, pos):
        topos = firstpos of to
        if topos is bad:
            return False
        set firstpos of to to next
        copy local branch over
        lowpos = None
        if there is anything below in low bit:
            lowpos = next position
            if not self._copy_section_between_leafs(low area):
                reset topos cell to point to firstpos
                set firstpos to next
                return False
        if there is anything below in high bit:
            if not self._copy_section_between_leafs(high area):
                self._delete_section_from_leaf(lowpos area)
                reset topos cell to point to firstpos
                set firstpos to next
                return False
        return True

    # state can be INVALIDATING, DONE
    def _add_to_leaf(self, toadd, branch, branchpos, leaf, pos, depth):
        booga call _add_to_leaf_inner
        if not FULL:
            return result of inner call
        if only one thing in leaf:
            copy into new branch
            update branch
            add to new branch
            return INVALIDATING
        if leaf is not active_child and there is an active_child:
            copy into active_child
            if not FULL:
                delete old copy
                call _add_to_leaf
                return INVALIDATING
        make a new active_child
        copy into new active_child
        assert did not fail
        delete old copy
        call _add_to_leaf
        return INVALIDATING

    # returns INVALIDATING, DONE, FULL
    def _add_to_leaf_inner(self, toadd, leaf, pos, depth):
        if the next bit of toadd is lower:
            if the next thing is empty:
                insert next thing into slot
                mark as terminal
                return INVALIDATING
            invalid = whether currently invalid
            if the next thing is not terminal:
                result = self._add_to_leaf_inner(next level)
            else:
                if next thing is the same as toadd:
                    return DONE
                result = self._insert_leaf_two(toadd and other value):
                if result != FULL:
                    increase size by 1
            if not invalid and result == INVALIDATING:
                mark invalid
            return result
        else:
            if the next thing is empty:
                insert next thing into slot
                mark as terminal
                return INVALIDATING
            invalid = whether currently invalid
            if the next thing is not terminal:
                result = self._add_to_leaf_inner(next level)
            else:
                if next thing is the same as toadd:
                    return DONE
                result = self._insert_leaf_two(toadd and other value):
                if result != FULL:
                    increase size by 1
            if not invalid and result == INVALIDATING:
                mark invalid
            return result

    # returns branch
    def _move_leaf_to_branch(self, leaf, pos):
        branch = new branch
        self._move_leaf_to_branch_inner(branch leaf pos)
        delete leaf
        return branch

    def _move_leaf_to_branch_inner(self, branch, branchpos, moddepth, leaf, leafpos):
        if moddepth == 0:
            if there is no active child:
                make new active child
            if not self._copy_section_between_leafs(to active child):
                make new active child
                result = self._copy_section_between_leafs(to active child)
                assert result
            insert child info to branchpos
            return
        copy cell
        if there is anything in the 0 position:
            self._move_leaf_to_branch_inner(0 position)
        if there is anything in the 1 position:
            self._move_leaf_to_branch_inner(1 position)

    # returns INVALIDATING
    def _insert_leaf_three(self, things, branch, branchpos, depth):
        assert branch data are nulled out
        if there is no active child:
            make new active child
        pos = active child first pos
        result = self._insert_leaf_three_inner(things, active child, pos, depth)
        if result != INVALIDATING:
            make a new active child
            pos = active first pos
            result, pos = self._insert_leaf_three_inner(things, active child, pos, depth)
            assert result == INVALIDATING
        increase inputs by one
        insert at branchpos active_child, pos
        return INVALIDATING

    # returns INVALIDATING
    def _insert_leaf_two(self, things, branch, branchpos):
        assert branch data are nulled out
        if there is no active child:
            make a new active child
        pos = active first pos
        result = self._insert_leaf_two_inner(things, active child, pos)
        if result != INVALIDATING:
            make a new active child
            pos = active first pos
            result = self._insert_leaf_two_inner(booga booga)
            assert result == INVALIDATING
        increase inputs by one
        insert at branchpos active_child, pos
        return INVALIDATING

    # returns INVALIDATING, FULL
    def _insert_leaf_three_inner(self, things, leaf, pos, depth):
        if pos is bad:
            return FULL
        nextpos = nextpointer from pos
        if all three next bits are the same:
            result, newpos = self._insert_leaf_three(things, leaf, nextpos, depth + 1)
            if result == FULL:
                return FULL
            if bits are zero:
                insert with empty in 1 to mypos
            else:
                insert with empty in 0 to mypos
            return INVALIDATING
        else:
            result = self._insert_leaf_two_inner(remaining things, leaf, nextpos, depth + 1)
            if result == FULL:
                return FULL
            if there are two in the zero:
                insert with terminal in 1
            else:
                insert with terminal in 0
            return INVALIDATING

    # returns INVALIDATING, FULL
    def _insert_leaf_two_inner(self, things, leaf, pos):
        if pos is bad:
            return FULL
        set nextpos in leaf to next link after pos
        insert BOTHTERM into pos
        return INVALIDATING

    def remove(self, toremove):
        return self.remove_already_hashed(shahash(toremove))

    def remove_already_hashed(self, toremove):
        assert len(toremove) == 32
        toremove = toremove[:-1]
        if self.root == EMPTY:
            return
        if self.size == 1:
            if self.root == toremove:
                self.size = 0
                self.root = EMPTY
            return
        status, oneval = self._remove_branch(toremove, 4, 0, len(self.subblock_lengths))
        if status == INVALIDATING:
            self.root = INVALID
        elif status == DONE:
            pass
        elif status == ONELEFT:
            assert self.size == 1
            self.root = oneval
            deallocate root branch
        else:
            assert False

    # returns (status, oneval)
    # status can be ONELEFT, INVALIDATING, DONE
    def _remove_branch(self, toremove, block, pos, depth):
        result, val = self._remove_branch_inner(my vals)
        assert result != NOTSTARTED
        if result == ONELEFT:
            delete branch
        return result, val

    # returns (status, oneval)
    # status can be NOTSTARTED, ONELEFT, INVALIDATING, DONE
    def _remove_branch_inner(self, toremove, pos, depth, moddepth):
        if moddepth == 0:
            if outpointer is to nothing:
                return NOTSTARTED, None
            if pos is bad:
                r, val = booga _remove_branch
            else:
                r, val = self._remove_leaf(toremove, toremove_bits, pos, depth)
            if r == ONELEFT:
                zero out at pos
            return (r, val)
        was_invalid = invalid 0 bit or invalid 1 bit
        if next bit == 0:
            state, oneval = remove from 0 pos
            if state == DONE:
                return DONE, None
            elif state == INVALIDATING:
                if 0 invalid bit is not set:
                    set 0 invalid bit
            elif state == NOTSTARTED:
                if there is nothing at the current pos:
                    return NOTSTARTED, None
                assert terminal in 0
                if thing in 0 is toremove:
                    self.size -= 1
                    if terminal in 1:
                        oneval = thing in 1
                        zero out data
                        return ONELEFT, oneval
                    mark 0 as not terminal, valid, zero out
                    c = collapse down 1
                    if c is not None:
                        overwrite with c
                        mark both valid and terminal
                elif terminal in 1 and thing in 1 is toremove:
                    self.size -= 1
                    oneval = thing in 0
                    zero out data
                    return ONELEFT, oneval
                else:
                    return DONE, None
            else:
                assert state == ONELEFT
                if 1 pos is not terminal or branch:
                    zero out data
                    return ONELEFT, oneval
                put oneval into 0 pos
                mark 0 pos as terminal, not branch, valid
        else:
            state, oneval = remove from 1 pos
            if state == DONE:
                return DONE, None
            elif state == INVALIDATING:
                if 1 invalid bit is not set:
                    set 1 invalid bit
            elif state == NOTSTARTED:
                if there is nothing at the current pos:
                    return NOTSTARTED, None
                assert terminal in 1
                if thing in 1 is toremove:
                    self.size -= 1
                    if terminal in 0:
                        oneval = thing in 0
                        zero out data
                        return ONELEFT, oneval
                    mark 1 as not terminal, valid, zero out
                    c = collapse down 0
                    if c is not None:
                        overwrite with c
                        mark both valid and terminal
                elif terminal in 0 and thing in 0 is toremove:
                    self.size -= 1
                    oneval = thing in 1
                    zero out data
                    return ONELEFT, oneval
                else:
                    return DONE, None
            else:
                assert state == ONELEFT
                if 0 pos is not terminal or branch:
                    zero out data
                    return ONELEFT, oneval
                put oneval into 1 pos
                mark 1 pos as terminal, not branch, valid
        if not was_invalid:
            return INVALIDATING, None
        return DONE, None

    # returns (status, oneval)
    # status can be ONELEFT, INVALIDATING, DONE
    def _remove_leaf(self, toremove, block, pos, depth):
        result, val = call _remove_leaf_inner
        if result == ONELEFT:
            deallocate block
        return result

    # returns (status, oneval)
    # status can be ONELEFT, INVALIDATING, DONE
    def _remove_leaf_inner(self. toremove, block, pos, depth):
        if next bit is 0:
            if nothing in 0 position:
                return DONE
            if terminal in 0 position:
                if 0 val is toremove:
                    v = _collapse_leaf
                    if v is not None:
                        set pos to v
                    self.size -= 1
                    return INVALIDATING
                else:
                    return DONE
            call _remove_leaf_inner on next depth
        else:
            if nothing in 1 position:
                return DONE
            if terminal in 1 position:
                if 1 val is toremove:
                    v = _collapse_leaf
                    if v is not None:
                        set pos to v
                    self.size -= 1
                    return INVALIDATING
                else:
                    retun DONE
            call _remove_leaf_inner on next depth

    # returns BOTHTERM string or None
    def _collapse_branch_inner(self, block, pos, moddepth):
        if moddepth == 0:
            if next is branch:
                r = collapse branch
                if r is not None:
                    deallocate branch
                    zero out data
            else:
                r = collapse leaf
                if r is not None:
                    deallocate leaf
                    zero out data
            return r
        if both terminal:
            r = my data
        elif nothing in 0:
            r = collapse branch in 1
        elif nothing in 1:
            r = collapse branch in 0
        else:
            return None
        if r is not None:
            zero out data
        return r

    # returns BOTHTERM string or None
    def _collapse_leaf(self, block, pos):
        if bothterm:
            result = my string
        elif nothing in 0 position:
            result = _collapse_leaf in 1
        elif nothing in 1 position:
            result = collapse leaf in 0
        else:
            return None
        if result is not None:
            deallocate pos
        return result

    def _allocate_in_leaf(self, block):
        next = firstpos
        set firstpos to nextpointer of next
        return next

    def _deallocate_in_leaf(self, block, pos):
        next = current firstpos
        if pos == TERMNODE:
            return None
        zero out pos and set next in it
        set firstpos to next

    def batch_add_and_remove(self, toadd, toremove):
        self.batch_add_and_remove_already_hashed({shahash(x) for x in toadd}, {shahash(x) for x in toremove})

    def batch_add_and_remove_already_hashed(self, toadd, toremove):
        toadd = sorted(toadd)
        toremove = sorted(toremove)
        addpos = 0
        removepos = 0
        while addpos < len(toadd) or removepos < len(toremove):
            while addpos < len(toadd) and (removepos == len(toremove) or toadd[addpos] < toremove[removepos]):
                self.add_already_hashed(toadd[addpos])
                addpos += 1
            while removepos < len(toremove) and (addpos == len(toadd) or toremove(removepos) < toadd[addpos]):
                self.remove_already_hashed(toremove[removepos])
                removepos += 1
            if addpos < len(toadd) and removepos < len(toremove) and toadd[addpos] == toremove[removepos]:
                lastval = toadd[addpos]
                while addpos < len(toadd) and toadd[addpos] == lastval:
                    addpos += 1
                while removepos < len(toremove) and toremove[removepos] == lastval:
                    removepos += 1

    # returns (boolean, proof string)
    def is_included(self, tocheck):
        return self.is_included_already_hashed(shahash(tocheck))

    # returns (boolean, proof string)
    def is_included_already_hashed(self, tocheck):
        assert len(tocheck) == 32
        tocheck = tocheck[:-1]
        return self._is_included_outer(tocheck, None)

    # returns (boolean, proof string)
    def is_included_make_proof(self, tocheck):
        return self.is_included_make_proof_already_hashed(shahash(tocheck))

    # returns (boolean, proof string)
    def is_included_make_proof_already_hashed(self, tocheck):
        assert len(tocheck) == 32
        buf = []
        r = return self._is_included(tocheck, buf)
        return r, b''.join(buf)

    # returns boolean
    def _is_included_outer(self, tocheck, buf):
        self.get_root()
        if self.size == 0:
            return False
        if self.size == 1:
            if buf is not None:
                buf.append(SINGULAR)
            if tocheck == self.root:
                return True
            else:
                if buf is not None:
                    buf.append(self.root)
                return False
        return self._is_included(tocheck, _to_bits(tocheck), 5, 0, len(self.subblock_lengths)-1, None, buf)

    # returns True, False, NOTSTARTED
    def _is_included(self, tocheck, tocheck_bits, pos, depth, moddepth, buf):
        if moddepth == 0:
            bnum = from_bytes(self.memory[pos:pos + 4])
            bpos = from_bytes(self.memory[pos + 4:pos + 6])
            if bpos == 0:
                return self._is_included(tocheck, tocheck_bits, bnum * self.block_size + 4, depth, len(self.subblock_lengths), buf)
            else:
                return self._is_included_leaf(tocheck, tocheck_bits, bnum * self.block_size, bpos, depth, buf)
        newpos = pos + 65
        if tocheck_bits[depth] == 1:
            newpos += self.subblock_lengths[moddepth - 1]
        def b(x):
            if buf:
                buf.append(x)
        if buf is None and moddepth > 1:
            v = self._is_included(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
            if v != NOTSTARTED:
                return v
        t = self.memory[pos:pos + 1]
        b(t)
        if t == NOTHING:
            return NOTSTARTED
        elif t == MIDDLE:
            if tocheck_bits[depth] == 1:
                b(self.memory[pos + 1:pos + 1 + 32])
            else:
                b(self.memory[pos + 1 + 32:pos + 1 + 64])
            return self._is_included(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
        elif t == ONLY0:
            if tocheck_bits[depth] == 0:
                return self._is_included(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
            else:
                b(self.memory[pos + 1:pos + 1 + 32])
                return False
        elif t == ONLY1:
            if tocheck_bits[depth] == 0:
                b(self.memory[pos + 1:pos + 1 + 32])
                return False
            else:
                return self._is_included(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
        elif t == TERM0:
            if tocheck_bits[depth] == 0:
                if self.memory[pos + 1:pos + 1 + 32] == tocheck:
                    b(self.memory[pos + 1 + 32:pos + 1 + 64])
                    return True
                else:
                    b(self.memory[pos + 1:pos + 1 + 64])
                    return False
            else:
                b(self.memory[pos + 1:pos + 1 + 32])
                return self._is_included(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
        elif t == TERM1:
            if tocheck_bits[depth] == 0:
                b(self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32])
                return self._is_included(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
            else:
                if self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32] == tocheck:
                    b(self.memory[pos + 1:pos + 1 + 32])
                    return True
                else:
                    b(self.memory[pos + 1:pos + 1 + 32])
                    b(self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32])
                    return False
        elif t == TERMBOTH:
            if tocheck_bits[depth] == 0:
                if self.memory[pos + 1:pos + 1 + 32] == tocheck:
                    b(self.memory[pos + 1 + 32:pos + 1 + 64])
                    return True
                else:
                    b(self.memory[pos + 1:pos + 1 + 64])
                    return False
            else:
                if self.memory[pos + 1 + 32:pos + 1 + 64] == tocheck:
                    b(self.memory[pos + 1:pos + 1 + 32])
                    return True
                else:
                    b(self.memory[pos + 1:pos + 1 + 64])
                    return False
        else:
            raise IntegrityError()

    def _is_included_leaf(self, tocheck, tocheck_bits, block_base, pos, depth, buf = None):
        booga booga
        pos += block_base
        def child(p):
            return self._is_included_leaf(tocheck, tocheck_bits, block_base, from_bytes(self.memory[pos + p:pos + p + 2]), depth + 1, buf)
        def b(a, b):
            if buf:
                buf.append(self.memory[pos + a:pos + a + b])
        b(pos, 1)
        t = self.memory[pos:pos + 1]
        if t == MIDDLE:
            if tocheck_bits[depth] == 0:
                b(1 + 32 + 2, 32)
                return child(33)
            else:
                b(1, 32)
                return child(1)
        elif t == ONLY0:
            if tocheck_bits[depth] == 0:
                return child(33)
            else:
                b(1, 32)
                return False
        elif t == ONLY1:
            if tocheck_bits[depth] == 1:
                return child(33)
            else:
                b(1, 32)
                return False
        elif t == TERM0:
            if tocheck_bits[depth] == 0:
                if tocheck == self.memory[pos + 1:pos + 1 + 32]:
                    b(1 + 32, 32)
                    return True
                else:
                    b(1, 64)
                    return False
            else:
                b(1, 32)
                return child(65)
        elif t == TERM1:
            if tocheck_bits[depth] == 0:
                b(1 + 32 + 2, 32)
                return child(33)
            else:
                if tocheck == self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32]:
                    b(1, 32)
                    return True
                else:
                    b(1, 32)
                    b(1 + 32 + 2, 32)
                    return False
        elif t == TERMBOTH:
            if tocheck_bits[depth] == 0:
                if tocheck == self.memory[pos + 1:pos + 1 + 32]:
                    b(1 + 32, 32)
                    return True
                else:
                    b(1, 64)
                    return False
            else:
                if tocheck == self.memory[pos + 1:pos + 1 + 32]:
                    b(1, 32)
                    return True
                else:
                    b(1, 64)
                    return False
        else:
            raise IntegrityError()
