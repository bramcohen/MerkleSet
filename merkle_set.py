from hashlib import sha256

def hasher(mystr, safe = True):
    if safe:
        assert len(mystr) == 63
    return sha256(mystr).digest()[:-1]

"""
Advantages of this merkle tree implementation:
Lazy root calculation
Few l1 and l2 cache misses
Small proofs of inclusion/exclusion
Reasonably simple implementation
Reasonably efficient in memory
Reasonable defense against malicious insertion attacks

TODO: Port to C
TODO: Switch to non-padding variant of sha256
TODO: Optimize! Benchmark!
TODO: add multi-threading support
TODO: add support for continuous self-auditing
TODO: Try heuristically calculating hashes non-lazily when they're likely to be needed later
TODO: Try unrolling all this recursivity to improve performance


# all unused should be zeroed out
branch: active_child 8 patricia[size]
patricia[n]: type 1 hash 31 hash 31 patricia[n-1] patricia[n-1]
# pos 0xFFFF means child is a branch
patricia[0]: block 8 pos 2
type: ONLY0 or ONLY1 or TERM0 or TERM1 or TERMBOTH or MIDDLE or NOTHING

# first_unused is the start of linked list, 0xFFFF for terminal
leaf: first_unused 2 num_inputs 2 [node or emptynode]
node: type 1 hash0 31 hash1 31 pos0 2 pos1 2
type: MIDDLE or ONLY0 or ONLY1 or TERM0 or TERM1 or TERMBOTH or NOTHING
emptynode: NOTHING 1 next 2

# EMPTY always has proofs of length 0
inclusion_proof: [unit]
unit: only0 or only1 or term0 or term1 or bothterm or middle or singular
only0: ONLY0 1
only1: ONLY1 1
term0: TERM0 1 hash 31
term1: TERM1 1 hash 31
bothterm: TERMBOTH 1 hash 31
middle: MIDDLE 1 hash 31
singular: SINGULAR 1

# EMPTY always has proofs of length 0
exclusion_proof: [unit]
unit: only0 or only1 or term0 or term1 or bothterm or middle or singular
only0: ONLY0 1 (hash 31)
only1: ONLY1 1 (hash 31)
term0: TERM0 1 hash 31 (hash 31)
term1: TERM1 1 hash 31 (hash 31)
bothterm: TERMBOTH 1 hash 31 hash 31
middle: MIDDLE 1 hash 31
singular: SINGULAR 1 hash 31

bits for type:
0 invalid, 1 invalid, unused, singular, branch in 0, terminal in 0, branch in 1, terminal in 1
"""

EMPTY = bytes([0]) * 31
INVALID = bytes([1]) * 31

TERMNODE = bytes([0xFF, 0xFF])

INVALID0 = 0x80
INVALID1 = 0x40
SINGULAR = 0x10
BRANCH0 = 0x08
END0 = 0x04
BRANCH1 = 0x02
END1 = 0x01

MIDDLE = BRANCH0 | BRANCH1
ONLY0 = BRANCH0
ONLY1 = BRANCH1
TERM0 = END0 | BRANCH1
TERM1 = BRANCH0 | END1
TERMBOTH = END0 | END1
NOTHING = 0

Maybe = 2

NOTSTARTED = 0
ONELEFT = 1
INVALIDATING = 2
DONE = 3
FAILED = 4
NEWPOS = 5

def confirm_included(root, val, proof):
    return confirm_included_already_hashed(root, hasher(val, False), proof)

def confirm_included_already_hashed(root, val, proof):
    assert len(root) == 31
    assert len(val) == 31
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
    return confirm_included_already_hashed(root, hasher(val, False), proof)

def confirm_not_included_already_hashed(root, val, proof):
    assert len(root) == 31
    assert len(val) == 31
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
        self.rootblock = self._allocate_branch()

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
        del self.pointers_to_arrays[self._deref_leaf(leaf), 6)]

    def _ref_leaf(self, ref):
        return self.pointers_to_arrays[ref]

    def _deref_leaf(self, leaf):
        return to_bytes(id(leaf), 6)

    def get_root(self):
        if self.size == 0:
            return EMPTY
        if self.size == 1:
            return hasher(self.root)
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
        return self.add_already_hashed(hasher(toadd, False))

    def add_already_hashed(self, toadd):
        assert len(toadd) == 31
        if self.size == 0:
            self.root = toadd
            self.size = 1
        elif self.size == 1:
            allocate root branch
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
                    assert r == INVALIDATING:
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
                    assert r == INVALIDATING:
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
                    assert r == INVALIDATING:
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
                    assert r == INVALIDATING:
                    self.memory[pos:pos + 1] = TERM0
                    self.memory[pos + 1 + 32:pos + 1 + 64] = INVALID
                    return INVALIDATING
            else:
                assert False

    def _insert_branch_three(self, things, block, pos, depth, moddepth):
        if moddepth == 0:
            blockbegin = block * self.block_size
            active_child = from_bytes(self.memory[blockbegin:blockbegin + 4])
            if active_child == 0:
                new_child = self.first_unused
                if new_child == 0:
                    raise OutOfMemoryError()
                self.memory[blockbegin:blockbegin + 4] = to_bytes(new_child, 4)
                newbegin = new_child * self.block_size
                self.first_unused = from_bytes(self.memory[newbegin:newbegin + 4])
                self.memory[newbegin:newbegin + 2] = to_bytes(4, 2)
                self.memory[newbegin + 2:newbegin + 4] = to_bytes(0, 2)
            else:
                newbegin = active_child * self.block_size
            result, newpos = self._add_leaf_two(old, oldbits, toadd, toadd_bits, block, newbegin, depth, from_bytes(self.memory[newbegin:newbegin + 2]))
            if result == DONE:
                return DONE
            self.memory[newbegin + 2:newbegin + 4] = to_bytes(from_bytes(self.memory[newbegin + 2:newbegin + 4]) + 1, 2)
            self.memory[pos:pos + 4] = to_bytes(active_child)
            self.memory[pos + 4:pos + 6] = to_bytes(newpos)
        if self.memory[pos:pos + 1] != NOTHING:
            raise IntegrityError()
        if oldbits[depth] != toadd_bits[depth]:
            self.memory[pos:pos + 1] = TERMBOTH
            if oldbits[depth] == 0:
                self.memory[pos + 1:pos + 1 + 32] = old
                self.memory[pos + 1 + 32:pos + 1 + 64] = toadd
            else:
                self.memory[pos + 1:pos + 1 + 32] = toadd
                self.memory[pos + 1 + 32:pos + 1 + 64] = old
            return INVALIDATING
        newpos = pos + 1 + 64
        if oldbits[depth] == 1:
            newpos += self.subblock_lengths[moddepth - 1]
        return self._add_branch_two_inner(self, old, oldbits, toadd, toadd_bits, block, newpos, depth + 1, moddepth - 1)

    def _insert_branch_two(self, thing1, thing2, block, pos, depth, moddepth):
        if moddepth == 0:
            call _insert_leaf_two
        insert directly

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

    # returns state, memblock, pos
    # state can be INVALIDATING, DONE, NEWPOS
    def _add_to_leaf(self, toadd, branch, leaf, pos, depth):
        booga call _add_to_leaf_inner
        if not failed:
            return result of inner call
        if only one thing in leaf:
            copy into branch
            add to branch
            return NEWPOS
        if leaf is not active_child and there is an active_child:
            copy into active_child
            if not failed:
                delete old copy
                call _add_to_leaf
                return NEWPOS
        make a new active_child
        copy into new active_child
        assert did not fail
        delete old copy
        return NEWPOS

    # returns INVALIDATING, DONE, FAILED
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
                if result != FAILED:
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
                if result != FAILED:
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

    # returns INVALIDATING, FAILED
    def _insert_leaf_three(self, thinga, thingb, thingc, leaf, depth):
        if firstpos is bad:
            return FAILED
        mypos = firstpos
        set firstpos to mypos next
        if all three next bits are the same:
            if bits are zero:
                insert with empty in 1 to mypos
            else:
                insert with empty in 0 to mypos
            result = self._insert_leaf_three(thinga, thingb, thingc, leaf, depth + 1)
        else:
            if there are two in the zero:
                insert with terminal in 1
            else:
                insert with terminal in 0
            result = self._insert_leaf_two(remaining things)
        if result == FAILED:
            replace mypos with pointer to firstpos
            set firstpos to mypos
        return result

    # returns INVALIDATING, FAILED
    def _insert_leaf_two(self, things, leaf, pos):
        if firstpos is bad:
            return FAILED
        mypos = firstpos
        set firstpos to mypos next
        insert BOTHTERM into mypos
        return INVALIDATING

    def remove(self, toremove):
        return self.remove_already_hashed(hasher(toadd))

    def remove_already_hashed(self, toremove):
        assert len(toremove) == 31
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

    def _remove_branch(self, toremove, block, depth):
        result, val = self._remove_branch_inner(my vals)
        assert result != NOTSTARTED
        if result == ONELEFT:
            delete branch
        return result, val

    # returns (status, oneval)
    # status can be NOTSTARTED, ONELEFT, INVALIDATING, DONE
    def _remove_branch_inner(self, toremove, pos, depth, moddepth):
        if moddepth == 0:
            if pos is bad:
                return _remove_branch
            return self._remove_outside_leaf(toremove, toremove_bits, pos, depth)
        if moddepth == 1:
            t = sef.memory[pos:pos + 1]
            if t == NOTHING:
                return NOTSTARTED, None
        if toremove_bits[depth] == 0:
            state, oneval = self._remove_branch(toremove, toremove_bits, pos + 1 + 64, depth + 1, moddepth - 1)
        else:
            state, oneval = self._remove_branch(toremove, toremove_bits, pos + 1 + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
        if state == DONE:
            return DONE, None
        if state == INVALIDATING:
            if toremove_bits[depth] == 0:
                ipos = pos + 1
            else:
                ipos + pos + 1 + 32
            if self.memory[ipos:ipos + 32] == INVALID:
                return DONE, None
            else:
                self.memory[ipos:ipos + 32] = INVALID
                return INVALIDATING, None
        t = self.memory[pos:pos + 1]
        if t == NOTHING:
            return NOTSTARTED
        elif t == MIDDLE:
            if state != ONELEFT:
                raise IntegrityError()
            if toremove_bits[depth] == 0:
                self.memory[pos:pos + 1] = TERM0
                self.memory[pos + 1:pos + 1 + 32] = oneval
                return INVALIDATING, None
            else:
                self.memory[pos:pos + 1] = TERM1
                self.memory[pos + 1 + 32:pos + 1 + 64] = oneval
                return INVALIDATING, None
        elif t == ONLY0:
            if toremove_bits[depth] == 0:
                if state != ONELEFT:
                    raise IntegrityError()
                self.memory[pos:pos + 1] = NOTHING
                self.memory[pos + 1:pos + 1 + 32] = bytes(32)
                return ONELEFT, oneval
            else:
                if state != NOTSTARTED:
                    raise IntegrityError()
                return DONE, None
        elif t == ONLY1:
            if toremove_bits[depth] == 0:
                if state != NOTSTARTED:
                    raise IntegrityError()
                return DONE, None
            else:
                if state != ONELEFT:
                    raise IntegrityError()
                self.memory[pos:pos + 1] = NOTHING
                self.memory[pos + 1 + 32:pos + 1 + 64] = bytes(32)
                return ONELEFT, oneval
        elif t == TERM0:
            if toremove_bits[depth] == 0:
                if state != NOTSTARTED:
                    raise IntegrityError()
                if self.memory[pos + 1:pos + 1 + 32] == toremove:
                    self.memory[pos:pos + 1] = ONLY1
                    self.memory[pos + 1:pos + 1 + 32] = bytes(32)
                    self.size -= 1
                    return INVALIDATING, None
                else:
                    return DONE, None
            else:
                if state != ONELEFT:
                    raise IntegrityError()
                self.memory[pos:pos + 1] = TERMBOTH
                self.memory[pos + 1 + 32:pos + 1 + 64] = oneval
                return INVALIDATING, None
        elif t == TERM1:
            if toremove_bits[depth] == 0:
                if state != ONELEFT:
                    raies IntegrityError()
                self.memory[pos:pos + 1] = TERMBOTH
                self.memory[pos + 1:pos + 1 + 32] = oneval
                return INVALIDATING, None
            else:
                if state != NOTSTARTED:
                    raise IntegrityError()
                if self.memory[pos + 1 + 32:pos + 1 + 64] == toremove:
                    self.memory[pos:pos + 1] = ONLY0
                    self.memory[pos + 1 + 32:pos + 1 + 64] = bytes(32)
                    self.size -= 1
                    return INVALIDATING, None
                else:
                    return DONE, None
        elif t == TERMBOTH:
            if state != NOTSTARTED:
                raise IntegrityError()
            if toremove_bits[depth] == 0:
                if self.memory[pos + 1:pos + 1 + 32] == toremove:
                    self.memory[pos:pos + 1] = NOTHING
                    left = self.memory[pos + 1 + 32:pos + 1 + 64]
                    self.memory[pos + 1:pos + 1 + 64] = bytes(64)
                    self.size -= 1
                    return ONELEFT, left
                else:
                    return DONE, None
            else:
                if self.memory[pos + 1 + 32:pos + 1 + 64] == toremove:
                    self.memory[pos:pos + 1] = NOTHING
                    left = self.memory[pos + 1:pos + 1 + 32]
                    self.memory[pos + 1:pos + 1 + 64] = bytes(64)
                    self.size -= 1
                    return ONELEFT, left
                else:
                    return DONE, None
        else:
            raise IntegrityError()

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
                    v = _collapse_leaf_two
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
                    v = _collapse_leaf_two
                    if v is not None:
                        set pos to v
                    self.size -= 1
                    return INVALIDATING
                else:
                    retun DONE
            call _remove_leaf_inner on next depth

    # returns BOTHTERM string on None
    def _collapse_leaf_two(self, block, pos):
        if bothterm:
            x = my string
            deallocate pos
            return x
        if nothing in 0 position:
            result = _collapse_leaf_two on upper position
            if result is not None:
                deallocate pos
            return result
        if nothing in 1 position:
            result = _collapse_leaf_two on lower position
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
        self.batch_add_and_remove_already_hashed({hasher(x) for x in toadd}, {hasher(x) for x in toremove})

    def batch_add_and_remove_already_hashed(self, toadd, toremove):
        toadd = sorted(toadd)
        toremove = sorted(toremove)
        addpos = 0
        removepos = 0
        while addpos < len(toadd) or removepos < len(toremove):
            while addpos < len(toadd) and toadd[addpos] < toremove[removepos]:
                self.add_already_hashed(toadd[addpos])
                addpos += 1
            while removepos < len(toremove) and toremove(removepos) < toadd[addpos]:
                self.remove_already_hashed(toremove[removepos])
                removepos += 1
            if addpos < len(toadd) and removepos < len(toremove) and toadd[addpos] == toremove[removepos]:
                lastval = toadd[addpos]
                while addpos < len(toadd) and toadd[addpos] == lastval:
                    addpos += 1
                while removepos < len(toremove) and toremove[removepos] == lastval:
                    removepos += 1

    def is_included(self, tocheck):
        return self.is_included_already_hashed(hasher(tocheck))

    def is_included_already_hashed(self, tocheck):
        assert len(mystr) == 31
        return self._is_included_outer(tocheck, None)

    def is_included_make_proof(self, tocheck):
        return self.is_included_make_proof_already_hashed(hasher(tocheck, False))

    def is_included_make_proof_already_hashed(self, tocheck):
        assert len(tocheck) == 32
        buf = []
        r = return self._is_included(tocheck, buf)
        return r, b''.join(buf)

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
            if v != Maybe:
                return v
        t = self.memory[pos:pos + 1]
        b(t)
        if t == NOTHING:
            return Maybe
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
