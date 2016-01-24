from hashlib import sha256

def hasher(mystr):
    return sha256(mystr).digest()

# TODO: Port to C
# TODO: Optimize! Benchmark!
# TODO: change the state constants to make bit twiddling a lot prettier
# TODO: truncate the children when calculating nodes to be more sha2-optimized
# TODO: add multi-threading support
# TODO: add support for continuous self-auditing
# TODO: Try heuristically calculating hashes non-lazily when they're likely to be needed later
# TODO: Try unrolling all this recursivity to improve performance

"""
memory: [block]
block: empty or branch or leaf

empty: next 4                                                     # 0 for end of the line

branch: active_child 4 balanced[size]                             # active_child 0 when there are none
balanced[n]: type 1 hash 32 hash 32 balanced[n-1] balanced[n-1]   # hashes can be EMPTY or INVALID
balanced[0]: type 1 hash 32 hash 32 block 4 pos 2 block 4 pos 2   # pos 0 means child is a branch
type: ONLY0 or ONLY1 or TERM0 or TERM1 or TERMBOTH or MIDDLE or NOTHING      # no singular, that's handled in root. NOTHING should be in all unallocated positions

leaf: first_unused 2 num_inputs 2 data                            # first_unused is a position in bytes in the current block
data: [only0 or only1 or term0 or term1 or bothterm or middle]    # there may be gaps between items
middle: MIDDLE 1 hash 32 pos 2 hash 32 pos 2
only0: ONLY0 1 hash 32 pos 2
only1: ONLY1 1 hash 32 pos 2
term0: TERM0 1 hash 32 hash 32 pos 2
term1: TERM1 1 hash 32 pos 2 hash 32
bothterm: TERMBOTH 1 hash 32 hash 32

inclusion_proof: [unit]        # EMPTY always has proofs of length 0
unit: only0 or only1 or term0 or term1 or bothterm or middle or singular
only0: ONLY0 1                 # never terminal
only1: ONLY1 1                 # never terminal
term0: TERM0 1 hash 32         # hash is of other side
term1: TERM1 1 hash 32         # hash is of other side
bothterm: TERMBOTH 1 hash 32   # always terminal
middle: MIDDLE 1 hash 32       # never terminal
singular: SINGULAR 1           # can only happen in the first position, terminal

exclusion_proof: [unit]                 # EMPTY always has proofs of length 0
unit: only0 or only1 or term0 or term1 or bothterm or middle or singular
only0: ONLY0 1 (hash 32)                # has a hash if different path and thus terminal
only1: ONLY1 1 (hash 32)                # has a hash if different path and thus terminal
term0: TERM0 1 hash 32 (hash 32)        # has a second hash if terminal
term1: TERM1 1 hash 32 (hash 32)        # has a second hash if terminal
bothterm: TERMBOTH 1 hash 32 hash 32    # always terminal
middle: MIDDLE 1 hash 32                # never terminal
singular: SINGULAR 1 hash 32            # can only happen in the first position, terminal
"""

EMPTY = bytes([0]) * 32
INVALID = bytes([255]) * 32
NOTHING = b'0x0'
MIDDLE = b'0x1'
ONLY0 = b'0x2'
ONLY1 = b'0x3'
TERM0 = b'0x4'
TERM1 = b'0x5'
TERMBOTH = b'0x6'
SINGULAR = b'0x7'

Maybe = 2

NOTSTARTED = 0
ONELEFT = 1
INVALIDATING = 2
DONE = 3

class IntegrityError(Exception):
    pass

def confirm_included(root, val, proof):
    assert len(root) == 32
    assert len(val) == 32
    if root == EMPTY:
        return False
    if proof == SINGULAR:
        return hasher(val) == root
    possible, newroot = self._confirm_included(_to_bits(val), 0, proof, 0, val)
    return possible and newroot == root

def _confirm_included(bits, depth, proof, pos, val):
    if depth > 220:
        raise IntegrityError("Impossibly deep proof")
    if len(proof) <= pos:
        return False, None
    t = proof[pos:pos + 1]
    if t == ONLY0:
        if bits[depth] == 0:
            p, v = self._confirm_included(bits, depth + 1, proof, pos + 1, val)
            if not p:
                return False, None
            return True, hasher(ONLY0 + v)
        else:
            return False, None
    elif t == ONLY1:
        if bits[depth] == 0:
            return False, None
        else:
            p, v = self._confirm_included(bits, depth + 1, proof, pos + 1, val)
            if not p:
                return False, None
            return True, hasher(ONLY1 + v)
    elif t == TERM0:
        if bits[depth] == 0:
            if len(proof) != pos + 1 + 32:
                return False, None
            return True, hasher(TERM0 + hasher(val) + proof[pos + 1:])
        else:
            if len(proof) < pos + 1 + 32:
                return False, None
            if _to_bits(proof[pos + 1:pos + 1 + 32])[:depth + 1] != bits[:depth] + [0]:
                return False, None
            v0 = hasher(proof[pos + 1:pos + 1 + 32])
            possible, v1 = _confirm_included(bits, depth + 1, proof, pos + 1 + 32, val)
            if not possible:
                return False, None
            return True, hasher(TERM0 + v0 + v1)
    elif t == TERM1:
        if bits[depth] == 0:
            if len(proof) < pos + 1 + 32:
                return False, None
            if _to_bits(proof[pos + 1:pos + 1 + 32])[:depth + 1] != bits[:depth] + [1]:
                return False, None
            v1 = hasher(proof[pos + 1:pos + 1 + 32])
            possible, v0 = _confirm_included(bits, depth + 1, proof, pos + 1 + 32, val)
            if not possible:
                return False, None
            return True, hasher(TERM1 + v0 + v1)
        else:
            if len(proof) != pos + 1 + 32:
                return False, None
            return True, hasher(TERM1 + proof[pos + 1:] + hasher(val))
    elif t == TERMBOTH:
        if len(proof) != pos + 1 + 32:
            return False, None
        if _to_bits(proof[pos + 1:pos + 1 + 32])[:depth + 1] != bits[:depth] + [1-bits[depth]]:
            return False, None
        if bits[depth] == 0:
            v0 = hasher(val)
            v1 = hasher(proof[pos + 1:pos + 1 + 32])
        else:
            v0 = hasher(proof[pos + 1:pos + 1 + 32])
            v1 = hasher(val)
        return True, hasher(TERMBOTH + v0 + v1)
    elif t == MIDDLE:
        if len(proof) < pos + 1 + 32:
            return False, None
        if bits[depth] == 0:
            v1 = proof[pos + 1:pos + 1 + 32]
            possible, v0 = _confirm_included(bits, depth + 1, proof, pos + 1 + 32, val)
        else:
            v0 = proof[pos + 1:pos + 1 + 32]
            possible, v1 = _confirm_included(bits, depth + 1, proof, pos + 1 + 32, val)
        if not possible:
            return False, None
        return True, hasher(MIDDLE + v0 + v1)
    else:
        return False, None

def confirm_not_included(root, val, proof):
    assert len(root) == 32
    assert len(val) == 32
    if root == EMPTY:
        return len(proof) == 0
    if len(proof) > 0 and proof[0:1] == SINGULAR:
        return len(proof) == 1 + 32 and proof[1:1 + 32] != val and hasher(proof[1:]) == root
    possible, newroot = self._confirm_not_included(_to_bits(val), 0, proof, 0, val)
    return possible and newroot == root

def _confirm_not_included(bits, depth, proof, pos, val):
    if depth > 220:
        raise IntegrityError("Impossibly deep proof")
    if len(proof) <= pos:
        return False, None
    t = proof[pos:pos + 1]
    if t == ONLY0:
        if bits[depth] == 0:
            p, v = self._confirm_included(bits, depth + 1, proof, pos + 1, val)
            if not p:
                return False, None
            return True, hasher(ONLY0 + v)
        else:
            if len(proof) != pos + 1 + 32:
                return False, None
            return True, hasher(ONLY0 + proof[pos + 1:pos + 1 + 32])
    elif t == ONLY1:
        if bits[depth] == 0:
            if len(proof) != pos + 1 + 32:
                return False, None
            return True, hasher(ONLY1 + proof[pos + 1:pos + 1 + 32])
        else:
            p, v = self._confirm_included(bits, depth + 1, proof, pos + 1, val)
            if not p:
                return False, None
            return True, hasher(ONLY1 + v)
    elif t == TERM0:
        if bits[depth] == 0:
            if len(proof) != pos + 1 + 64:
                return False, None
            if proof[pos + 1 + 32:] == val:
                return False, None
            if _to_bits(proof[pos + 1:pos + 1 + 32])[:depth + 1] != bits[:depth + 1]:
                return False, None
            return True, hasher(TERM0 + hasher(proof[pos + 1:pos + 1 + 32]) + proof[pos + 1 + 32:])
        else:
            if len(proof) < pos + 1 + 32:
                return False, None
            if _to_bits(proof[pos + 1:pos + 1 + 32])[:depth + 1] != bits[:depth] + [0]:
                return False, None
            v0 = hasher(proof[pos + 1:pos + 1 + 32])
            possible, v1 = _confirm_not_included(bits, depth + 1, proof, pos + 1 + 32, val)
            if not possible:
                return False, None
            return True, hasher(TERM0 + v0 + v1)
    elif t == TERM1:
        if bits[depth] == 0:
            if len(proof) < pos + 1 + 32:
                return False, None
            if _to_bits(proof[pos + 1:pos + 1 + 32])[:depth + 1] != bits[:depth] + [1]:
                return False, None
            v1 = hasher(proof[pos + 1:pos + 1 + 32])
            possible, v0 = _confirm_not_included(bits, depth + 1, proof, pos + 1 + 32, val)
            if not possible:
                return False, None
            return True, hasher(TERM1 + v0 + v1)
        else:
            if len(proof) != pos + 1 + 64:
                return False, None
            if proof[pos + 1 + 32:] == val:
                return False, None
            if _to_bits(proof[pos + 1:pos + 1 + 32])[:depth + 1] != bits[:depth + 1]:
                return False, None
            return True, hasher(TERM1 + proof[pos + 1:pos + 1 + 32] + hasher(proof[pos + 1 + 32:]))
    elif t == TERMBOTH:
        if len(proof) != pos + 1 + 64:
            return False, None
        if bits[depth] == 0:
            if proof[pos + 1:pos + 1 + 32] == val:
                return False, None
        else:
            if proof[pos + 1 + 32:pos + 1 + 64] == val:
                return False, None
        if _to_bits(proof[pos + 1:pos + 1 + 32])[:depth + 1] != bits[:depth] + [0]:
            return False, None
        if _to_bits(proof[pos + 1:pos + 1 + 32])[:depth + 1] != bits[:depth] + [1]:
            return False, None
        v0 = hasher(proof[pos + 1:pos + 1 + 32])
        v1 = hasher(proof[pos + 1 + 32:pos + 1 + 64])
        return True, hasher(TERMBOTH + v0 + v1)
    elif t == MIDDLE:
        if len(proof) < pos + 1 + 32:
            return False, None
        if bits[depth] == 0:
            v1 = proof[pos + 1:pos + 1 + 32]
            possible, v0 = _confirm_included(bits, depth + 1, proof, pos + 1 + 32, val)
        else:
            v0 = proof[pos + 1:pos + 1 + 32]
            possible, v1 = _confirm_included(bits, depth + 1, proof, pos + 1 + 32, val)
        if not possible:
            return False, None
        return True, hasher(MIDDLE + v0 + v1)
    else:
        return False, None

def _to_bits(mystring):
    r = []
    for val in mystring[-1, -1, -1]:
        for i in range(8):
            r.append(val & 1)
            val >>= 1
    r.reverse()
    return r

class MerkleSet:
    def __init__(self, size, depth):
        self.root = EMPTY
        self.size = 0
        self.subblock_lengths = [12]
        while len(subblock_lengths) < depth:
            self.subblock_lengths.append(65 + 2 * self.subblock_lengths[-1])
        self.block_size = self.subblock_lengths[-1] + 4
        numblocks = size // self.block_size
        self.memory = bytearray(numblocks * self.block_size)
        for i in range(1, self.numblocks - 1):
            pos = self.block_size * i
            self.memory[pos:pos + 4] = (i+1).to_bytes(4)
        self.first_unused = 1

    def get_root(self):
        if self.size == 0:
            return EMPTY
        if self.size == 1:
            return hasher(self.root)
        if self.root == INVALID:
            self.root = self._force_calculation(5, 0, len(self.subblock_lengths)-1)
        return self.root

    def get_size(self):
        return self.size

    def _force_calculation(self, pos, depth, moddepth):
        if moddepth == 0:
            block = from_bytes(self.memory[pos:pos + 4])
            pos = from_bytes(self.memory[pos + 4:pos + 6])
            if pos == 0:
                return self._force_calculation(self.block_size * block + 4, depth, len(self.subblock_lengths))
            else:
                return self._force_calculation_leaf(self.block_size * block, pos, depth)
        def check0():
            if self.memory[pos + 1:pos + 1 + 32] == INVALID:
                self.memory[pos + 1:pos + 1 + 32] = self._force_calculation(pos + 65, depth + 1, moddepth - 1)
        def check1():
            if self.memory[pos + 1 + 32:pos + 1 + 64] == INVALID:
                self.memory[pos + 1 + 32:pos + 1 + 64] = self._force_calculation(pos + 65 + self.subblock_lengths[moddepth - 1], moddepth - 1)
        t = self.memory[pos:pos + 1]
        if t == MIDDLE:
            check0()
            check1()
            return hasher(self.memory[pos:pos + 65])
        elif t == ONLY0:
            check0()
            return hasher(ONLY0 + self.memory[pos + 1: pos + 1 + 32])
        elif t == ONLY1:
            check1()
            return hasher(ONLY1 + self.memory[pos + 1 + 32:pos + 1 + 64])
        elif t == TERM0:
            check1()
            return hasher(TERM0 + hasher(self.memory[pos + 1:pos + 1 + 32]) + self.memory[pos + 1 + 32:pos + 1 + 64])
        elif t == TERM1:
            check0()
            return hasher(TERM1 + self.memory[pos + 1:pos + 1 + 32] + hasher(self.memory[pos + 1 + 32:pos + 1 + 64]))
        elif t == TERMBOTH:
            return hasher(TERM0 + hasher(self.memory[pos + 1:pos + 1 + 32]) + hasher(self.memory[pos + 1 + 32:pos + 1 + 64]))
        else:
            raise IntegrityError('Invalid node type')

    def _force_calculation_leaf(self, blockbegin, pos, depth):
        p = blockbegin + pos
        t = self.memory[p]
        def check_single(mypos):
            if self.memory[mypos:mypos + 32] == INVALID:
                self.memory[mypos:mypos + 32] = self._force_calculation_leaf(blockbegin, from_bytes(self.memory[mypos + 32:mypos + 32 + 2]), depth + 1)
        if t == MIDDLE:
            check_single(p + 1)
            check_single(p + 1 + 32 + 2)
            return hasher(self.memory[p:p + 65])
        elif t == ONLY0 or t == ONLY1:
            check_single(p + 1)
            return hasher(self.memory[p:p + 33])
        elif t == TERM0:
            check_single(p + 1 + 32)
            return hasher(TERM0 + hasher(self.memory[p + 1:p + 1 + 32]) + self.memory[p + 1 + 32:p + 1 + 64])
        elif t == TERM1:
            check_single(p + 1)
            return hasher(TERM1 + self.memory[p + 1:p + 1 + 32] + hasher(self.memory[p + 1 + 32 + 2:p + 1 + 32 + 2 + 32]))
        elif t == TERMBOTH:
            return hasher(TERMBOTH + hasher(self.memory[p + 1:p + 1 + 32]) + hasher(self.memory[p + 1 + 32:p + 1 + 64]))
        else:
            raise IntegrityError('Invalid node type in leaf')

    def add(self, toadd):
        return self.add_already_hashed(hasher(toadd))

    def add_already_hashed(self, toadd):
        assert len(toadd) == 32
        if self.size == 0:
            self.root = toadd
            self.size = 1
        elif self.size == 1:
            self._add_branch_two(self.root, toadd, 0, 4, 0, len(self.subblock_lengths) - 1)
            self.root = INVALID
        else:
            if self._add_branch_one(toadd, _to_bits(toadd), 0, 4, 0, len(self.subblock_lengths) - 1) == INVALIDATING:
                self.root = INVALID

    # returns NOTSTARTED, INVALIDATING, DONE
    def _add_branch_one(self, toadd, toadd_bits, block, pos, depth, moddepth):
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
                r = self._add_branch_two(self.memory[pos + 1:pos + 1 + 32], toadd, toadd_bits, block, pos + 1 + 64, depth + 1, moddepth - 1)
                if r == DONE:
                    return DONE
                else:
                    assert r == INVALIDATING:
                    self.memory[pos:pos + 1] = MIDDLE
                    self.memory[pos + 1:pos + 1 + 32] = INVALID
                    return INVALIDATING
            elif t == TERMBOTH:
                r = self._add_branch_two(self.memory[pos + 1:pos + 1 + 32], toadd, toadd_bits, block, pos + 1 + 64, depth + 1, moddepth - 1)
                if r == DONE:
                    return DONE
                else:
                    assert r == INVALIDATING:
                    self.memory[pos:pos + 1] = TERM1
                    self.memory[pos + 1:pos + 1 + 32] = INVALID
                    return INVALIDATING
            else:
                raise IntegrityError()
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
                r = self._add_branch_two(self.memory[pos + 1 + 32:pos + 1 + 64], toadd, toadd_bits, block, pos + 1 + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                if r == DONE:
                    return DONE
                else:
                    assert r == INVALIDATING:
                    self.memory[pos:pos + 1] = MIDDLE
                    self.memory[pos + 1 + 32:pos + 1 + 64] = INVALID
                    return INVALIDATING
            elif t == TERMBOTH:
                r = self._add_branch_two(self.memory[pos + 1 + 32:pos + 1 + 64], toadd, toadd_bits, block, pos + 1 + 64 + self.subblock_lengths[moddepth - 1], depth + 1, moddepth - 1)
                if r == DONE:
                    return DONE
                else:
                    assert r == INVALIDATING:
                    self.memory[pos:pos + 1] = TERM0
                    self.memory[pos + 1 + 32:pos + 1 + 64] = INVALID
                    return INVALIDATING
            else:
                raise IntegrityError()

    # returns INVALIDATING, DONE
    def _add_branch_two(self, old, toadd, toadd_bits, block, pos, depth, moddepth):
        booga booga

    # returns state, newpos
    # state can be INVALIDATING, DONE
    def _add_leaf_one(self, toadd, toadd_bits, oldblock, blockbegin, pos, depth):
        booga booga

    # returns state, newpos
    # state can be INVALIDATING, DONE
    def _add_leaf_two(self, oldval, toadd, toadd_bits, oldblock, blockbegin, pos, depth):
        booga booga

    def remove(self, toremove):
        return self.remove_already_hashed(hasher(toadd))

    def remove_already_hashed(self, toremove):
        assert len(toremove) == 32
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
        else:
            assert False

    # returns (status, oneval)
    # status can be NOTSTARTED, ONELEFT, INVALIDATING, DONE
    def _remove_branch(self, toremove, toremove_bits, pos, depth, moddepth):
        if moddepth == 0:
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
    def _remove_outside_leaf(self, toremove, toremove_bits, pos, depth):
        block = from_bytes(self.memory[pos:pos + 4])
        pos = from_bytes(self.memory[pos + 4:pos + 6])
        if pos == 0:
            state, oneval = self._remove_branch(toremove, toremove_bits, block * self.block_size + 4, depth, len(self.subblock_lengths) - 1)
            if state == DONE:
                return DONE, None
            elif state == INVALIDATING:
                return state, oneval
            elif state == ONELEFT:
                self.memory[pos:pos + 6] = bytes(6)
                self.memory[block + self.block_size:(block + 1) * self.block_size] = bytes(blocksize)
                self.memory[block * self.blocksize:block * self.block_size + 4] = to_bytes(self.first_unused)
                self.first_unused = block
                return state, oneval
            else:
                raise IntegrityError()
        else:
            block_begin = block * self.block_size
            state, oneval = self._remove_leaf(toremove, block_begin, pos, depth)
            if state == DONE:
                return DONE, None
            if state == INVALIDATING:
                return INVALIDATING, None
            if state == ONELEFT:
                num_inputs = from_bytes(self.memory[block_begin + 2:blockbegin + 4])
                if numinputs == 1:
                    first_unused = from_bytes(self.memory[block_begin:block_begin + 2])
                    self.memory[block_begin:block_begin + first_unused] = bytes(first_unused)
                    self.memory[block_begin:block_begin + 4] = to_bytes(self.first_unused)
                    self.first_unused = block
                else:
                    self.memory[block_begin + 2:block_begin + 4] = to_bytes(numinputs - 1)
                self.memory[pos:pos + 6] = bytes(6)
                return ONELEFT, oneval
            else:
                raise IntegrityError()

    # returns (status, oneval)
    # status can be ONELEFT, INVALIDATING, DONE
    def _remove_leaf(self. toremove, toremove_bits, blockbegin, pos, depth):
        oldpos = pos
        pos += blockbegin
        t = self.memory[pos:pos + 1]
        if t == MIDDLE:
            if toremove_bits[depth] == 0:
                state, oneval = self._remove_leaf(toremove, toremove_bits, blockbegin, from_bytes(self.memory[pos + 1 + 32:pos + 1 + 32 + 2]), depth + 1)
                if state == DONE:
                    return DONE, None
                elif state == INVALIDATING:
                    if self.memory[pos + 1:pos + 1 + 32] == INVALID:
                        return DONE, None
                    else:
                        self.memory[pos + 1:pos + 1 + 32] = INVALID
                        return INVALIDATING, None
                elif state == ONELEFT:
                    self.memory[pos:pos + 1] = TERM0
                    self.memory[pos + 1:pos + 1 + 32] = oneval
                    self.memory[pos + 1 + 32:pos + 1 + 64 + 2] = self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32 + 2]
                    return INVALIDATING, None
                else:
                    raise IntegrityError()
            else:
                state, oneval = self._remove_leaf(toremove, toremove_bits, blockbegin, from_bytes(self.memory[pos + 1 + 32 + 2 + 32:pos + 1 + 32 + 2 + 32 + 2]), depth + 1)
                if state == DONE:
                    return DONE, None
                elif state == INVALIDATING:
                    if self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32] == INVALID:
                        return DONE, None
                    else:
                        self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32] = INVALID
                        return INVALIDATING, None
                elif state == ONELEFT:
                    self.memory[pos:pos + 1] = TERM1
                    self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32] = INVALID
                    return INVALIDATING, None
                else:
                    raise IntegrityError()
        elif t == ONLY0:
            if toremove_bits[depth] == 0:
                state, oneval = self._remove_leaf(toremove, toremove_bits, blockbegin, from_bytes(self.memory[pos + 1 + 32:pos + 1 + 32 + 2]) , depth + 1)
                if state == DONE:
                    return DONE, None
                elif state == INVALIDATING:
                    if self.memory[pos + 1:pos + 1 + 32] == INVALID:
                        return DONE, None
                    else:
                        self.memory[pos + 1:pos + 1 + 32] = INVALID
                        return INVALIDATING, None
                elif state == ONELEFT:
                    return ONELEFT, oneval
                else:
                    raise IntegrityError()
            else:
                return DONE, None
        elif t == ONLY1:
            if toremove_bits[depth] == 0:
                return DONE, None
            else:
                state, oneval = self._remove_leaf(toremove, toremove_bits, blockbegin, from_bytes(self.memory[pos + 1 + 32:pos + 1 + 32 + 2]), depth + 1)
                if state == DONE:
                    return DONE, None
                elif state == INVALIDATING:
                    if self.memory[pos + 1:pos + 1 + 32] == INVALID:
                        return DONE, None
                    else:
                        self.memory[pos + 1:pos + 1 + 32] = INVALID
                        return INVALIDATING, None
                elif state == ONELEFT:
                    return ONELEFT, oneval
                else:
                    raise IntegrityError()
        elif t == TERM0:
            if toremove_bits[depth] == 0:
                if self.memory[pos + 1:pos + 1 + 32] != toremove:
                    return DONE, None
                self.size -= 1
                self.memory[0] = ONLY1
                self.memory[pos + 1:pos + 1 + 32 + 2] = self.memory[pos + 1 + 32:pos + 1 + 32 + 32 + 2]
                return INVALIDATING, None
            else:
                state, oneval = self._remove_leaf(toremove, toremove_bits, blockbegin, from_bytes(self.memory[pos + 1 + 64:pos + 1 + 64 + 2]), depth + 1)
                if state == DONE:
                    return DONE, None
                elif state == INVALIDATING:
                    if self.memory[pos + 1 + 32:pos + 1 + 64] == INVALID:
                        return DONE, None
                    else:
                        self.memory[pos + 1 + 32:pos + 1 + 64] = INVALID
                        return INVALIDATING, None
                elif state == ONELEFT:
                    self.memory[pos:pos + 1] = TERMBOTH
                    self.memory[pos + 1 + 32:pos + 1 + 64] = oneval
                    return INVALIDATING, None
                else:
                    raise IntegrityError()
        elif t == TERM1:
            if toremove_bits[depth] == 0:
                state, oneval = self._remove_leaf(toremove, toremove_bits, blockbegin, from_bytes(self.memory[pos + 1 + 32:pos + 1 + 32 + 2]), depth + 1)
                if state == DONE:
                    return DONE, None
                elif state == INVALIDATING:
                    if self.memory[pos + 1:pos + 1 + 32] == INVALID:
                        return DONE, None
                    else:
                        self.memory[pos + 1:pos + 1 + 32] = INVALID
                        return INVALIDATING, None
                elif state == ONELEFT:
                    self.memory[pos:pos + 1] = TERMBOTH
                    self.memory[pos + 1:pos + 1 + 32] = oneval
                    self.memory[pos + 1 + 32:pos + 1 + 64] = self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32]
                    return INVALIDATING, None
                else:
                    raise IntegrityError()
            else:
                if self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32] != toremove:
                    return DONE, None
                self.size -= 1
                self.memory[pos] = ONLY0
                return INVALIDATING, None
        elif t == TERMBOTH:
            if toremove_bits[depth] == 0:
                if self.memory[pos + 1:pos + 1 + 32] != toremove:
                    return DONE, None
                self.size -= 1
                return ONELEFT, self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32], oldpos
            else:
                if self.memory[pos + 1 + 32:pos + 1 + 32 + 2 + 32] != toremove:
                    return DONE, None
                self.size -= 1
                return ONELEFT, self.memory[pos + 1:pos + 1 + 32]
        else:
            raise IntegrityError()

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
                updates.append((toremove[removepos], 0))
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
        assert len(mystr) == 32
        return self._is_included(tocheck, None)

    def is_included_make_proof(self, tocheck):
        return self.is_included_make_proof_already_hashed(hasher(tocheck))

    def is_included_make_proof_already_hashed(self, tocheck):
        assert len(tocheck) == 32
        buf = _bytesio()
        r = return self._is_included(tocheck, buf)
        return r, buf.get()

    def _is_included_outer(self, tocheck, buf):
        self.get_root()
        if self.size == 0:
            return False
        if self.size == 1:
            if buf is not None:
                buf.add(SINGULAR)
            if tocheck == self.root:
                return True
            else:
                if buf is not None:
                    buf.add(self.root)
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
                buf.add(x)
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
        pos += block_base
        def child(p):
            return self._is_included_leaf(tocheck, tocheck_bits, block_base, from_bytes(self.memory[pos + p:pos + p + 2]), depth + 1, buf)
        def b(a, b):
            if buf:
                buf.add(self.memory[pos + a:pos + a + b])
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

class _bytesio:
    def __init__(self):
        self.buf = bytearray(33 * 256)
        self.end = 0

    def add(self, b):
        self.buf[self.end:self.end + len(b)] = b
        self.end += len(b)

    def get(self):
        return self.buf[:self.end]


