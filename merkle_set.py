from hashlib import sha256

def hasher(mystr):
    return sha256(mystr).digest()

"""
memory: [block]
block: empty or branch or leaf

empty: next 4                                                     # 0 for end of the line

branch: active_child 4 balanced[size]                             # active_child 0 when there are none
balanced[n]: type 1 hash 32 hash 32 balanced[n-1] balanced[n-1]   # hashes can be EMPTY or INVALID
balanced[0]: type 1 hash 32 hash 32 block 4 pos 2 block 4 pos 2   # pos 0 means child is a branch
type: ONLY0 or ONLY1 or TERM0 or TERM1 or TERMBOTH or MIDDLE      # no singular, that's handled in root

leaf: first_unused 2 num_inputs 2 data                            # first_unused is a position in bytes in the current block
data: [only0 or only1 or term0 or term1 or bothterm or middle]    # there may be gaps between items
middle: MIDDLE 1 hash 32 pos 2 hash 32 pos 2
only0: ONLY0 1 hash 32 pos 2
only1: ONLY1 1 hash 32 pos 2
term0: TERM0 1 hash 32 hash 32 pos 2
term1: TERM1 1 hash 32 pos 2 hash 32
bothterm: TERMBOTH 1 hash 32 hash 32

inclusion_proof: [unit]        # EMPTY always has proofs of length 0
unit: ONLY0 or ONLY1 or term0 or term1 or bothterm or middle or singular
ONLY0: ONLY0 1                 # never terminal
ONLY1: ONLY1 1                 # never terminal
term0: TERM0 1 hash 32         # hash is of other side
term1: TERM1 1 hash 32         # hash is of other side
bothterm: TERMBOTH 1 hash 32   # always terminal
middle: MIDDLE 1 hash 32       # never terminal
singular: SINGULAR 1           # can only happen in the first position, terminal

exclusion_proof: [unit]                 # EMPTY always has proofs of length 0
unit: ONLY0 or ONLY1 or term0 or term1 or bothterm or middle or singular
ONLY0: ONLY0 1 (hash 32)                # has a hash if different path and thus terminal
ONLY1: ONLY1 1 (hash 32)                # has a hash if different path and thus terminal
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

class IntegrityError(Exception):
    pass

def confirm_included(root, val, proof):
    assert len(root) == 32
    assert len(val) == 32
    if root == EMPTY:
        return False
    if proof == SINGULAR:
        return hasher(SINGULAR + val) == root
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
        return len(proof) == 1 + 32 and proof[1:1 + 32] != val and hasher(proof) == root
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
        self.current_size = 0
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
        if self.current_size == 0:
            return EMPTY
        if self.current_size == 1:
            return hasher(SINGULAR + self.root)
        if self.root == INVALID:
            self.root = self._force_calculation(5, 0, len(self.subblock_lengths)-1)
        return self.root

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
        raise NotImplementedError("booga booga")

    def remove(self, toremove):
        return self.remove_already_hashed(hasher(toadd))

    def remove_already_hashed(self, toremove):
        assert len(toremove) == 32
        raise NotImplementedError("booga booga")

    def batch_add_and_remove(self, toadd, toremove):
        self.batch_add_and_remove_already_hashed({hasher(x) for x in toadd}, {hasher(x) for x in toremove})

    def batch_add_and_remove_already_hashed(self, toadd, toremove):
        tadd = set(toadd)
        toremove = set(toremove)
        both = toadd.intersection(toremove)
        toadd.difference_remove(both)
        toremove.difference_remove(both)
        updates = [(x, 0) for x in toadd] + [(x, 1) for x in toremove]
        updates.sort()
        for val, type in updates:
            if type == 0:
                self.add_already_hashed(val)
            else:
                self.remove_already_hashed(val)

    def are_any_included(self, tocheck):
        return self.are_any_included_already_hashed([hasher(x) for x in tochecks])

    def are_any_included_already_hashed(self, tocheck):
        for t in sorted(tocheck):
            if self.is_included(t):
                return True
        return False

    def are_all_included(self, tocheck):
        return self.are_all_included_already_hashed([hasher(x) for x in tochecks])

    def are_all_included_already_hashed(self, tocheck):
        for t in sorted(tocheck):
            if not t.is_included:
                return False
        return True

    def is_included(self, tocheck):
        return self.is_included_already_hashed(hasher(tocheck))

    def is_included_already_hashed(self, tocheck):
        assert len(mystr) == 32
        return self._is_included(tocheck, _to_bits(tocheck), 5, 0, len(self.subblock_lengths)-1, None)

    def _is_included(self, tocheck, tocheck_bits, pos, depth, moddepth):
        newpos = pos + 65
        if tocheck_bits[depth] == 1:
            newpos += self.subblock_lengths[moddepth - 1]
        def check_block():
            if moddepth != 1:
                raise IntegrityError()
            bnum = from_bytes(self.memory[newpos:newpos + 4])
            bpos = from_bytes(self.memory[newpos + 4:newpos + 6])
            if bpos == 0:
                return self._is_included(tocheck, tocheck_bits, bnum * self.block_size + 4, depth + 1, len(self.subblock_lengths))
            else:
                return self._is_included_leaf(tocheck, tocheck_bits, bnum * self.block_size, bpos, depth + 1)
        if moddepth > 1:
            val = self._is_included(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1)
            if val != Maybe:
                return val
        t = self.memory[pos:pos + 1]
        if t == NOTHING:
            return Maybe
        elif t == MIDDLE:
            return check_block()
        elif t == ONLY0:
            if tocheck_bits[depth] == 0:
                return check_block()
            else:
                return False
        elif t == ONLY1:
            if tocheck_bits[depth] == 0:
                return False
            else:
                return check_block()
        elif t == TERM0:
            if tocheck_bits[depth] == 0:
                return self.memory[pos + 1:pos + 1 + 32] == tocheck
            else:
                return check_block()
        elif t == TERM1:
            if tocheck_bits[depth] == 0:
                return check_block()
            else:
                return self.memory[pos + 1 + 32:pos + 1 + 64] == tocheck
        elif t == TERMBOTH:
            if tocheck_bits[depth] == 0:
                return self.memory[pos + 1:pos + 1 + 32] == tocheck
            else:
                return self.memory[pos + 1 + 32:pos + 1 + 64] == tocheck
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

    def is_included_make_proof(self, tocheck):
        return is_included_make_proof_already_hashed(hasher(tocheck))

    def is_included_make_proof_already_hashed(self, tocheck):
        assert len(mystr) == 32
        self.get_root()
        buf = _bytesio()
        if self.current_size == 0:
            return False, b''
        if self.current_size == 1:
            if tocheck == self.root:
                return True, SINGULAR
            else:
                return False, SINGULAR + self.root
        r = self._is_included_make_proof(tocheck, _to_bits(tocheck), 5, 0, len(self.subblock_lengths)-1, None, buf)
        return r, buf.get()

    def _is_included_make_proof(self, tocheck, tocheck_bits, pos, depth, moddepth, buf):
        if moddepth == 0:
            bnum = from_bytes(self.memory[pos:pos + 4])
            bpos = from_bytes(self.memory[pos + 4:pos + 6])
            if bpos == 0:
                return self._is_included_make_proof(tocheck, tocheck_bits, bnum * self.block_size + 4, depth, len(self.subblock_lengths), buf)
            else:
                return self._is_included_leaf(tocheck, tocheck_bits, bnum * self.block_size, bpos, depth, buf)
        newpos = pos + 65
        if tocheck_bits[depth] == 1:
            newpos += self.subblock_lengths[moddepth - 1]
        t = self.memory[pos:pos + 1]
        buf.add(t)
        if t == MIDDLE:
            if tocheck_bits[depth] == 1:
                buf.add(self.memory[pos + 1:pos + 1 + 32])
            else:
                buf.add(self.memory[pos + 1 + 32:pos + 1 + 64])
            return self._is_included_make_proof(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
        elif t == ONLY0:
            if tocheck_bits[depth] == 0:
                return self._is_included_make_proof(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
            else:
                buf.add(self.memory[pos + 1:pos + 1 + 32])
                return False
        elif t == ONLY1:
            if tocheck_bits[depth] == 0:
                buf.add(self.memory[pos + 1:pos + 1 + 32])
                return False
            else:
                return self._is_included_make_proof(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
        elif t == TERM0:
            if tocheck_bits[depth] == 0:
                if self.memory[pos + 1:pos + 1 + 32] == tocheck:
                    buf.add(self.memory[pos + 1 + 32:pos + 1 + 64])
                    return True
                else:
                    buf.add(self.memory[pos + 1:pos + 1 + 64])
                    return False
            else:
                buf.add(self.memory[pos + 1:pos + 1 + 32])
                return self._is_included_make_proof(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
        elif t == TERM1:
            if tocheck_bits[depth] == 0:
                buf.add(self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32])
                return self._is_included_make_proof(tocheck, tocheck_bits, newpos, depth + 1, moddepth - 1, buf)
            else:
                if self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32] == tocheck:
                    buf.add(self.memory[pos + 1:pos + 1 + 32])
                    return True
                else:
                    buf.add(self.memory[pos + 1:pos + 1 + 32])
                    buf.add(self.memory[pos + 1 + 32 + 2:pos + 1 + 32 + 2 + 32])
                    return False
        elif t == TERMBOTH:
            if tocheck_bits[depth] == 0:
                if self.memory[pos + 1:pos + 1 + 32] == tocheck:
                    buf.add(self.memory[pos + 1 + 32:pos + 1 + 64])
                    return True
                else:
                    buf.add(self.memory[pos + 1:pos + 1 + 64])
                    return False
            else:
                if self.memory[pos + 1 + 32:pos + 1 + 64] == tocheck:
                    buf.add(self.memory[pos + 1:pos + 1 + 32])
                    return True
                else:
                    buf.add(self.memory[pos + 1:pos + 1 + 64])
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


