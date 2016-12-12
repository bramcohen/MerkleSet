from hashlib import sha256
from blake2 import blake2s
from binascii import b2a_hex

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
INVALIDATING = 4
DONE = 5
FULL = 6

ERROR = bytearray([1] * 32)
BLANK = bytearray([0] * 32)

def shahash(mystr):
    return flip_terminal(sha256(mystr).digest())

def flip_terminal(mystr):
    assert len(mystr) == 32
    r = bytearray(mystr)
    r[0] = TERMINAL | (r[0] & 0x3F)
    return r

def hasher(mystr):
    assert len(mystr) == 64
    r = bytearray(b2a_hex(blake2s(mystr, 32)))
    r[0] = MIDDLE | (r[0] & 0x3F)
    return r

def get_type(mybytes, pos):
    return mybytes[pos] & INVALID

def make_invalid(mybytes, pos):
    mybytes[pos] |= INVALID

def get_bit(mybytes, pos):
    return (mybytes[-(pos // 8) - 1] >> (pos % 8)) & 1

def confirm_included(root, val, proof):
    return _confirm_included(root, shahash(val), proof)

def confirm_included_already_hashed(root, val, proof):
    return _confirm_included(root, flip_terminal(val), proof)

def _confirm_included(root, val, proof):
    assert len(root) == 32
    root = bytearray(root)
    a = get_type(root, 0)
    if a == TERMINAL:
        if len(proof) != 0:
            return False
        return root == val
    elif a == MIDDLE:
        return root == _find_implied_root_inclusion(0, proof, val)
    else:
        return False

def _find_implied_root_inclusion(depth, proof, val):
    if depth > 220:
        return ERROR
    if len(proof) == 0:
        return ERROR
    t = ord(proof[0])
    if t == GIVE0:
        if get_bit(val, depth) == 0 or len(pos) < 33:
            return ERROR
        if len(pos) == 33:
            return hasher(proof[1:] + val)
        return hasher((proof[1:] + self._find_implied_root_inclusion(depth + 1, proof[33:], val))
    elif t == GIVE1:
        if get_bit(val, depth) == 1 or len(pos) < 33:
            return ERROR
        if len(pos) == 33:
            return hasher(val + proof[1:])
        return hasher((self._find_implied_root_inclusion(depth + 1, proof[33:], val) + proof[1:])
    elif t == EMPTY0:
        if get_bit(val, depth) == 0:
            return ERROR
        return hasher(BLANK + self._find_implied_root_inclusion(depth + 1, proof[1:], val))
    elif t == EMPTY1:
        if get_bit(val, depth) == 1:
            return ERROR
        return hasher(self._find_implied_root_inclusion(depth + 1, proof[1:], val) + BLANK)
    else:
        return ERROR

def confirm_not_included(root, val, proof):
    return _confirm_included(root, shahash(val), proof)

def confirm_not_included_already_hashed(root, val, proof):
    return _confirm_included(root, flip_terminal(val), proof)

def _confirm_not_included(root, val, proof):
    assert len(root) == 32 and len(val) == 32
    root = bytearray(root)
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
        return root == _find_implied_root_exclusion(0, proof, val)
    else:
        return False

def _find_implied_root_exclusion(depth, proof, val):
    if depth > 220:
        return ERROR
    if len(proof) == 0:
        return ERROR
    t = ord(proof[0])
    if t == GIVE0:
        if get_bit(val, depth) == 0 or len(pos) < 33:
            return ERROR
        return hasher((proof[1:] + self._find_implied_root_exclusion(depth + 1, proof[33:], val))
    elif t == GIVE1:
        if get_bit(val, depth) == 1 or len(pos) < 33:
            return ERROR
        return hasher((self._find_implied_root_exclusion(depth + 1, proof[33:], val) + proof[1:])
    elif t == GIVEBOTH:
        if len(proof) != 65:
            return ERROR
        if val == proof[1:33] or val == proof[33:]:
            return ERROR
        return hasher(proof[1:])
    elif t == GIVE0EMPTY1:
        if get_bit(val, depth) != 1 or len(proof) != 33:
            return ERROR
        return hasher(proof[1:] + BLANK)
    elif t == GIVE1EMPTY0:
        if get_bit(val, depth) != 0 or len(proof) != 33:
            return ERROR
        return hasher(BLANK + proof[1:])
    elif t == EMPTY0:
        if get_bit(val, depth) == 0:
            if len(proof) != 33:
                return ERROR
            return hasher(BLANK + proof[1:])
        else:
            return hasher(BLANK + self._find_implied_root_exclusion(depth + 1, proof[1:], val))
    elif t == EMPTY1:
        if get_bit(val, depth) == 1:
            if len(proof) != 33:
                return ERROR
            return hasher(proof[1:] + BLANK)
        else:
            return hasher(self._find_implied_root_inclusion(depth + 1, proof[1:], val) + BLANK)
    else:
        return ERROR

class MerkleSet:
    def __init__(self, depth, leaf_units):
        self.subblock_lengths = [10]
        while len(subblock_lengths) <= depth:
            self.subblock_lengths.append(64 + 2 * self.subblock_lengths[-1])
        self.leaf_units = leaf_units
        self.root = BLANK
        # should be dumped completely on a port to C in favor of real dereferencing.
        self.pointers_to_arrays = {}
        self.rootblock = None

    def _allocate_branch(self):
        b = bytearray(8 + self.subblock_lengths[-1])
        self.pointers_to_arrays[self._deref(branch)] = b
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
        return self._add(shahash(toadd))

    def add_already_hashed(self, toadd):
        return self._add(flip_terminal(toadd))

    def _add(self, toadd):
        t = get_type(self.root, 0)
        if t == EMPTY:
            self.root = toadd
        elif t == TERMINAL:
            self.rootblock = self._allocate_branch()
            self._insert_branch([self.root, toadd], self.rootblock, 8, 0, len(self.subblock_lengths) - 1)
            make_invalid(self.root, 0)
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
            r = self._add_branch_inner(toadd, block, pos + 64, moddepth - 1)
            if r == INVALIDATING:
                if get_type(block, pos) != INVALID:
                    make_invalid(block, pos)
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
                return INVALIDATING
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
            return INVALIDATING
        else:
            r = self._add_branch_inner(toadd, block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
            if r == INVALIDATING:
                if get_type(block, pos + 32) != INVALID:
                    make_invalid(block, pos + 32)
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
                return INVALIDATING
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
            return INVALIDATING

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
                self._insert_branch(things, block, pos + 64 + self.subblock_lengths[moddepth - 1], moddepth - 1)
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
    def _add_to_leaf(self, toadd, branch, branchpos, leaf, pos, depth):
        call _add_to_leaf_inner
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
                result = self._insert_leaf(toadd and other value):
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
                result = self._insert_leaf(toadd and other value):
                if result != FULL:
                    increase size by 1
            if not invalid and result == INVALIDATING:
                mark invalid
            return result

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

    def _delete_section_from_leaf(self, leaf, pos):
        if there is anything below in high bit:
            self._delete_section_from_leaf(high bit area)
        if there is anything below in low bit:
            self._delete_section_from_leaf(low bit area)
        make pos cell point to firstpos
        reset firstpos to pos

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

    # returns (INVALIDATING, FULL), pos
    def _insert_leaf(self, things, leaf, depth):
        pos = from_bytes(leaf[:2])
        if pos == 0xFFFF:
            return FULL, None
        lpos = pos * 68 + 4
        nextpos = from_bytes(leaf[lpos:lpos + 2])
        leaf[:2] = to_bytes(nextpos, 2)
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
        return self._remove(shahash(toremove))

    def remove_already_hashed(self, toremove):
        return self._remove(flip_terminal(toremove))

    def _remove(self, toremove):
        t = get_type(self.root)
        if t == EMPTY:
            return
        elif t == TERMINAL:
            if toremove == self.root:
                self.root = BLANK
        else:
        status, oneval = self._remove_branch(toremove, 4, 0, len(self.subblock_lengths))
        if status == INVALIDATING:
            make_invalid(self.root, 0)
        elif status == ONELEFT:
            self.root = oneval

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

    def batch_add_and_remove(self, toadd, toremove):
        self._batch_add_and_remove([shahash(x) for x in toadd], [shahash(x) for x in toremove])

    def batch_add_and_remove(self, toadd, toremove):
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
        while addpos < len(toadd):
            self._add(toadd[addpos])
            addpos += 1
        while removepos < len(toremove):
            self._remove(toremove)
            removepos += 1

    # returns (boolean, proof string)
    def is_included(self, tocheck):
        return self._is_included(shahash(tocheck))

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
            if block[pos + 8:pos + 10] == bytearray([0xFF, 0xFF]):
                return self._is_included_branch(tocheck, self._ref(block[pos:pos + 8]), 8, depth + 1, len(self.subblock_lengths) - 1, buf)
            else:
                return self._is_included_leaf(tocheck, self._ref(block[pos:pos + 8]), from_bytes(block[pos + 8:pos + 10]), buf)
        if block[pos:pos + 32] == tocheck:
            buf.append(chr(GIVE1))
            buf.append(block[pos + 32:pos + 64])
            return True
        if block[pos + 32:pos + 64] == tocheck:
            buf.append(chr(GIVE0))
            buf.append(block[pos:pos + 32])
            return True
        if get_bit(tocheck, depth) == 0:
            t = get_type(block, pos)
            if t == EMPTY:
                buf.append(chr(EMPTY0))
                buf.append(block[pos + 32:pos + 64])
                return False
            if t == TERMINAL:
                buf.append(chr(GIVEBOTH))
                buf.append(block[pos:pos + 64])
                return False
            assert t == MIDDLE
            buf.append(chr(GIVE1))
            buf.append(block[pos + 32:pos + 64])
            return self._is_included_branch(tocheck, block, pos + 64, depth + 1, moddepth - 1, buf)
        else:
            t = get_type(block, pos + 32)
            if t == EMPTY:
                buf.append(chr(EMPTY1))
                buf.append(block[pos:pos + 32])
                return False
            if t == TERMINAL:
                buf.append(chr(GIVEBOTH))
                buf.append(block[pos:pos + 64])
                return False
            assert t == MIDDLE
            buf.append(chr(GIVE0))
            buf.append(block[pos:pos + 32])
            return self._is_included_branch(tocheck, block, pos + 64 + self.subblock_lengths[moddepth], depth + 1, moddepth - 1, buf)

    # returns boolean, appends to buf
    def _is_included_leaf(self, tocheck, block, pos, depth, buf):
        pos = 4 + pos * 68
        if block[pos:pos + 32] == tocheck:
            buf.append(chr(GIVE1))
            buf.append(block[pos + 32:pos + 64])
            return True
        if block[pos + 32:pos + 64] == tocheck:
            buf.append(chr(GIVE0))
            buf.append(block[pos:pos + 32])
            return True
        if get_bit(tocheck, depth) == 0:
            t = get_type(block, pos)
            if t == EMPTY:
                buf.append(chr(EMPTY0))
                buf.append(block[pos + 32:pos + 64])
                return False
            if t == TERMINAL:
                buf.append(chr(GIVEBOTH))
                buf.append(block[pos:pos + 64])
                return False
            assert t == MIDDLE
            buf.append(chr(GIVE1))
            buf.append(block[pos + 32:pos + 64])
            return self._is_included_leaf(tocheck, block, from_bytes(block[pos + 64:pos + 66]), depth + 1, buf)
        else:
            t = get_type(block, pos + 32)
            if t == EMPTY:
                buf.append(chr(EMPTY1))
                buf.append(block[pos:pos + 32])
                return False
            if t == TERMINAL:
                buf.append(chr(GIVEBOTH))
                buf.append(block[pos:pos + 64])
                return False
            assert t == MIDDLE
            buf.append(chr(GIVE0))
            buf.append(block[pos:pos + 32])
            return self._is_included_leaf(tocheck, block, from_bytes(block[pos + 66:pos + 68]), depth + 1, buf)
