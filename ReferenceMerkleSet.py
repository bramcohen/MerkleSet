from hashlib import blake2s

"""
A simple, confidence-inspiring Merkle Set standard

Advantages of this standard:
Low CPU requirements
Small proofs of inclusion/exclusion
Reasonably simple implementation

The main tricks in this standard are:

Uses blake2s because that has the best performance on 512 bit inputs
Sacrifices two bits of security for metadata information (leaf, branch, or empty) to stay within 512 bits
Skips repeated hashing of exactly two things even when they share prefix bits


Proofs are multiproofs, and support proving including/exclusion for a large number of values in 
a single string. They're a serialization of a subset of the tree.

Proof format:

multiproof: subtree
subtree: middle or terminal or unvalidated or empty
middle: MIDDLE 1 subtree subtree
terminal: hash (terminal type) 32
# Unvalidated means two or more children if the sibling isn't empty.
# If the sibling is empty it means more than two children.
unvalidated: hash (invalid type) 32
empty: EMPTY 1
"""

EMPTY = 0
TERMINAL = 0x40
MIDDLE = 0x80
INVALID = TERMINAL | MIDDLE

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

def hashdown(mystr):
    r = blake2s(bytes(mystr)).digest()
    return bytes([MIDDLE | (r[0] & 0x3F)]) + r[1:]

def get_bit(mybytes, pos):
    assert len(mybytes) == 32
    pos += 2
    return (mybytes[pos // 8] >> (7 - (pos % 8))) & 1

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
            self.hash = hashdown(children[0].hash + children[1].hash)

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

class SetError(BaseException):
    pass

def confirm_included(root, val, proof):
    return confirm_not_included_already_hashed(root, sha256(val).digest(), proof)

def confirm_included_already_hashed(root, val, proof):
    return _confirm(root, val, proof, True)

def confirm_not_included(root, val, proof):
    return confirm_not_included_already_hashed(root, sha256(val).digest(), proof)

def confirm_not_included_already_hashed(root, val, proof):
    return _confirm(root, val, proof, False)

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

