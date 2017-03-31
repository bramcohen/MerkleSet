from ReferenceMerkleSet import *
from MerkleSet import *

def from_bytes(f):
    return int.from_bytes(f, 'big')

def to_bytes(f, v):
    return int.to_bytes(f, v, 'big')

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

testall()
