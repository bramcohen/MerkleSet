# MerkleSet
A highly performant Merkle set data structure

Merkle set implementations tend to have very poor cache coherence because nodes are often stored nowhere near each other in memory. The non-reference implemention in here does a good job of keeping parent and sibling nodes nearby, thus dramatically reducing the number of cache misses and improving performance.

RefenceMerkleSet.py contains a simple reference implementation.

MerkleSet.py contains an implementation which will be very performant after porting to C. A number of aspects of it don't make much sense in Python, most notably the _ref and _deref methods, which should be replaced with simple referencing and dereferencing on a port to C. This was written in a slightly odd style specifically for the purposes of making porting to C a direct transliteration.

TestMerkleSet.py does extensive testing of both implementions. It gets 98% code coverage and handles many semantic edge cases as well.
