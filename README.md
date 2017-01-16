# MerkleSet
A highly performant Merkle set data structure

This code is expected to be ported to C in the future. A number of aspects of it don't make much sense in Python, most notably the _ref and _deref methods, which should be replaced with simple referencing and dereferencing on a port to C.

merkle_set.py contains a reference implementation and a performant implementation. The reference implementation is much simpler and more understandable but when ported to C the non-reference implementation will have far better performance. They have exactly identical semantics and will give the same results in all cases.
