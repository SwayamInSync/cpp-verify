Supported C++ subset
====================

CppVerify targets a growing fragment of ISO C++. The verifier is strongest on integer programs,
control flow, and modular function contracts.

Currently outside the supported core:

- Class templates and generic programming
- Exceptions and RTTI
- Virtual dispatch and multiple inheritance
- Heap allocation with ``new`` and ``delete``

Pointer and heap reasoning are available in the language surface (see :doc:`pointers` and
:doc:`../book/part-ii/ch14-pointers-frames-modifies`). Pointer arithmetic and array indexing
(``*(p + i)``, ``p[i]``) verify with disjointness, and quantified loop invariants over a buffer
range prove whole-array properties: single-buffer fills, ``strlen``-style search loops, and
two-buffer ``memcpy``-style copies (given an explicit non-overlap precondition) all verify
end-to-end. Addresses are modeled as mathematical integers, so range conditions are wrap-free;
disjointness facts should use **bounded** indices — an unbounded pure-disequality disjointness
(``i != k`` with no range) may report ``unknown``. Depth of automation continues to expand; see
the project :doc:`../book/part-ii/ch17-backends-modular-calls` and design notes in the repo
``docs/`` tree.

Undefined-behavior checking
---------------------------

With ``--check-ub`` the verifier proves freedom from a class of undefined behavior: **integer UB**
(signed overflow, division/modulo by zero) and **array out-of-bounds access**. A buffer's extent is
declared with ``valid(p, n)`` in a precondition, and every ``p[i]`` / ``*(p+i)`` access whose base
has a declared length must then be in ``[0, n)`` (see :doc:`integers` and
:doc:`../book/part-ii/ch18-undefined-behavior`). Not yet checked: use-after-lifetime and
uninitialized reads; pointer provenance, strict aliasing, and alignment are assumed away. The
layering plan is in ``docs/UB-CHECKING.md``.