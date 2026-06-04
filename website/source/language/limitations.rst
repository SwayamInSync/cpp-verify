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

With ``--check-ub`` the verifier also proves freedom from a class of undefined behavior. Today this
covers **integer UB** — signed overflow and division/modulo by zero (see :doc:`integers` and
:doc:`../book/part-ii/ch18-undefined-behavior`). **Memory-safety UB** (out-of-bounds access,
use-after-lifetime, uninitialized reads) is not yet checked, and pointer provenance, strict
aliasing, and alignment are assumed away. The layering plan is in ``docs/UB-CHECKING.md``.