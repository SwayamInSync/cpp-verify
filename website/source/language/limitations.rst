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
:doc:`../book/part-ii/ch14-pointers-frames-modifies`). Depth of automation continues to expand;
see the project :doc:`../book/part-ii/ch17-backends-modular-calls` and design notes in the repo
``docs/`` tree.