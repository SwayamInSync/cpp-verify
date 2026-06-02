Part II — CppVerify
===================

These chapters cover verified C++ in practice: the toolchain, contract syntax, common proof
patterns, backends (Z3, BMC, Lean export), modular calls, and how to respond when verification fails.

.. figure:: /_static/diagrams/cppverify-workflow.svg
   :align: center
   :figclass: book-figure
   :alt: Verify and compile paths from the same source

.. toctree::
   :maxdepth: 1

   ch09-why-cppverify
   ch10-getting-started
   ch11-first-verified-function
   ch12-loops-in-practice
   ch13-spec-and-proof-functions
   ch14-pointers-frames-modifies
   ch15-toolchain-and-flags
   ch16-when-verification-fails
   ch17-backends-modular-calls