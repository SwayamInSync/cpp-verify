C++ API reference
=================

Reference for the verification engine headers in ``clang/lib/Verify/``.

.. raw:: html

   <p><a class="btn" href="../doxygen/index.html">Open API reference (Doxygen)</a></p>

Modules
-------

.. list-table::
   :header-rows: 1
   :widths: 22 78

   * - Module
     - Role
   * - ``IR/``
     - Expressions, statements, types (VCR)
   * - ``Frontend/``
     - Clang AST to VCR conversion
   * - ``Transform/``
     - VCR passes: memory checks, pointer origins, ownership, spec inlining,
       inductive predicates, loop unrolling for BMC, and passivization
   * - ``Backend/``
     - The Obligation IR and its archives, the Z3, cvc5, and Lean adapters,
       counterexample certification, induction, and the proof cache
   * - ``Driver/``
     - Verification driver and IR output