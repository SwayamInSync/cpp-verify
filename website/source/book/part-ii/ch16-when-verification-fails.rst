Chapter 16 — When verification fails
====================================

A failed proof means the verifier found inputs or paths that break your stated properties—treat
that as actionable feedback on the code, the contracts, or both.

Understanding the report
------------------------

Diagnostics name the obligation that failed and often include a **counterexample**: concrete
values for variables that violate the claim. Use those values to see which assumption or branch
is wrong.

Adjusting contracts
-------------------

.. list-table::
   :header-rows: 1
   :widths: 32 68

   * - Situation
     - Response
   * - Precondition too weak
     - Strengthen ``pre`` so callers cannot supply bad inputs
   * - Postcondition too strong
     - Weaken ``post`` or fix the implementation
   * - Loop invariant too weak
     - Add facts to ``invariant`` so preservation holds
   * - Spec vs machine integers disagree
     - Use ``spec`` for mathematical integers; ``constexpr`` for machine semantics
   * - Recursive specification
     - Use ``reveal_with_fuel`` in a ghost block
   * - Pointer aliasing
     - Prove distinct pointers or declare ``aliases``
   * - Overflow / divide-by-zero (``--check-ub``)
     - Add the precondition the counterexample points to (see :doc:`ch18-undefined-behavior`)

Further reference: :doc:`../../language/index`.