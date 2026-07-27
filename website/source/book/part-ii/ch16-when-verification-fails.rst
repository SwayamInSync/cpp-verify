Chapter 16 — When verification fails
====================================

A failed proof means the verifier found inputs or paths that break your stated properties—treat
that as actionable feedback on the code, the contracts, or both.

Understanding the report
------------------------

Diagnostics name the obligation that failed and often include a **counterexample**: concrete
values for variables that violate the claim. Use those values to see which assumption or branch
is wrong.

``unknown`` is different from a counterexample. It means Z3 timed out or entered
a fragment it could not decide, often because the VC combines bounded
quantifiers with heap arrays. CppVerify may retry smaller ordered obligations,
but if those also remain unknown it reports the function as **not verified**.
It never treats solver uncertainty as success.

For a deliberately invalid program, both outcomes are sound:

- ``error: verification failed`` means Z3 found a concrete model;
- ``unknown`` means the verifier conservatively refused to certify it;
- only ``Verified`` is a proof result.

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
     - Use the smallest sufficient ``reveal_with_fuel`` depth; after importing
       finite lemma facts, ``hide`` an irrelevant recursive definition to keep
       the VC tractable
   * - Pointer aliasing
     - Prove distinct pointers or declare ``aliases``
   * - Overflow / divide-by-zero
     - Add the precondition the counterexample points to (see :doc:`ch18-undefined-behavior`)
   * - Indexed access is out of bounds (``--check-ub``)
     - Declare the correct ``valid(p, n)`` extent and prove the index lies in
       ``[0, n)``
   * - Heap fact disappears after a call
     - Prefer an exact ``modifies(p[i])`` / ``modifies(p->field)`` footprint,
       or state the required fact in the callee postcondition; a region
       ``modifies(*p)`` call is conservatively whole-heap today

Further reference: :doc:`../../language/index`.