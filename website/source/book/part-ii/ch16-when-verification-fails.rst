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

``Lowered`` is not a fourth solver outcome. It is emitted only by
``cpp-verify --lower-only`` and says that Clang AST conversion, VCR, passive
SSA, canonical Obligation IR generation, and backend encoding succeeded without running
satisfiability. This is useful when isolating a frontend or lowering bug from a
slow quantified/heap query, but it never certifies the program.

``Exported`` is also not a proof result. The Lean path writes the canonical
obligation as an unchecked theorem with ``sorry`` and does not invoke Z3.

Trusting a new feature
----------------------

Do not use one successful Z3 result as the only implementation oracle. A
feature regression should combine:

- realistic C++ programs that must verify;
- nearby false programs that must be rejected;
- exact VCR and passive-SSA checks;
- critical typed Obligation IR and Z3-encoding checks;
- boundary cases for mathematical integers and machine bitvectors.

This split answers two independent questions. ``--lower-only`` checks whether
the program became the intended formula. Ordinary verification checks whether
that formula is valid. A timeout can block the second answer without hiding a
malformed first answer.

Proof failure versus unsupported C++
------------------------------------

A source program can also be outside CppVerify's current semantic subset. That
is different from a failed proof:

- a **conversion/unsupported error** means the relevant C++ semantics are not
  modeled and verification stopped fail-closed;
- **verification failed** means the semantics were lowered and a
  counterexample violates an obligation;
- **unknown** means the obligation was lowered but automation did not decide it.

Do not work around an unsupported diagnostic by replacing a C++ operation with
an unchecked integer or external axiom. Either reformulate the program within
the documented subset or add the missing semantics through Clang, VCR,
passivization, backend encoding, and positive/false-proof tests.

The full feature matrix, memory/object-model boundaries, missing induction and
solver tactics, performance work, library models, and raw-C++ readiness gates
are maintained in :doc:`../../language/limitations`.

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