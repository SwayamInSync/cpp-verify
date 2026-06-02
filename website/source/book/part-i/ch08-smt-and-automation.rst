Chapter 8 — SMT solvers and automation
======================================

Hoare logic tells us **what** to prove. **SMT solvers** (Satisfiability Modulo Theories) automate
the **how** for many formulas.

Validity via unsatisfiability
-----------------------------

To show a formula ``F`` is **always true** (valid), show ``not F`` is **unsatisfiable** (no model makes it false).

CppVerify proves ``Hypothesis ⇒ Goal`` by checking unsatisfiability of ``Hypothesis ∧ ¬Goal``:

.. figure:: /_static/diagrams/vc-validity.svg
   :align: center
   :figclass: book-figure
   :alt: Verification checks UNSAT of hypothesis combined with negated goal

If Z3 returns **unsat**, no counterexample exists — the implication holds in the modeled theory.
If **sat**, the model is a **counterexample** (concrete values for variables).

Weakest precondition calculus
-----------------------------

Instead of reasoning forward through every path by hand, the verifier computes the **weakest
precondition** ``wp(S, Q)`` — the *weakest* ``P`` such that ``{P} S {Q}`` holds. For straight-line
code, ``wp`` is largely syntactic substitution; loops become invariant obligations.

CppVerify lowers code to **passive IR** (SSA, assume/assert) then runs ``wp`` (see :doc:`../part-ii/ch15-toolchain-and-flags`).

What SMT decides (and what it does not)
---------------------------------------

Z3 understands arithmetic, Booleans, arrays, and more — within limits. It may return **unknown**
when the VC is too hard or the theory is incomplete.

Verification is always relative to:

- The **language fragment** the tool models
- **Integer semantics** (mathematical vs machine; Part II)
- **Memory model** approximations

Together, contracts, Hoare triples, invariants, ghost lemmas, frame conditions, and SMT solvers
form the vocabulary used throughout Part II.