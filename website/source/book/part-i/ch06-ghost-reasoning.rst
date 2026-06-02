Chapter 6 — Ghost reasoning and lemmas
======================================

Some facts are true but not part of the executable algorithm. **Ghost** (or **proof-only**) code
exists only to help the verifier — lemmas, case splits, and internal assertions.

Proof obligations inside a function
-----------------------------------

While proving a function, you may need an intermediate fact:

.. code-block:: text

   // We know a <= b and b <= c from earlier lines
   // We need a <= c before the return

A **proof step** (``contract_assert`` in CppVerify) asks the verifier to show the formula at that point.
It is not a runtime check.

Lemmas as separate functions
----------------------------

Large proofs factor into **lemma** functions:

.. code-block:: text

   lemma monotonic(i, j):
     requires i <= j
     ensures f(i) <= f(j)

The lemma is verified once; call sites use its contract without repeating the induction.

Ghost variables and code
------------------------

Ghost variables track proof-only state (counters in a proof, snapshots). Ghost blocks group steps
that must not appear in compiled binaries.

**Zero runtime cost** is non-negotiable for production verification: CppVerify strips ghost
constructs in CodeGen (Part II).

Axioms vs executable definitions
--------------------------------

**Spec** (mathematical) functions define symbols used in contracts — like ``fibo(n)`` as a recurrence.
Their bodies are **definitions** for the verifier, not instructions the CPU runs.

**Proof** functions are ghost programs whose only job is to establish ``pre ==> post``.

