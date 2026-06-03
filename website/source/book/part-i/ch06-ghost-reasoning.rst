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

Opacity and fuel
----------------

A recursive spec's defining axiom — ``∀n. fibo(n) = fibo(n-1) + fibo(n-2)`` — is dangerous to hand
an SMT solver unrestricted: matching the right-hand side reintroduces the symbol and the instantiation
never stops (a *matching loop*). The remedy is to keep recursive specs **opaque** by default and
unfold them only as far as a proof needs:

- **fuel** *n* — unfold the definition *n* times along this obligation;
- **reveal / hide** — turn a spec transparent or opaque for a region of a proof.

This is a knob on *automation*, not on truth: revealing more never changes what is provable, only how
hard the solver works. Part II maps these to ``reveal_with_fuel``, ``reveal``, and ``hide``.

