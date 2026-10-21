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

A **proof step** (``cppverify::check`` in CppVerify) asks the verifier to show the formula at that point.
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

Erasure also imposes an isolation rule: ghost code may update only ghost-local
variables and their direct fields. It cannot mutate executable locals, global
state, or pointees; call executable functions; or return from the enclosing
function. Ghost loops require a termination measure, so an erased infinite
loop cannot suppress runtime code only in the verifier.

Axioms vs executable definitions
--------------------------------

**Spec** (mathematical) functions define symbols used in contracts — like ``fibo(n)`` as a recurrence.
Their bodies are **definitions** for the verifier, not instructions the CPU runs.

**Proof** functions are ghost programs whose only job is to establish ``pre ==> post``.
They can mutate local proof state and call other proof functions, but cannot
write executable memory or invoke executable functions.

Opacity and fuel
----------------

A recursive spec's defining axiom — ``∀n. fibo(n) = fibo(n-1) + fibo(n-2)`` — is dangerous to hand
an SMT solver unrestricted: matching the right-hand side reintroduces the symbol and the instantiation
never stops (a *matching loop*). The remedy is to unfold a recursive spec only a bounded number of
times: once by default (fuel 1), and deeper only where a proof asks for it:

- **fuel** *n* — unfold the definition *n* times along this obligation;
- **reveal / hide** — turn a spec transparent or opaque in a whole function.

This is a knob on *automation*, not on truth: no setting makes a false claim verify or a true one
fail. It does change what a proof can reach: with a definition hidden, or unfolded too few times, a
claim may stay unresolved, and more fuel can settle it. Part II maps these to ``cppverify::reveal_with_fuel``, ``cppverify::reveal``, and ``cppverify::hide``.
