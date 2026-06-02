Chapter 1 — Correctness and trust
==================================

When you ship software, you are asking users to **trust** that the program will behave as they expect.
**Correctness** is the precise version of that expectation: a program is correct with respect to a
specification if every allowed run satisfies what the specification says.

Programs vs specifications
--------------------------

A **program** is operational: it describes *how* to compute. A **specification** is declarative:
it describes *what* should be true. Example:

.. code-block:: cpp

   // Program (one algorithm)
   int abs(int x) { return x < 0 ? -x : x; }

   // Specification (property we want)
   // For all inputs x, the return value r satisfies r >= 0.

The program might be wrong (return ``x`` unchanged). The specification can stay the same while
you fix the implementation.

.. admonition:: Key idea
   :class: tip

   Verification separates **what** (spec) from **how** (code) so you can judge whether the
   how implies the what.

Kinds of correctness
--------------------

- **Functional correctness** — outputs and data match the spec (what CppVerify targets first).
- **Safety** — no undefined behavior (no buffer overrun, no signed overflow in critical code).
- **Security** — confidentiality, authorization (often needs richer logics).
- **Liveness** — something good eventually happens (requires temporal logics beyond the current scope).

CppVerify emphasizes **functional contracts** and **partial correctness**: if a function
terminates, its postcondition holds.

Why not “just be careful”?
--------------------------

Large systems have too many paths for informal reasoning. A single off-by-one loop, a swapped
argument, a missing ``nullptr`` check — each is obvious in hindsight and invisible in review at scale.

Formal verification does not replace engineering judgment; it **mechanizes** a class of judgments
so they cannot be forgotten on the next refactor.

What you will learn in Part I
------------------------------

We will define **logic** for stating properties, **Hoare logic** for connecting programs to
properties, **invariants** for loops, **ghost** reasoning for lemmas, **memory** conventions for
pointers, and **SMT** for automation. Part II maps each idea to CppVerify syntax and tools.

