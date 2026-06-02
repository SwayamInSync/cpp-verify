Chapter 2 — The limits of testing
=================================

Testing is the default way we gain confidence in software. It is indispensable — and **incomplete**
for proving absence of bugs.

What testing does well
----------------------

- Finds **witnesses** to failure quickly (a concrete input that reproduces a crash).
- Validates integration, performance, and human-visible behavior.
- Cheap to run on every commit in CI.

What testing cannot guarantee
-----------------------------

Consider ``int abs(int x)`` that should return a non-negative value. Tests might check:

.. code-block:: cpp

   assert(abs(0) == 0);
   assert(abs(-3) == 3);
   assert(abs(5) == 5);

There are infinitely many ``int`` values. No finite test suite exercises all of them.

.. figure:: /_static/diagrams/testing-vs-samples.svg
   :align: center
   :figclass: book-figure
   :alt: Testing uses finitely many sample inputs; verification covers all inputs in the modeled domain

Even with billions of random tests, **absence of observed failure is not proof of absence of bugs**.
The industry phrase is “testing shows presence, not absence, of errors.”

Path explosion in control flow
------------------------------

.. code-block:: cpp

   int f(int a, int b, int c) {
     int x = 0;
     if (a > 0) x++;
     if (b > 0) x++;
     if (c > 0) x++;
     return x;
   }

Three ``if`` statements yield :math:`2^3 = 8` paths. Add loops and pointers: path count explodes.
Test coverage metrics (line, branch) **under-approximate** which logical combinations were exercised.

Regression vs proof
-------------------

A test encodes one scenario: “when I call ``f(1,2,3)``, I expect ``3``.” A **proof** encodes a
general claim: “for **all** inputs satisfying the precondition, the postcondition holds.”

When someone later edits ``f``, tests might still pass while a new input breaks an unstated assumption.
A verified contract fails until the proof obligation is discharged again.

When testing remains essential
------------------------------

Verification models a **subset** of reality (integer semantics, memory model, no concurrency yet).
Tests still catch:

- Spec wrong for the real world (“we proved the wrong thing”).
- Compiler/backend bugs outside the verifier model.
- Environment issues (I/O, configuration).

**Use tests and verification together:** tests for reality checks; verification for logical
implications inside the modeled language.

