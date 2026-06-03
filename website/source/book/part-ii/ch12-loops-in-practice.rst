Chapter 12 — Loops in practice
==============================

Map Part I’s invariant story to CppVerify syntax.

Example skeleton
----------------

.. code-block:: cpp

   while (i < n)
     invariant(0 <= i && i <= n)
     decreases(n - i)
   {
     // ...
     i++;
   }

Place ``invariant`` and ``decreases`` **after** the loop header’s closing ``)``.

Common failure modes
--------------------

.. list-table::
   :header-rows: 1
   :widths: 35 65

   * - Symptom
     - Likely fix
   * - Establishment fails
     - Weaken invariant or strengthen pre before loop
   * - Preservation fails
     - Strengthen invariant to include facts needed after body
   * - Termination fails
     - Fix ``decreases`` expression; show it decreases and stays nonnegative

``for`` loops use the same clause placement after the ``for (...)`` part.

Quantified properties
---------------------

A loop usually establishes a property over a *range*. Express that with the bounded quantifiers
``forall(i, lo, hi, e)`` and ``exists(i, lo, hi, e)`` — ``i`` ranges over ``[lo, hi)`` and the
half-open bound is the implicit trigger:

.. code-block:: cpp

   bool nonneg_prefix(int n)
     pre(n >= 0 && n <= 8)
     post(result == forall(i, 0, n, i >= 0))
   { return true; }

Quantifiers are valid anywhere a contract expression is — ``pre``, ``post``, ``invariant`` — which
is how a loop invariant talks about "everything processed so far". MVP supports **bounded**
quantifiers only.

