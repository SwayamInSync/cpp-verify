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

