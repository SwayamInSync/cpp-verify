Functions and loops
===================

Functions
---------

.. code-block:: cpp

   int f(int x)
     pre(x > 0 && x < 1000)
     post(result > x)
   { return x + 1; }

Loops
-----

.. code-block:: cpp

   while (c)
     invariant(I)
     decreases(D)
   { ... }

Clauses go after the loop header's closing ``)``; ``for`` loops use the same
placement. Multiple ``invariant`` clauses are conjoined.

The verifier checks a loop **modularly** (no unrolling), discharging three
obligations:

.. list-table::
   :header-rows: 1
   :widths: 22 78

   * - Obligation
     - Meaning
   * - Establishment
     - ``I`` holds when the loop is first reached.
   * - Preservation
     - From an **arbitrary** state satisfying ``I && c``, one body iteration
       re-establishes ``I``. (Loop-modified variables are havocked first, so the
       invariant must be *inductive* — strong enough to re-prove itself.)
   * - Termination
     - ``0 <= D_new < D_old`` each iteration. Only checked when ``decreases`` is
       present; without it the loop is verified for **partial correctness**.

After the loop the verifier knows exactly ``I && !c`` — anything needed
downstream must be captured by the invariant.

.. note::

   Invariants are checked under **honest machine integers**. An unbounded
   accumulator invariant like ``s >= 0`` is *not* inductive (from ``s ==
   INT_MAX``, ``s + 1`` overflows negative); bound the accumulator instead
   (e.g. ``s == i``). A loop placed after an early ``return`` is checked only on
   the path that reaches it.

Each ``decreases`` expression must be integer-typed. A comma-separated tuple
``decreases(a, b)`` is a **lexicographic** measure: each iteration the tuple must
strictly decrease in lexicographic order (some component drops while every
earlier component stays equal), with all components non-negative. This proves
termination of nested counters and Ackermann-style recursion.