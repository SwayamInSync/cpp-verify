Functions and loops
===================

Functions
---------

.. code-block:: cpp

   int f(int x)
     pre(x > 0 && x < 1000)
     post(result > x)
   { return x + 1; }

Contracts may instead appear on a forward declaration.  A later definition
inherits that declaration's contract even when its parameter names differ::

   int f(int value)
     pre(value > 0)
     post(result > value);

   int f(int x) { return x + 1; }

A contracted declaration with no definition is an explicit trusted interface.
Calls are verified against its contract, and ``cpp-verify`` emits a warning that
the external contract is being assumed rather than reporting it as verified.

An uncontracted ``constexpr`` definition may be lifted for use in contract
expressions.  Once a ``constexpr`` function has executable ``pre``/``post``
clauses, it remains a modular executable function: calls must satisfy its
preconditions and cannot be used as pure contract expressions.

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

Recursive ``spec``, ``proof``, and executable functions use the same
well-founded, lexicographic discipline. Each recursive call must occur on a
path where its ``decreases`` measure is nonnegative and strictly smaller than
the caller's. Calls hidden after assignment-only or fallthrough branches are
checked as well.

The end-to-end acceptance programs include recursive and iterative factorial
and Fibonacci implementations, each proved against a mathematical recursive
specification at the exact signed-``int`` boundary.
