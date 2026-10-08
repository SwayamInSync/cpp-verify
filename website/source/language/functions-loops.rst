Functions and loops
===================

Functions
---------

.. code-block:: cpp

   int f(int x)
     cv::pre(x > 0 && x < 1000)
     cv::post(cv::result > x)
   { return x + 1; }

Contracts may instead appear on a forward declaration.  A later definition
inherits that declaration's contract even when its parameter names differ::

   int f(int value)
     cv::pre(value > 0)
     cv::post(cv::result > value);

   int f(int x) { return x + 1; }

A caller's proof uses its callees' contracts, so a verdict is only as good as
those contracts. A caller whose proof relies on a callee contract that the
callee's own verification did not establish is ``Unresolved`` with reason
``callee.contract``, naming the callee.

Trusted contracts
-----------------

Some contracts cannot be proved in the program being verified: a function
from a library compiled elsewhere, a system call, a routine whose body is
outside the verified subset, or a lemma you decide to assume.
``[[cppverify::trusted]]`` marks such a contract as assumed, as Verus's
``#[verifier::external_body]`` does:

.. code-block:: cpp

   // Defined in another library.
   [[cppverify::trusted]] int clamp_byte(int v)
     cv::post(0 <= cv::result && cv::result <= 255);

   // Compiled and run, but its body is not verified.
   [[cppverify::trusted]] int read_sensor(int channel)
     cv::pre(channel >= 0 && channel < 4)
     cv::post(cv::result >= 0 && cv::result <= 1023)
   {
     return channel * 300;
   }

   // An axiom: a proof function without a proof.
   cv::spec int sq(int x) { return x * x; }

   [[cppverify::trusted]] cv::proof void sq_nonnegative(int x)
     cv::post(sq(x) >= 0);

   int sample(int c)
     cv::pre(c >= 0 && c < 4)
     cv::post(0 <= cv::result && cv::result <= 255)
   {
     int r = read_sensor(c);
     cv::ghost { sq_nonnegative(r); }
     return clamp_byte(r);
   }

.. code-block:: text

   trusted.cpp:2:28: Trusted: clamp_byte (contract assumed, not verified)
   trusted.cpp:6:28: Trusted: read_sensor (contract assumed, not verified)
   Verified: spec axiom: sq
   trusted.cpp:16:35: Trusted: sq_nonnegative (contract assumed, not verified)
   Verified: sample [backend=z3] [trusts=clamp_byte,read_sensor,sq_nonnegative]

- On a declaration, the contract is assumed at every call; the preconditions
  are still checked there.
- On a definition, the body is compiled but not verified.
- On a proof function, the postcondition is an axiom.
- A spec function cannot be trusted: its definition is its meaning, so there
  is nothing to assume. The attribute is an error there.
- Each trusted contract is marked on its own function: ``#pragma clang
  attribute`` cannot apply the attribute to a region.
- Every verdict that relies on a trusted contract lists it in
  ``[trusts=...]`` (JSON ``"trusts"``), transitively through verified
  callees: a caller of ``sample`` carries the same three names.

The mark may appear on any declaration of the function. Without it, a
contract with no definition is neither proved nor vouched for, so it proves
nothing:

.. code-block:: cpp

   int helper(int v)
     cv::post(cv::result == v);

   int uses_helper(int v)
     cv::post(cv::result == v)
   {
     return helper(v);
   }

.. code-block:: text

   warning: helper has a contract but no definition, so its callers are not
     verified; mark the declaration [[cppverify::trusted]] to assume the contract
   Unresolved: uses_helper [backend=z3] [reason=callee.contract] (relies on the
     contract of helper (no definition; mark it [[cppverify::trusted]] to
     assume it), which is not established)

A trusted contract is an assumption, and a wrong one makes proofs wrong. One
that contradicts the state of a call (no result can satisfy it) would make
everything after the call hold vacuously; CppVerify reports that case with
``[vacuous]`` and a warning at the call (see :doc:`tooling`).

An uncontracted ``constexpr`` definition may be lifted for use in contract
expressions. It is lifted where verification uses it: in a contract, a
verified body, a type invariant, or another lifted function, so the
``constexpr`` functions of a header that nothing verified uses are never
examined. Once a ``constexpr`` function has executable ``cppverify::pre``/``cppverify::post``
clauses, it remains a modular executable function: calls must satisfy its
preconditions and cannot be used as pure contract expressions.

Preconditions, ``cppverify::old(parameter)``, and a parameter named in a postcondition
all denote the argument's entry value, as in ACSL, even when the callee
reassigns its by-value parameter; a caller can therefore use the
postcondition directly.

Behaviors
---------

A contract can be split into cases, as ACSL behaviors do. ``behavior(name,
assumes)`` starts a case; the ``pre`` and ``post`` clauses after it apply
where its assumption holds (``assumes`` at entry):

.. code-block:: cpp

   int abs_value(int x)
     cv::behavior(nonnegative, x >= 0)
       cv::post(cv::result == x)
     cv::behavior(negative, x < 0)
       cv::pre(x > -2147483647 - 1)
       cv::post(cv::result == -x)
     cv::complete_behaviors
     cv::disjoint_behaviors
   {
     return x < 0 ? -x : x;
   }

``cppverify::complete_behaviors`` requires that some behavior applies to every input the
preconditions admit, and ``cppverify::disjoint_behaviors`` that no two do; either may
list the behaviors it relates, as in ``cppverify::disjoint_behaviors(low, high)``.

Loops
-----

.. cppverify-example: fragment

.. code-block:: cpp

   while (c)
     cv::invariant(I)
     cv::decreases(D)
   { ... }

Clauses go after the loop header's closing ``)``; ``for`` loops use the same
placement. For ``do`` loops, clauses go after the trailing ``while (c)`` and
before its semicolon:

.. cppverify-example: fragment

.. code-block:: cpp

   do {
     value = value + 1;
   } while (value <= n)
     cv::invariant(value >= 1 && value <= n + 1)
     cv::decreases(n + 1 - value);

The mandatory first body execution is checked from the concrete incoming state.
It must establish the invariant; subsequent iterations use the ordinary
modular ``while`` rule. The invariant therefore need not hold before entering
the first body.

Multiple ``cppverify::invariant`` clauses are conjoined. ``cppverify::old(expr)`` is permitted in an
invariant and always denotes the enclosing function's entry state, not the
previous iteration. Function locals do not exist at function entry and are
rejected inside ``cppverify::old(...)``; use an ordinary snapshot local directly instead.
``return``, ``break``, and ``continue`` may leave a ``while`` or ``for`` loop
from any iteration. A ``return`` checks the postcondition in its own state and
a ``break`` continues after the loop in its own state. A ``continue`` ends the
iteration: the invariant must hold again and the ``cppverify::decreases`` measure must
drop, after a ``for`` increment has run. ``break`` and ``continue`` in a
``do`` loop are not supported yet, and ``cppverify::ghost`` code cannot leave an
executable loop.

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
     - ``0 <= D_old`` and ``D_new < D_old`` each iteration (and at each
       ``continue``).
   * - Frame
     - With a loop ``cppverify::modifies``, every cell outside its footprints, read in the
       iteration's state, is unchanged since the loop began.

Verification is total correctness, as in Verus: an executable loop without
``cppverify::decreases`` leaves its function ``Unresolved`` with reason
``decreases.missing``. ``cppverify::decreases(*)`` allows a loop (or an executable
function) to diverge; its function and every caller are then reported
``Verified ... [partial]``, proved only for the executions that terminate.
Ghost-block and proof-function loops are erased at runtime and must have a
real measure; ``cppverify::decreases(*)`` is rejected there.

Nobody knows whether this loop ends for every start, so it has no measure:

.. code-block:: cpp

   unsigned collatz_steps(unsigned n)
     cv::post(n != 1 || cv::result == 0)
   {
     unsigned steps = 0;
     while (n != 1)
       cv::invariant(cv::old(n) != 1 || (n == 1 && steps == 0))
       cv::decreases(*)
     {
       n = n % 2 == 0 ? n / 2 : 3 * n + 1;
       steps = steps + 1;
     }
     return steps;
   }

   unsigned none()
     cv::post(cv::result == 0)
   {
     return collatz_steps(1);
   }

.. code-block:: text

   Verified: collatz_steps [backend=z3] [partial]
   Verified: none [backend=z3] [partial]
   warning: collatz_steps: proved only for executions that terminate: decreases(*) at 11:15 allows it to diverge
   warning: none: proved only for executions that terminate: it calls collatz_steps, which may diverge

A loop writes only the objects its stores and calls reach, so other memory
keeps its value across it without an invariant. ``cppverify::modifies(...)`` after the
invariants narrows that further, like ACSL's ``loop assigns``; its footprints
are read in each iteration's state, so ``cppverify::modifies(a[0 : i])`` describes the
prefix written so far.

.. code-block:: cpp

   void clear_prefix(int *a, int n, int k)
     cv::pre(valid(a, n) && 0 <= k && k <= n && n <= 1000)
     cv::modifies(a[0 : k])
     cv::post(cv::forall(j, 0, k, a[j] == 0))
     cv::post(cv::forall(j, k, n, a[j] == cv::old(a[j])))
   {
     for (int i = 0; i < k; i = i + 1)
       cv::invariant(0 <= i && i <= k)
       cv::invariant(cv::forall(j, 0, i, a[j] == 0))
       cv::modifies(a[0 : i])
       cv::decreases(k - i)
     {
       a[i] = 0;
     }
   }

The loop's frame is checked at the end of each iteration, after the ``for``
increment, so ``a[0 : i]`` then covers the cell just written; the function's
``cppverify::modifies(a[0 : k])`` is the range ``[0, k)``, and the cells from ``k`` on
keep their values without an invariant saying so.

After the loop the verifier knows exactly ``I && !c`` — anything needed
downstream must be captured by the invariant.

.. note::

   Contracts are mathematical, but the loop body runs on machine integers.
   An unbounded accumulator invariant like ``s >= 0`` does not prove that the
   body's ``s + 1`` cannot overflow (``s`` may be ``INT_MAX``); bound the
   accumulator instead (e.g. ``s == i``). A loop placed after an early ``return`` is checked only on
   the path that reaches it.

Each ``cppverify::decreases`` expression must be integer-typed. A comma-separated tuple
``cppverify::decreases(a, b)`` is a **lexicographic** measure: each iteration the tuple must
strictly decrease in lexicographic order (some component drops while every
earlier component stays equal), and the component that drops must be
non-negative before the step, as in ACSL. This proves termination of nested
counters and Ackermann-style recursion.

Recursive ``cppverify::spec``, ``cppverify::proof``, and executable functions use the same
well-founded, lexicographic discipline. Each recursive call must occur on a
path where its ``cppverify::decreases`` measure is nonnegative and strictly smaller than
the caller's. Calls hidden after assignment-only or fallthrough branches are
checked as well.

The end-to-end acceptance programs include recursive and iterative factorial
and Fibonacci implementations, each proved against a mathematical recursive
specification at the exact signed-``int`` boundary.
