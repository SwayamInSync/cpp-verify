Chapter 12 — Loops in practice
==============================

Map Part I’s invariant story to CppVerify syntax.

Example skeleton
----------------

.. cppverify-example: fragment

.. code-block:: cpp

   while (i < n)
     cv::invariant(0 <= i && i <= n)
     cv::decreases(n - i)
   {
     // ...
     i++;
   }

Place ``cppverify::invariant`` and ``cppverify::decreases`` **after** the loop header’s closing ``)``.

What the verifier actually checks
---------------------------------

A loop is verified **modularly**: the verifier does not unroll it (bounded
model checking, ``--backend=bmc``, does; see Chapter 17). Instead it
discharges three obligations from the invariant ``I`` and measure ``D``:

#. **Establishment.** ``I`` holds when the loop is first reached (from the
   concrete state just before the loop).
#. **Preservation.** Starting from an *arbitrary* state that satisfies
   ``I`` **and** the loop condition, one iteration of the body re-establishes
   ``I``. The state is arbitrary — the verifier forgets ("havocs") every
   variable the loop writes and assumes only ``I``. This is what makes the proof
   cover *all* iterations at once.
#. **Termination.** Under the same arbitrary state, the measure is
   non-negative before the iteration and strictly smaller after it:
   ``0 <= D_old`` and ``D_new < D_old``.

After a normal exit the verifier knows ``I && !cond``, plus the unchanged
values of everything the loop does not write. A ``break`` or ``return`` leaves
from its own state. A fact about what the loop writes has to be in the
invariant.

``do`` loops
------------

A contracted ``do`` loop places its clauses after the trailing condition and
before the semicolon:

.. cppverify-example: fragment

.. code-block:: cpp

   do {
     i = i + 1;
   } while (i < n)
     cv::invariant(i >= 1 && i <= n)
     cv::decreases(n - i);

The first body execution is mandatory. CppVerify checks it from the concrete
incoming state and establishes the invariant **after** that execution. It then
uses the same modular preservation and termination rule as ``while`` for all
later iterations. ``cppverify::old(expr)`` in a loop invariant always reads the enclosing
function's entry state; it is not a previous-iteration operator. A function
local has no entry-state value and is rejected inside ``cppverify::old(...)``.
A ``return`` in a loop body checks the postcondition in its own state, in
every kind of loop. In a ``do`` loop's first iteration, which runs before the
invariant holds, a ``break`` skips the rest of the loop and a ``continue`` goes
to the condition, where the invariant must first hold. Ghost code that leaves
a loop is rejected.

Switches, and the other ways through a loop
-------------------------------------------

A ``switch`` runs from the matching label to a ``break`` or its end, falling
through the labels in between; inside a loop, ``continue`` goes on with the
loop and ``break`` leaves the switch. The verifier follows each path, so a
loop over a switch needs the same invariant as one over an ``if``:

.. code-block:: cpp

   int vowels(const char *s, int n)
     cv::pre(cv::valid(s, n) && 0 <= n && n <= 1000)
     cv::post(0 <= cv::result && cv::result <= n)
   {
     int count = 0;
     for (int i = 0; i < n; i++)
       cv::invariant(0 <= i && i <= n && 0 <= count && count <= i)
       cv::decreases(n - i)
     {
       switch (s[i]) {
       case 'a':
       case 'e':
       case 'i':
       case 'o':
       case 'u':
         count++;
         break;
       default:
         continue;
       }
     }
     return count;
   }

.. code-block:: text

   Verified: vowels [backend=z3]

Character literals such as ``'a'`` are integers of their type, as in C++.

A loop condition may declare a variable (``while (int k = next(i))``), made
at every test; a ``for`` loop may leave out its condition (``for (;;)``) and
end by ``break`` or ``return``, with a measure like any other; and its
increment may be a comma expression, ``i++, j += 2``, whose operands run in
order.

Inductive invariants and machine integers
-----------------------------------------

Because preservation starts from an *arbitrary* ``I``-state, the invariant must
be **inductive**: strong enough to re-prove itself. The classic trap is an
unbounded accumulator under honest machine integers:

.. cppverify-example: fails sum

.. code-block:: cpp

   // REJECTED: s >= 0 is not inductive.
   int sum(int n) cv::pre(n >= 0 && n <= 1000) cv::post(cv::result >= 0) {
     int s = 0, i = 0;
     while (i < n)
       cv::invariant(i >= 0 && i <= n && s >= 0)   // too weak
       cv::decreases(n - i)
     { s = s + 1; i = i + 1; }
     return s;
   }

From an arbitrary ``s`` satisfying ``s >= 0`` the verifier may pick
``s == INT_MAX``; then ``s + 1`` overflows ``int``, which is undefined
behavior, and the verifier reports the ``overflow`` obligation at ``s + 1``.
CppVerify reasons about ``int`` as a real 32-bit type, so this is not a false
alarm. The fix is to **bound the accumulator**
so it provably cannot overflow:

.. code-block:: cpp

   int sum_bounded(int n) cv::pre(n >= 0 && n <= 1000) cv::post(cv::result >= 0) {
     int s = 0, i = 0;
     while (i < n)
       cv::invariant(i >= 0 && i <= n && s == i)   // s tracks i, bounded by n
       cv::decreases(n - i)
     { s = s + 1; i = i + 1; }
     return s;
   }

Every loop needs ``cppverify::decreases``
-----------------------------------------

Verification is total correctness, as in Verus. A loop without ``cppverify::decreases``
leaves its function ``Unresolved`` with reason ``decreases.missing``, unless
its condition is the constant false (the ``do { ... } while (0)`` of a macro):
such a loop never repeats. When a
loop really may run forever (an event loop, a server), say so with
``cppverify::decreases(*)``: the function is then proved for the executions that
terminate and reported ``Verified ... [partial]``, and so is every caller.

.. code-block:: cpp

   int wait_for(const int *flag)
     cv::pre(valid(flag, 1))
     cv::post(cv::result == 1)
   {
     while (*flag != 1)
       cv::decreases(*)
     {
     }
     return *flag;
   }

What a loop does not write
--------------------------

A loop writes only the objects its stores and calls reach, so every other
object keeps its value with no invariant saying so. To narrow the frame inside
one object, list what the loop writes with ``cppverify::modifies`` after its invariants
(ACSL's ``loop assigns``). The footprints are read in each iteration's state:

.. code-block:: cpp

   void zero_prefix(int *a, int n)
     cv::pre(valid(a, n + 1) && n >= 1 && n <= 1000)
     cv::modifies(*a)
     cv::post(a[n] == cv::old(a[n]))
   {
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n)
       cv::modifies(a[0 : n])
       cv::decreases(n - i)
     {
       a[i] = 0;
     }
   }

Ghost variables
---------------

``cppverify::ghost T x = e;`` declares a variable that exists only for verification and
lives in the function's scope, so loop invariants may name it. It can snapshot
a value from before the loop:

.. code-block:: cpp

   void add_all(int *a, int n, int d)
     cv::pre(valid(a, n) && n >= 0 && n <= 1000 && d >= 0 && d <= 1000)
     cv::pre(cv::forall(k, 0, n, 0 <= a[k] && a[k] <= 1000))
     cv::modifies(*a)
     cv::post(cv::forall(k, 0, n, a[k] == cv::old(a[k]) + d))
   {
     cv::ghost int total = n;
     for (int i = 0; i < n; i = i + 1)
       cv::invariant(0 <= i && i <= n && total == n)
       cv::invariant(cv::forall(k, 0, i, a[k] == cv::old(a[k]) + d))
       cv::invariant(cv::forall(k, i, n, a[k] == cv::old(a[k])))
       cv::decreases(total - i)
     {
       a[i] = a[i] + d;
     }
   }

Loops over an array
-------------------

A range-based ``for`` loop over an array visits its elements in order. Its
contract holds at the loop's head, where the loop variable is not declared
yet, so it names the position instead: ``cppverify::index``, the number of
elements already visited, 0 at the first test and the size at the end. A
property of the elements so far is a quantifier up to it:

.. code-block:: cpp

   struct Samples {
     int values[16];
   };

   int largest(const Samples *s)
     cv::pre(s != nullptr)
     cv::post(cv::forall(k, 0, 16, s->values[k] <= cv::result))
     cv::post(cv::exists(k, 0, 16, s->values[k] == cv::result))
   {
     int best = s->values[0];
     for (int v : s->values)
       cv::invariant(cv::forall(k, 0, cv::index, s->values[k] <= best))
       cv::invariant(cv::exists(k, 0, 16, s->values[k] == best))
     {
       if (v > best)
         best = v;
     }
     return best;
   }

.. code-block:: text

   Verified: largest [backend=z3]

The loop needs no ``cppverify::decreases``: without one, its measure is the
number of elements left. Its variable may be a reference, which writes the
element (``for (int &x : a) x = 0;``), and its range a local array, an array
member reached through a pointer, a constant table, or a string literal,
whose last element is the terminating zero. The verifier finds the element
again at each iteration, where C++ evaluates the range once, so a range found
through a call, a pointer read from memory, or a variable the body changes
is rejected; copy the pointer into a variable the body leaves alone. A loop
over a class, through its ``begin`` and ``end``, is not supported yet.

Two loops, one name
-------------------

Two loops may each declare their counter, ``for (int i = 0; ...)``, and a
block may declare a name an outer one already has: each declaration is a
variable of its own, so the second ``i`` starts uninitialized and neither
loop's invariant is about the other's counter. A counterexample shows the
name as written, with the verifier's own name for the second one, ``i#2``, in
``[ssa=...]``.

Lexicographic measures
----------------------

When no single quantity falls every iteration, pass a comma-separated **tuple** —
``cppverify::decreases(a, b)`` is ordered lexicographically. Each iteration the tuple must
strictly decrease in lex order: some component drops while every earlier
component is unchanged. The component that drops must be non-negative before
the step; the others may be anything. This is what
proves nested counters and Ackermann-style recursion terminate:

.. cppverify-example: fragment

.. code-block:: cpp

   while (i > 0 || j > 0)
     cv::invariant(i >= 0 && j >= 0)
     cv::decreases(i, j)        // j falls while i is fixed; when j resets, i drops
   {
     if (j > 0) { j = j - 1; }
     else       { i = i - 1; j = b; }
   }

The same tuple syntax works on a function's ``cppverify::decreases`` clause, for recursive
``cppverify::spec``/``cppverify::proof`` functions whose arguments shrink lexicographically.

Loops after an early return
---------------------------

A loop that follows an early ``return`` verifies normally — its obligations are
only checked on the path that actually reaches it:

.. code-block:: cpp

   int f(int n) cv::pre(n >= 0 && n <= 50) cv::post(cv::result >= 0) {
     if (n == 0) return 0;          // early exit
     int i = 0;
     while (i < n)
       cv::invariant(0 <= i && i <= n)  // not checked on the n == 0 path
       cv::decreases(n - i)
     { i = i + 1; }
     return i;
   }

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
     - Fix ``cppverify::decreases`` expression; show it is non-negative before each iteration and decreases

``for`` loops use the same clause placement after the ``for (...)`` part.

Quantified properties
---------------------

A loop usually establishes a property over a *range*. Express that with the bounded quantifiers
``cppverify::forall(i, lo, hi, e)`` and ``cppverify::exists(i, lo, hi, e)`` — ``i`` ranges over ``[lo, hi)``, and the
solver chooses the terms that instantiate the quantifier unless a ``cppverify::trigger``
names one (:doc:`ch13-spec-and-proof-functions`):

.. code-block:: cpp

   bool nonneg_prefix(int n)
     cv::pre(n >= 0 && n <= 8)
     cv::post(cv::result == cv::forall(i, 0, n, i >= 0))
   { return true; }

Quantifiers are valid anywhere a contract expression is — ``cppverify::pre``, ``cppverify::post``, ``cppverify::invariant`` — which
is how a loop invariant talks about "everything processed so far". Quantifiers
without bounds, ``cppverify::forall(i, e)``, range over all integers (Chapter 13).

Recursive spec functions in an invariant
----------------------------------------

A common pattern relates the accumulator to a recursive ``cppverify::spec`` function — the
loop *computes* what the spec *defines*. The invariant ``acc == count(i - 1)``
below says "after processing ``i - 1`` elements, ``acc`` equals the spec's
value":

.. code-block:: cpp

   cv::spec int count(int n)
     cv::decreases(n)
   { if (n <= 0) return 0; return 1 + count(n - 1); }

   int compute_count(int n)
     cv::pre(n >= 0 && n <= 10)
     cv::post(cv::result == count(n))
   {
     int acc = 0, i = 1;
     while (i <= n)
       cv::invariant(i >= 1 && i <= n + 1 && acc == count(i - 1))
       cv::decreases(n - i + 1)
     {
       acc = acc + 1;
       i = i + 1;
     }
     return acc;
   }

The solver unfolds ``count`` once at each application the proof names, so
preservation sees ``count(i) == 1 + count(i - 1)`` at the symbolic index ``i``
without help. A spec that multiplies works the same way:

.. code-block:: cpp

   cv::spec int factorial(int n)
     cv::decreases(n)
   { return n <= 0 ? 1 : n * factorial(n - 1); }

   int fact_loop(int n)
     cv::pre(n >= 0 && n <= 12)
     cv::post(cv::result == factorial(n))
   {
     int acc = 1, i = 1;
     while (i <= n)
       cv::invariant(i >= 1 && i <= n + 1 && acc == factorial(i - 1))
       cv::decreases(n - i + 1)
     {
       acc = acc * i;
       i = i + 1;
     }
     return acc;
   }

When a step needs more than one unfolding, raise the depth with
``cppverify::reveal_with_fuel`` in a ghost block, or state the step as a lemma (a
``cppverify::proof`` function whose postcondition is the fact) and call it from the
loop body. Chapter 13 shows both.
