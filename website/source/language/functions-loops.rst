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
inherits that declaration's contract even when its parameter names differ:

.. code-block:: cpp

   int f(int value)
     cv::pre(value > 0 && value < 1000)
     cv::post(cv::result > value);

   int f(int x) { return x + 1; }

A local may take the name of a parameter or of another local, in an inner
block or a later one (two ``for (int i = ...)`` loops, say): each declaration
is a variable of its own, uninitialized until it is assigned whatever an
earlier one with its name held. A counterexample shows its name as written,
with the line of its declaration when another variable of the
counterexample has that name (``i (line 8) = 0 -> 1, i (line 14) = 0 -> 1``
for two loops that each declare ``i``); JSON records give the verifier's name
for each version as ``ssa_name``, ``i#2_1`` for the first of the second
``i``. Before 0.2 such a declaration was an error, ``local variable shadowing
is unsupported``.

A default argument is evaluated at the call, with the checks of its
operations there. A ``consteval`` call, like any constant Clang evaluates, is
its value, and so is an expression that evaluates nothing at run time:
``noexcept(e)``, a requires-expression, a concept such as ``Small<T>``, a
type trait such as ``__is_same(T, U)``, ``offsetof``, and
``__builtin_LINE()``. ``__builtin_expect(e, c)`` is ``e``. ``static_assert``, type
aliases, using-declarations, and local classes and enumerations declare
names and do nothing at run time.

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
   trusted.cpp:16:39: Trusted: sq_nonnegative (contract assumed, not verified)
   Verified: sample [backend=z3] [trusts=clamp_byte,read_sensor,sq_nonnegative]

- On a declaration, the contract is assumed at every call that sees no
  definition; the preconditions are still checked there.
- On a definition, the body is compiled but not verified. A definition that
  only inherits the mark from an earlier declaration (a header's, say) is
  verified: to leave a body unverified, mark the definition itself.
- On a proof function, the postcondition is an axiom.
- A spec function cannot be trusted: its definition is its meaning, so there
  is nothing to assume. The attribute is an error there.
- Each trusted contract is marked on its own function: ``#pragma clang
  attribute`` cannot apply the attribute to a region.
- Every verdict that relies on a trusted contract lists it in
  ``[trusts=...]`` (JSON ``"trusts"``), transitively through verified
  callees: a caller of ``sample`` carries the same three names.

Without the mark, a contract with no definition is neither proved nor
vouched for, so it proves nothing:

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

Contracts across files
----------------------

Real code declares a function with its contract in a header and defines it
in one file. Verified alone, a file that sees only the declaration has no
definition, as above. Verified together in one run, the files settle it: a
proof that rests on the contract stands once the verification of its
definition establishes it, and is ``Unresolved`` with ``callee.contract``
otherwise, as within one file.

.. cppverify-example: fragment
.. code-block:: cpp

   // include/mathx.h
   int clamp100(int x)
     cv::post(cv::result >= 0 && cv::result <= 100);

   // src/mathx.cpp
   #include "mathx.h"

   int clamp100(int x)
   {
     if (x < 0)
       return 0;
     if (x > 100)
       return 101;
     return x;
   }

   // src/a.cpp
   #include "mathx.h"

   int scaled(int x)
     cv::post(cv::result >= 0 && cv::result <= 200)
   {
     return 2 * clamp100(x);
   }

.. code-block:: text

   $ cpp-verify src/a.cpp src/mathx.cpp -- -Iinclude
   Unresolved: scaled [backend=z3] [reason=callee.contract] (relies on the contract of clamp100, which its verification in src/mathx.cpp does not establish)
   In file included from src/mathx.cpp:1:
   include/mathx.h:2:28: error: verification failed: clamp100 [postcondition] [backend=z3] [reason=counterexample]
       2 |   cv::post(cv::result >= 0 && cv::result <= 100);
         |            ~~~~~~~~~~~~~~~~^~~~~~~~~~~~~~~~~~~~
   include/mathx.h:2:28: note: counterexample: x = 101, result = 101
   src/mathx.cpp:5:3: note: takes the false branch
       5 |   if (x < 0)
         |   ^
   src/mathx.cpp:7:3: note: takes the true branch
       7 |   if (x > 100)
         |   ^
   src/mathx.cpp:8:5: note: returns 101
       8 |     return 101;
         |     ^
   Summary: 1 failed, 1 unresolved (callee.contract 1) in 0.0 s

With ``return 100;`` both verify, and the warning that ``clamp100`` has no
definition is not printed. The results of each file are held until every
file is verified, then printed in the order the files are given.

- A declaration matches a definition with the same function (its mangled
  name) and the same contract as written. A file that states another
  contract for the function does not match: its callers are unresolved, and
  the message says that the definition is verified against another
  contract.
- A contract whose proof rests on contracts of other files is established
  only once they are. Two files whose proofs rest on each other's contracts
  establish nothing, as proofs that rest on themselves never do.
- A trusted declaration stays an assumption, with ``[trusts=...]`` on what
  relies on it; only its definition, where it is verified, can find a wrong
  contract.

Files verified apart, as a build verifies each object, settle their
contracts with a check: each file records what it verifies and what it
assumes, and ``cpp-verify --check-contracts`` settles the records as one run
does. A proof that rests on a contract of another file says so, as
``[assumes=clamp100]``, and the warning that the contract has no definition
is not printed:

.. code-block:: text

   $ clang++ -fverify-contracts -fverify-contracts-out=a.o.cppverify -c src/a.cpp -o a.o -Iinclude
   Verified: scaled [backend=z3] [assumes=clamp100]
   $ clang++ -fverify-contracts -fverify-contracts-out=mathx.o.cppverify -c src/mathx.cpp -o mathx.o -Iinclude
   include/mathx.h:2:42: error: verification failed: clamp100 [...]
   $ cpp-verify --check-contracts a.o.cppverify mathx.o.cppverify
   src/a.cpp:3:5: error: the proof of scaled relies on the contract of clamp100, which its verification in src/mathx.cpp does not establish
   Contracts: 1 proof rests on contracts of other files, 1 on one not established

``cpp-verify --contracts-out=FILE`` records one file the same way. The check
exits with a non-zero status when a proof relies on a contract not
established: run it as a build's last step, beside the link.

An uncontracted, non-recursive, loop-free ``constexpr`` definition may be
lifted for use in contract expressions; a recursive one used with symbolic
arguments is rejected. It is lifted where verification uses it: in a contract, a
verified body, a type invariant, or another lifted function, so the
``constexpr`` functions of a header that nothing verified uses are never
examined. Once a ``constexpr`` function has executable ``cppverify::pre``/``cppverify::post``
clauses, it remains a modular executable function: calls must satisfy its
preconditions and cannot be used as pure contract expressions.

A lifted function's parameter or result that is a reference to a ``const``
integer stands for the value it refers to, as in ``constexpr const T
&larger(const T &a, const T &b)``. One that cannot be lifted (it reads memory
through a pointer, say) is reported, and a function that applies it is
``Unresolved`` with reason ``construct.unsupported``, naming it.

The standard library's functions are not lifted: each library writes them
its own way, and a proof would depend on which one. ``std::min`` and
``std::max`` of two integers, enumerations, or ``bool`` mean what the
standard says they mean, in contracts and in code alike: ``std::max(a, b)``
is ``a`` unless ``a < b``, and ``std::min(a, b)`` is ``a`` unless ``b < a``.

.. code-block:: cpp

   #include <algorithm>

   int lower(int a, int b)
     cv::post(cv::result == std::min(a, b))
     cv::post(cv::result <= a && cv::result <= b)
   {
     int m = std::min(a, b);
     return m;
   }

   long widened(int x)
     cv::post(cv::result >= 3)
   {
     long w = std::max<long>(x, 3L);
     return w;
   }

.. code-block:: text

   Verified: lower [backend=z3]
   Verified: widened [backend=z3]

Any other function of the standard library, such as ``std::clamp``, is an
error naming it (``std::clamp is not modeled: of the standard library, the
verifier knows std::min and std::max of two integers``), as is a reference
bound to the result of ``std::max``. Before 0.2, ``std::min`` and
``std::max`` in a contract, and every ``constexpr`` helper that could not be
lifted, ended ``Unresolved: obligation lowering failed: f (missing spec
definition: fn_...)``.

Preconditions, ``cppverify::old(parameter)``, and a parameter named in a postcondition
all denote the argument's entry value, as in ACSL, even when the callee
reassigns its by-value parameter; a caller can therefore use the
postcondition directly.

Contracts must be defined
-------------------------

A contract is C++, evaluated where the function is called and where it
returns. A clause that divides by zero or reads outside an object there says
nothing, so CppVerify checks that each clause is defined where it is
evaluated, as Dafny checks a method's well-formedness, and reports a clause
that may not be as ``contract of f``, at the operation:

- each precondition where the preconditions written before it hold, so a
  clause may rely on the ones before it, and each operand of ``&&``, ``||``,
  and ``?:`` where the operands before it allow its evaluation;
- each postcondition in the state the function returns in, where the
  postconditions before it hold. For a trusted function or one without a
  definition, that is every state its frame allows (only its
  ``cppverify::modifies`` footprints change), with any result;
- the checks an operation gets in a body: divisors, shifts, a mathematical
  value converted to a machine type, dereferences, and, with memory checking,
  every access inside its extent or object (see :doc:`pointers`). Loop
  invariants and ``cppverify::check`` get the same checks.

.. code-block:: cpp

   int average(int total, int count)
     cv::pre(total / count >= 0 && count > 0)
     cv::post(cv::result >= 0)
   {
     return total / count;
   }

   int average_checked(int total, int count)
     cv::pre(count > 0 && total / count >= 0)
     cv::post(cv::result >= 0)
   {
     return total / count;
   }

   int pick(const int *p, int i)
     cv::pre(cv::valid(p, 8) && p[i] > 0 && 0 <= i && i < 8)
     cv::post(cv::result > 0)
   {
     return p[i];
   }

   [[cppverify::trusted]] int read_sensor(int channel)
     cv::post(1000 / cv::result > 0);

   int scaled(int channel)
     cv::post(cv::result > 0)
   {
     int r = read_sensor(channel);
     return 1000 / r;
   }

.. code-block:: text

   defined.cpp:2:17: error: verification failed: contract of average [division-by-zero] [backend=z3] [reason=counterexample]
       2 |   cv::pre(total / count >= 0 && count > 0)
         |                 ^
   defined.cpp:2:17: note: counterexample: count = 0
   Verified: average [backend=z3]
   Verified: average_checked [backend=z3]
   defined.cpp:16:30: error: verification failed: contract of pick [bounds] [backend=z3] [reason=counterexample]
      16 |   cv::pre(cv::valid(p, 8) && p[i] > 0 && 0 <= i && i < 8)
         |                              ^
   defined.cpp:16:30: note: counterexample: p = 1, i = -1
   Verified: pick [backend=z3]
   defined.cpp:22:28: Trusted: read_sensor (contract assumed, not verified)
   defined.cpp:23:17: error: verification failed: contract of read_sensor [division-by-zero] [backend=z3] [reason=counterexample]
      23 |   cv::post(1000 / cv::result > 0);
         |                 ^
   defined.cpp:23:17: note: counterexample: result = 0
   Unresolved: scaled [backend=z3] [reason=callee.contract] (relies on the
     contract of read_sensor (its clauses are not shown to be defined), which is
     not established)

``average`` divides before it tests ``count``, so its precondition is undefined
at ``count == 0``; written the other way round, as in ``average_checked``, it
is defined. ``pick`` reads ``p[i]`` before it bounds ``i``. Both bodies still
verify: their proofs assume the preconditions, and a body's own operations
are checked whatever its contract says. The trusted contract of
``read_sensor`` divides by its result, which may be 0.

A contract that may be undefined establishes nothing: every caller that relies
on it is ``Unresolved`` with reason ``callee.contract``, as ``scaled`` is. Its
proof read ``1000 / r > 0`` as excluding ``r == 0``, since the logic defines a
division by zero, but C++ does not, so nothing excludes it. The function's own
verdict is about its body and does not change. The check prints nothing when it
holds. With ``--backend=lean`` it is exported as goals of its own,
``Exported: lean obligation: contract of f``; once their proofs certify,
``Certified: contract of f`` establishes the contract, and until then the
callers that rely on it are ``Unresolved`` with reason ``callee.contract``.

Spec functions stay total, as in Verus and ACSL: a spec's division by zero is
0, so applying a spec in a contract adds no check, and
``cppverify::recommends`` remains a warning (see :doc:`ghost-proofs`).

Calls in expressions
--------------------

A call of a function with a contract may stand anywhere an expression may:
an operand, a condition, an index, an argument of another call, a return
value, a loop condition. It is checked as a call statement is: its
preconditions are asserted with its arguments, it changes only its
``cppverify::modifies`` footprints, and its postconditions describe its
result. Each call runs where C++ evaluates it:

- before whatever reads its result, and a condition's calls before the
  branch the condition chooses;
- the second operand of ``&&`` and ``||``, and each branch of ``?:``, only
  on its own path, after the first operand or the condition is evaluated, so
  a callee's precondition needs to hold only where the call is made;
- a loop condition's calls at every test of the condition, the last one
  included, after the invariants hold at the head.

.. code-block:: cpp

   int inc(int x)
     cv::pre(x < 1000)
     cv::post(cv::result == x + 1)
   {
     return x + 1;
   }

   int sq(int x)
     cv::pre(-1000 <= x && x <= 1000)
     cv::post(cv::result == x * x)
   {
     return x * x;
   }

   int sum_sq(int a, int b)
     cv::pre(-100 <= a && a <= 100 && -100 <= b && b <= 100)
     cv::post(cv::result == a * a + b * b)
   {
     return sq(a) + sq(b);
   }

   int guarded(int x)
     cv::pre(-2000 <= x && x <= 2000)
     cv::post(cv::result == (-1000 <= x && x <= 1000 && x * x > 4))
   {
     if (-1000 <= x && x <= 1000 && sq(x) > 4)
       return 1;
     return 0;
   }

   int unguarded(int x)
     cv::pre(-2000 <= x && x <= 2000)
   {
     if (sq(x) > 4 && x <= 1000)
       return 1;
     return 0;
   }

   int count_up(int n)
     cv::pre(0 <= n && n < 2000)
     cv::post(cv::result == n)
   {
     int i = 0;
     while (inc(i) <= n)
       cv::invariant(0 <= i && i <= n)
       cv::decreases(n - i)
     {
       i = i + 1;
     }
     return i;
   }

.. code-block:: text

   Verified: inc [backend=z3]
   Verified: sq [backend=z3]
   Verified: sum_sq [backend=z3]
   Verified: guarded [backend=z3]
   calls.cpp:34:7: error: verification failed: unguarded [precondition] [backend=z3] [reason=counterexample]
      34 |   if (sq(x) > 4 && x <= 1000)
         |       ^
   calls.cpp:34:7: note: counterexample: x = -1001
   calls.cpp:34:7: note: calls sq(-1001)
   calls.cpp:44:10: error: verification failed: count_up [precondition] [backend=z3] [reason=counterexample]
      44 |   while (inc(i) <= n)
         |          ^
   calls.cpp:44:10: note: counterexample: n = 1000, i = 0 -> 1000
   calls.cpp:44:3: note: enters the loop
      44 |   while (inc(i) <= n)
         |   ^
   calls.cpp:44:3: note: starts an arbitrary iteration of the loop, where its condition is true
   calls.cpp:44:10: note: calls inc(1000)
      44 |   while (inc(i) <= n)
         |          ^
   note: the counterexample's state at the loop at 44:3 is any state its invariants allow, not necessarily one an execution reaches
   note: no execution fails this check within 10 iterations of each loop

``guarded`` calls ``sq`` only where ``-1000 <= x && x <= 1000`` holds, so
``sq``'s precondition holds at every call it makes. ``unguarded`` calls
``sq`` before it tests ``x``, at ``x = -1001`` among others. ``count_up``
calls ``inc`` at every test of its condition: with ``n = 1000``, the test
that would end the loop calls ``inc(1000)``, which ``inc``'s precondition
excludes. A ``for`` loop's increment and a ``continue`` behave the same way:
the increment's calls run at the end of each iteration, and the condition's
again after a ``continue``.

C++ leaves the order of most operands open: the two operands of ``+`` or
``<``, a subscript's array and index, the arguments of a call. The verifier
runs calls first, in one order, so that order must not matter. A call that
may write memory (its callee has a ``cppverify::modifies``, a pointer or
reference parameter, or is a member function that is not ``const``) next to
an operand that reads memory, or makes another call, is an error:

.. cppverify-example: label add_one

.. code-block:: cpp

   int add_one(int *p)
     cv::pre(p != nullptr && *p < 1000)
     cv::modifies(*p)
     cv::post(*p == cv::old(*p) + 1 && cv::result == *p)
   {
     *p = *p + 1;
     return *p;
   }

.. cppverify-example: with add_one
.. cppverify-example: rejects

.. code-block:: cpp

   int sum_with(int *p)
     cv::pre(p != nullptr && 0 <= *p && *p < 100)
     cv::modifies(*p)
   {
     return add_one(p) + *p;
   }

.. code-block:: text

   order.cpp:18:10: error: sum_with: C++ leaves the order of these operands open, and a call in one may write what the other reads; make the call in a statement of its own first
      18 |   return add_one(p) + *p;
         |          ^~~~~~~~~~~~~~~

Where ``*p`` is ``v`` before it, ``add_one(p) + *p`` is ``2 * v + 2`` when a
compiler evaluates the call first and ``2 * v + 1`` when it reads ``*p``
first. Write ``int a = add_one(p);`` first and use ``a + *p``, which says
which one is meant.

An assignment evaluates its right operand first (C++17), so a call in the
target runs after the value is read, and a call in the value runs before
the target is located:

.. cppverify-example: with add_one

.. code-block:: cpp

   void store_old(int *a, int *p)
     cv::pre(cv::valid(a, 4) && p != nullptr && 0 <= *p && *p < 2)
     cv::modifies(*p, a[0 : 4])
     cv::post(a[cv::old(*p) + 1] == cv::old(*p))
   {
     a[add_one(p)] = *p;
   }

.. code-block:: text

   Verified: store_old [backend=z3]

Before C++17 an assignment's operands are unsequenced too: with
``--extra-arg=-std=c++14``, ``store_old`` is ``error: store_old: before
C++17 the order of an assignment's operands is open, and a call in one may
write what the other reads; make the call in a statement of its own
first``.

A call that returns nothing is made as a statement of its own
(``note(x);``), and one that returns a record as a statement or a whole
initializer, assignment, or return value (``Pt p = make(x);``,
``return make(x);``): a record result read in a larger expression
(``make(x).y``) is still ``executable call is unsupported in this expression
context``. Before 0.2, every call inside a larger expression was that error,
and the file stopped.

Templates
---------

A function template is verified in each of its specializations, as Kani and
CBMC verify the code a program instantiates: its contract is instantiated
with its body, so the contract and every check of the body are about the
template's arguments, and each specialization gets a verdict of its own,
named with its arguments. A template value parameter is its argument, and
``if constexpr`` keeps the branch its constant condition selects:

.. code-block:: cpp

   template <int N> int scaled(int x)
     cv::pre(-1000 <= x && x <= 1000)
     cv::post(cv::result == N * x)
   {
     if constexpr (N == 0)
       return 0;
     else
       return N * x;
   }

   int scaled_sum(int x)
     cv::pre(-1000 <= x && x <= 1000)
     cv::post(cv::result == 3 * x)
   {
     return scaled<0>(x) + scaled<3>(x);
   }

.. code-block:: text

   Verified: scaled<0> [backend=z3]
   Verified: scaled<3> [backend=z3]
   Verified: scaled_sum [backend=z3]

.. cppverify-example: fails twice<short>

.. code-block:: cpp

   template <typename T>
   T twice(T x)
     cv::pre(0 <= x && x <= 30000)
     cv::post(cv::result == 2 * x)
   {
     return x + x;
   }

   int twice_int(int x)
     cv::pre(0 <= x && x <= 30000)
     cv::post(cv::result == 2 * x)
   {
     int r = twice(x);
     return r;
   }

   short twice_short(short x)
     cv::pre(0 <= x && x <= 30000)
   {
     short r = twice(x);
     return r;
   }

.. code-block:: text

   Verified: twice<int> [backend=z3]
   templates.cpp:4:23: error: verification failed: twice<short> [postcondition] [backend=z3] [reason=counterexample]
       4 |   cv::post(cv::result == 2 * x)
         |            ~~~~~~~~~~~^~~~~~~~
   templates.cpp:4:23: note: counterexample: x = 16384, result = -32768
   templates.cpp:6:3: note: returns -32768
       6 |   return x + x;
         |   ^
   templates.cpp:20:13: note: in instantiation of function template specialization 'twice<short>' requested here
      20 |   short r = twice(x);
         |             ^
   Verified: twice_int [backend=z3]
   Unresolved: twice_short [backend=z3] [reason=callee.contract] (relies on the contract of twice<short>, which is not established)

``x + x`` is an ``int``, which a ``short`` result holds only up to 32767:
``twice<short>`` fails, and the function that relies on it is unresolved.

- A specialization is verified where the translation unit instantiates it,
  by a call or by an explicit instantiation (``template long
  twice<long>(long);``). A function template with a contract that nothing
  instantiates is reported, not verified: ``warning: f: function template is
  not verified: this translation unit instantiates none of its
  specializations``. What a template means depends on the types and
  overloads its arguments bring, which C++ fixes only where it is
  instantiated.
- A diagnostic about a specialization notes where it is instantiated, as a
  compiler's does (JSON ``instantiated_at``).
- The contract is checked where it is instantiated, as a C++ condition is: a
  clause that does not fit the arguments, such as ``cv::post(cv::result ==
  v.first)`` for an ``int``, is a compiler error there, with Clang's ``in
  instantiation of function template specialization`` note. Arguments the
  contract fits are no error.
- Loop contracts, assertions, ghost code, quantifiers, and triggers are
  instantiated with the body, and so are spec function templates and member
  function templates of ordinary classes. An uncontracted ``constexpr``
  template that a contract applies is a spec in each specialization, as a
  ``constexpr`` function is (see Functions above). A contract written on a
  declaration holds for the definition after it, and a
  ``[[cppverify::trusted]]`` template without a definition holds at every
  call of its specializations.
- In a variadic template, the parameters a pack expands to are named as
  C++26 indexes a pack, ``ns...[1]``, in counterexamples too, and a fold
  over a quantifier binds a variable of its own in each element.
- A specialization the verifier cannot represent (``maxv<double>``) costs
  that specialization alone, as a construct in any function does.
- A class template is verified in each specialization too: its members'
  contracts are instantiated with the members, and its type invariants with
  the class (:doc:`structs`).
- A template without contracts changes nothing for the rest of the file, as
  long as verified code does not call it.

Before 0.2, the contracts of templates were ignored with a warning
(``-Wcontract-unsupported``, which no longer reports anything), and a call to
one from verified code was ``call to function without a verification
contract``. A template whose contract depended on its
parameters did not compile (``value of type '<dependent type>' is not
contextually convertible to 'bool'``), nor did ``cv::result`` or
``cv::old(x)`` of the template's type compared with a constant
(``cv::post(cv::result > 0)``: ``invalid operands to binary expression ('T'
and 'int')``). A template without any contract, even one nothing calls,
stopped the file with ``function template verification is unsupported``.

Behaviors
---------

A contract can be split into cases, as ACSL behaviors do.
``cppverify::behavior(name, assumes)`` starts a case; the ``cppverify::pre`` and
``cppverify::post`` clauses after it apply where its assumption holds
(``assumes`` at entry):

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
``return``, ``break``, and ``continue`` may leave a loop from any iteration.
A ``return`` checks the postcondition in its own state and a ``break``
continues after the loop in its own state. A ``continue`` ends the
iteration: the invariant must hold again and the ``cppverify::decreases``
measure must drop, after a ``for`` increment has run. In a ``do`` loop's
first iteration, which runs before the invariant holds, a ``break`` skips the
rest of the loop, and a ``continue`` goes to the condition, where the
invariant must first hold. ``cppverify::ghost`` code cannot leave an
executable loop.

A failure is relative to the loop's invariants: after the loop, and at the
start of an iteration, the verifier knows only what they say, so a
counterexample there may start from a state no execution reaches. Such a
failure says so in a note, and the verifier then unrolls each loop, up to
``--confirm-bound`` iterations (10 by default, ``0`` to skip), to look for an
execution that fails the same check, with callees still by their contracts:

.. code-block:: cpp

   namespace cv = cppverify;

   int count_up(int n)
     cv::pre(n >= 0 && n <= 5)
     cv::post(cv::result == n)
   {
     int c = 0;
     while (c < n)
       cv::decreases(n - c)
     {
       c = c + 1;
     }
     return c;
   }

.. code-block:: text

   count_up.cpp:5:23: error: verification failed: count_up [postcondition] [backend=z3] [reason=counterexample]
       5 |   cv::post(cv::result == n)
         |            ~~~~~~~~~~~^~~~
   count_up.cpp:5:23: note: counterexample: n = 0, c = 0 -> 1, result = 1
   count_up.cpp:8:3: note: enters the loop
       8 |   while (c < n)
         |   ^
   count_up.cpp:8:3: note: leaves the loop
   count_up.cpp:13:3: note: returns 1
      13 |   return c;
         |   ^
   note: the counterexample's state at the loop at 8:3 is any state its invariants allow, not necessarily one an execution reaches
   note: no execution fails this check: every loop ends within 5 iterations, and unrolling proves it there; the loops' invariants are too weak for an unbounded proof

Here the loop has no invariant, so after it ``c`` may be anything; the fix is
``cv::invariant(0 <= c && c <= n)``. When unrolling finds an execution that
fails the check (in any iteration's copy of it, for a check in the loop's
body), the note says within how many iterations and gives that execution;
when it finds neither a failure nor a proof within the bound, the note says
that no execution fails the check within that many iterations. The execution
a note gives passes the checks before this one that fail, since one that
fails an earlier check never reaches it. When the check holds in every
execution that passes them, the note says so and names an earlier check that
fails, the one to fix first (``--max-failures=0`` reports it with its own
counterexample, see :doc:`tooling`):

.. code-block:: cpp

   namespace cv = cppverify;

   int divide(int a, int n)
     cv::pre(n >= 0 && n <= 5)
     cv::post(true)
   {
     int c = 0;
     int q = 0;
     while (c < n)
       cv::invariant(0 <= c && c <= n)
       cv::decreases(n - c)
     {
       q = a / (1 - c);
       c = c + 1;
     }
     return q;
   }

.. code-block:: text

   divide.cpp:13:7: error: verification failed: divide [overflow] [backend=z3] [reason=counterexample]
      13 |     q = a / (1 - c);
         |       ^
   divide.cpp:13:7: note: counterexample: a = -2147483648, n = 3, c = 0 -> 2, q = 0
   divide.cpp:9:3: note: enters the loop
       9 |   while (c < n)
         |   ^
   divide.cpp:9:3: note: starts an arbitrary iteration of the loop, where its condition is true
   note: the counterexample's state at the loop at 9:3 is any state its invariants allow, not necessarily one an execution reaches
   note: no execution fails this check without failing an earlier one first (the division-by-zero check at 13:7 fails): those that pass the checks before it end every loop within 2 iterations, and unrolling proves it there

``INT_MIN / -1`` needs ``c == 2``, and every execution that gets there
divides by ``1 - 1`` one iteration sooner.

Unrolling keeps no invariant and no measure, so a failed invariant or
measure gets the first note only. The verdict stays ``verification failed`` either way, since
the claim is not proved. A failure of a function
whose loop has no ``cppverify::decreases`` also notes that loop: with a
proof, the function would still be ``Unresolved`` (``decreases.missing``).

A range-based ``for`` loop over an array (a local array, an array member,
a constant table) visits its elements in order. Its contract names the
position, ``cppverify::index``, the number of elements before the current
one, from 0 to the size; without a ``cppverify::decreases`` its measure is
the number of elements left, since such a loop ends. The loop variable is a
copy of the element or a reference to it:

.. code-block:: cpp

   struct Ring {
     int buf[8];
     int head;
   };

   int total(const Ring *r)
     cv::pre(r != nullptr)
     cv::pre(cv::forall(k, 0, 8, 0 <= r->buf[k] && r->buf[k] <= 10))
     cv::post(0 <= cv::result && cv::result <= 80)
   {
     int s = 0;
     for (const int &v : r->buf)
       cv::invariant(0 <= s && s <= 10 * cv::index)
       s = s + v;
     return s;
   }

   void clear(Ring *r)
     cv::pre(r != nullptr)
     cv::modifies(r->buf[0 : 8])
     cv::post(cv::forall(k, 0, 8, r->buf[k] == 0))
   {
     for (int &x : r->buf)
       cv::invariant(cv::forall(k, 0, cv::index, r->buf[k] == 0))
       x = 0;
   }

.. code-block:: text

   Verified: total [backend=z3]
   Verified: clear [backend=z3]

C++ evaluates the range once and the verifier locates each element again, so
a range located through a call, a pointer read from memory, or a variable
the body may change is rejected: copy the pointer or index into a variable
the body does not change. The contract holds at the head, where the loop
variable is not declared, so it cannot name it. A range over a class,
through its ``begin`` and ``end``, an array of arrays, and a global array
that is not a constant table are not supported yet.

A condition may declare a variable, ``while (int k = next(i))``: it is
declared, and its value tested, at every test, so a loop's contract cannot
name it. A ``for`` loop without a condition repeats until a ``break`` or
``return`` leaves it, and needs a measure like any other. A comma
expression as a statement, such as the increment ``i++, j += 2``, runs its
operands in order.

The verifier checks a loop **modularly** (no unrolling), discharging four
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
``decreases.missing``, unless its condition is the constant false, so that it
never repeats (``while (false)``, the ``do { ... } while (0)`` of a macro).
Such a loop keeps the state it starts in. ``cppverify::decreases(*)`` allows a
loop (or an executable function) to diverge; its function and every caller
are then reported ``Verified ... [partial]``, proved only for the executions
that terminate. Ghost-block and proof-function loops are erased at runtime and
must have a real measure, unless their condition is the constant false;
``cppverify::decreases(*)`` is rejected there.

A loop whose condition is the constant false runs its body at most once (a
``do`` loop exactly once), so it needs no invariant or measure, and the state
after it is the one its body leaves. This is the shape of the usual
statement-like macro:

.. code-block:: cpp

   #define SWAP(a, b) do { int t = a; a = b; b = t; } while (0)

   int swapped_difference(int a, int b)
     cv::pre(0 <= a && a <= 1000 && 0 <= b && b <= 1000)
     cv::post(cv::result == b - a)
   {
     SWAP(a, b);
     return a - b;
   }

.. code-block:: text

   Verified: swapped_difference [backend=z3]

Before 0.2, such a loop was treated like any other: what it might change was
forgotten after it, so ``a - b`` failed with an ``overflow`` counterexample
for values the swap never produces.

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
   warning: collatz_steps: proved only for executions that terminate: cppverify::decreases(*) at 7:19 allows it to diverge
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

Local and dynamic objects follow the same rule. A store through a local
array, a local record, or a ``new`` pointer writes that object, a store or a
call through a reference to a local writes the cell it binds, and every
other object keeps its value:

.. cppverify-example: fails overwritten

.. code-block:: cpp

   int other_array()
     cv::post(cv::result == 7)
   {
     int a[3];
     int b[2];
     b[0] = 3;
     b[1] = 4;
     for (int i = 0; i < 3; i = i + 1)
       cv::invariant(0 <= i && i <= 3)
       cv::decreases(3 - i)
     {
       a[i] = 0;
     }
     return b[0] + b[1];
   }

   int overwritten()
     cv::post(cv::result == 7)
   {
     int a[4];
     a[3] = 7;
     for (int i = 0; i < 4; i = i + 1)
       cv::invariant(0 <= i && i <= 4)
       cv::decreases(4 - i)
     {
       a[i] = 0;
     }
     return a[3];
   }

.. code-block:: text

   Verified: other_array [backend=z3]
   frames.cpp:18:23: error: verification failed: overwritten [postcondition] [backend=z3] [reason=counterexample]
      18 |   cv::post(cv::result == 7)
         |            ~~~~~~~~~~~^~~~
   frames.cpp:18:23: note: counterexample: i = 0 -> 4, result = -2147483648
   frames.cpp:20:3: note: creates a local object at address 4
      20 |   int a[4];
         |   ^
   frames.cpp:21:8: note: stores 7 at address 16
      21 |   a[3] = 7;
         |        ^
   frames.cpp:22:3: note: enters the loop
      22 |   for (int i = 0; i < 4; i = i + 1)
         |   ^
   frames.cpp:22:3: note: leaves the loop
   frames.cpp:28:3: note: returns -2147483648
      28 |   return a[3];
         |   ^
   note: the counterexample's state at the loop at 22:3 is any state its invariants allow, not necessarily one an execution reaches
   note: an execution fails this check within 4 iterations of each loop (counterexample: i = 0 -> 1 -> 2 -> 3 -> 4, result = 0)

``overwritten`` fails because the loop writes ``a[3]``, which no invariant
describes. Before 0.2 a loop that wrote local or dynamic storage forgot the
value of every object, so ``other_array`` failed its postcondition.

After a normal exit the verifier knows ``I && !c`` about what the loop may
change; variables the loop does not assign and memory outside its write set
keep their values. A ``break`` or ``return`` leaves in its own state instead.

An invariant holds together with its definedness: establishment and
preservation check that what it reads is in bounds and initialized, and that
its shifts and divisions are defined, so the head of every iteration knows
both. A loop that fills a local array states what it has written, and the
reads that state it are what show those elements initialized, which no
contract can say directly:

.. cppverify-example: fails partially_filled

.. code-block:: cpp

   int filled()
     cv::post(cv::result == 0)
   {
     int a[4];
     for (int i = 0; i < 4; i = i + 1)
       cv::invariant(0 <= i && i <= 4)
       cv::invariant(cv::forall(k, 0, i, a[k] == 0))
       cv::decreases(4 - i)
     {
       a[i] = 0;
     }
     return a[3];
   }

   int partially_filled()
   {
     int a[4];
     for (int i = 0; i < 3; i = i + 1)
       cv::invariant(0 <= i && i <= 3)
       cv::invariant(cv::forall(k, 0, i, a[k] == 0))
       cv::decreases(3 - i)
     {
       a[i] = 0;
     }
     return a[3];
   }

.. code-block:: text

   Verified: filled [backend=z3]
   fill.cpp:25:3: error: verification failed: partially_filled [initialization] [backend=z3] [reason=counterexample]
      25 |   return a[3];
         |   ^
   fill.cpp:25:3: note: counterexample: i = 0 -> 3
   fill.cpp:17:3: note: creates a local object at address 9132
      17 |   int a[4];
         |   ^
   fill.cpp:18:3: note: enters the loop
      18 |   for (int i = 0; i < 3; i = i + 1)
         |   ^
   fill.cpp:18:3: note: leaves the loop
   note: the counterexample's state at the loop at 18:3 is any state its invariants allow, not necessarily one an execution reaches
   note: an execution fails this check within 3 iterations of each loop (counterexample: i = 0 -> 1 -> 2 -> 3)

No lifetime begins or ends inside a loop, so what was initialized before it
stays initialized in every iteration and after it; an element the loop may
write is initialized at its head only where an invariant reads it. Before
0.2 the head kept the initialization of the state before the loop: every
iteration after the first saw the elements the earlier ones wrote as
uninitialized, and ``filled`` failed its ``initialization`` check.

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

Assertions and calls that do not return
---------------------------------------

``assert(c)`` must not fail: reaching a failed assert, or any call that does
not return (``abort``, ``exit``, ``std::terminate``, ``__builtin_unreachable``,
``__builtin_trap``, a ``[[noreturn]]`` function), is a failure of kind
``unreachable``, as Frama-C proves an ``assert`` and Kani a panic unreachable.
The path ends there, so after ``assert(c)`` the condition holds. With
``NDEBUG``, ``assert(c)`` is nothing, as compiled, and proves nothing.

.. cppverify-example: fails aborts

.. code-block:: cpp

   #include <cassert>
   #include <cstdlib>

   int scaled(int x)
     cv::pre(0 < x && x < 1000)
     cv::post(cv::result == 2 * x)
   {
     assert(x > 0 && "x must be positive");
     return x + x;
   }

   int aborts(int x)
     cv::post(cv::result >= 0)
   {
     if (x < 0)
       abort();
     return x;
   }

.. code-block:: text

   Verified: scaled [backend=z3]
   aborts.cpp:16:5: error: verification failed: aborts [unreachable] [backend=z3] [reason=counterexample]
      16 |     abort();
         |     ^
   aborts.cpp:16:5: note: counterexample: x = -1
   aborts.cpp:15:3: note: takes the true branch
      15 |   if (x < 0)
         |   ^

An uncontracted ``constexpr`` helper's ``assert(c)`` is a requirement of each
call that reaches it, checked at the call as the helper's undefined
operations are. ``[[assume(e)]]`` and ``__builtin_assume(e)`` make ``e``
false undefined, so ``e`` is proved where it stands, then holds. A
statement that only computes a value, ``x + 1;``, is computed, with its
checks, and the operands of a discarded ``&&``, ``||``, or ``?:`` run on
their paths, which is how ``assert`` expands on every platform.

Before 0.2, ``assert`` stopped verification of its function (``unsupported
statement: ParenExpr``), and so did a call to ``abort`` (``call to function
without a verification contract``).

Switch statements
-----------------

A ``switch`` runs from the label its value matches, or from ``default`` when
no case matches, to the end of its body or to a ``break``; a label's
statements without a ``break`` fall through to the next label's, with or
without ``[[fallthrough]]``. The value is computed once, after the init
statement and the condition variable when there are any, and each case value
has the promoted type of the condition, as in C++. A case holds any
statements, loops and nested switches included: a ``break`` in a nested loop
leaves that loop, and a ``continue`` in a switch continues the loop around
it. A GNU case range, ``case 1 ... 9:``, matches each value from its first to
its last.

.. code-block:: cpp

   int bonus(int level)
     cv::post(level == 0 ? cv::result == 3 : true)
     cv::post(level == 1 ? cv::result == 1 : true)
     cv::post(level < 0 || level > 1 ? cv::result == 0 : true)
   {
     int points = 0;
     switch (level) {
     case 0:
       points = points + 2;
       [[fallthrough]];
     case 1:
       points = points + 1;
       break;
     default:
       break;
     }
     return points;
   }

.. code-block:: text

   Verified: bonus [backend=z3]

Each label's statements keep their checks, on the path that reaches them,
and a value is initialized after a switch only where every way out of it
initializes it: the end of the last label's statements, each ``break``, and,
without a ``default`` label, a value no case matches. An enumeration without
a fixed underlying type holds every value of its range ([dcl.enum]/8), so a
switch over its enumerators may match none:

.. cppverify-example: fails channel

.. code-block:: cpp

   enum Color { Red, Green, Blue };

   int channel(Color c)
     cv::post(cv::result >= 0)
   {
     switch (c) {
     case Red:
       return 0;
     case Green:
       return 1;
     case Blue:
       return 2;
     }
     return -1;
   }

.. code-block:: text

   channel.cpp:4:23: error: verification failed: channel [postcondition] [backend=z3] [reason=counterexample]
       4 |   cv::post(cv::result >= 0)
         |            ~~~~~~~~~~~^~~~
   channel.cpp:4:23: note: counterexample: c = 3, result = -1
   channel.cpp:7:3: note: takes the false branch
       7 |   case Red:
         |   ^
   channel.cpp:9:3: note: takes the false branch
       9 |   case Green:
         |   ^
   channel.cpp:11:3: note: takes the false branch
      11 |   case Blue:
         |   ^
   channel.cpp:14:3: note: returns -1
      14 |   return -1;
         |   ^

``Color`` holds 0 to 3, the values of the smallest bit-field that fits its
enumerators, and ``channel(Color(3))`` is defined C++ that returns -1.

A switch is lowered to the statements the verifier already has: the value
in a variable, a flag set when a label matches and kept through the labels
after it, and a flag for ``break`` that the statements after a ``break``
test, as BMC lowers a loop's exits. Specs, lifted ``constexpr`` helpers,
proof functions, and ghost code may switch too. What stays unsupported is
reported where it is, and costs its function alone:

- a label inside another statement of its switch, as in Duff's device
  (``a case label inside another statement of its switch is unsupported``);
- a local whose address is used, declared directly in a switch's body, which
  a later label enters without declaring it: declare it in a block after its
  label, ``case 1: { int t; f(&t); break; }``;
- ``[[assume(e)]]``, whose ``e`` false is undefined. Other statement
  attributes (``[[likely]]``, ``[[fallthrough]]``) change nothing.

Before 0.2, a ``switch`` stopped verification of its function with
``unsupported statement: SwitchStmt``, and ``break`` and ``continue`` in a
``do`` loop, a condition declaration, a ``for`` loop without a condition, and
a comma statement did the same.
