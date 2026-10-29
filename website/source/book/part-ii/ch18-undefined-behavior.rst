Chapter 18 — Undefined behavior
===============================

Proving a function meets its postcondition is only half of what "correct" means
for runtime C++. The other half is that the function is **well-defined** in the
first place — that it never executes undefined behavior (UB). This chapter is
about the second obligation. Core expression definedness is always on, and
memory checking is on by default (``--no-check-ub`` turns it off).

Two obligations, not one
------------------------

For an executable function with ``cppverify::pre``/``cppverify::post`` there are really two things to
prove:

#. **Safety** — every operation is well-defined (no UB).
#. **Functional** — ``pre ∧ code ⇒ post``.

The functional obligation is **meaningless without the safety one**. If the code
can execute UB, the real program has *no* defined behavior at all, so a proof of
``cppverify::post`` against any model says nothing about the binary. UB-freedom comes first.

And it is the **tool's** job to generate the safety obligations — not yours. You
write ``cppverify::pre`` and ``cppverify::post``; the verifier derives "this operation must not
overflow / must not divide by zero" from the code. If your precondition is too
weak to rule the UB out, it reports the exact counterexample.

Why functional verification alone would be blind
-------------------------------------------------

Machine arithmetic wraps modulo ``2^N``. A proof about the wrapped value of
an overflowing addition would describe an execution C++ does not define:

.. cppverify-example: fails add

.. code-block:: cpp

   int add(int a, int b) cv::post(cv::result == a + b) { return a + b; }

CppVerify therefore inserts a signed-overflow assertion before each evaluated
addition, and this function fails at the addition when the precondition admits
overflow. (In the contract, ``a + b`` is the exact mathematical sum, as in
ACSL and Verus, so the postcondition alone would also expose the problem.)
The machine result is still modeled faithfully, but definedness must be
established before that result can justify a contract.

Core safety and memory checking
-------------------------------

.. code-block:: bash

   cpp-verify               file.cpp  # contracts, definedness, memory checks
   cpp-verify --no-check-ub file.cpp  # without the memory checks

Always-on checks cover signed arithmetic and negation overflow, zero divisors,
the signed-minimum divided by minus one case, invalid shifts, conversions to an
enumeration outside its value range, non-null abstract-valid dereferences,
uses of storage after its lifetime ends (a read through a pointer after
``delete``), and reads of a local before it is written: a local that some path
may read uninitialized is an error (``read of uninitialized local value: x``).
They also follow operations executed inside lifted ``constexpr`` functions.

Memory checking, the default on every backend (``--check-ub``), proves that
each access and each pointer step stays in its object. It discovers
``valid(p, n)`` before that marker's trivial spec body is inlined.
``--no-check-ub`` turns it off; it does not control the always-on checks
above.

What is always checked
----------------------

.. list-table::
   :header-rows: 1
   :widths: 42 58

   * - Operation
     - Obligation
   * - signed ``+`` ``-`` ``*``, unary ``-``
     - does not overflow (at the operand's bit width)
   * - ``/`` ``%``
     - divisor ``!= 0``
   * - signed ``/`` ``%``
     - not ``INT_MIN / -1``
   * - ``<<`` / ``>>``
     - valid count; before C++20, a signed left shift also follows the C++17
       rule (see :doc:`../../language/integers`)
   * - conversion to an enumeration without a fixed underlying type
     - the value lies in the enumeration's range
   * - ``*p``, ``p[i]``, ``p->field``
     - base is non-null and satisfies the abstract validity predicate; storage
       from ``new`` or an addressed local is live and initialized

The classic example — the tool tells you the precondition you forgot:

.. code-block:: cpp

   int abs_unguarded(int x) cv::post(cv::result >= 0)
   { return x < 0 ? -x : x; }

   int abs_guarded(int x) cv::pre(x > -2147483648) cv::post(cv::result >= 0)
   { return x < 0 ? -x : x; }

.. code-block:: text

   abs.cpp:2:18: error: verification failed: abs_unguarded [overflow] [backend=z3] [reason=counterexample]
       2 | { return x < 0 ? -x : x; }
         |                  ^~
   abs.cpp:2:18: note: counterexample: x = -2147483648
   Verified: abs_guarded [backend=z3]

Negating ``INT_MIN`` overflows, so the first version fails at that input;
the second states the precondition the counterexample points to.

Array out-of-bounds
-------------------

Reading or writing past the end of a buffer is the most consequential memory UB
(it is the buffer-overflow CVE class). A C++ function receives a buffer as a
pointer and a length, and nothing in the type connects them. The contract
does: ``valid(p, n)`` in a precondition says that ``p`` points to ``n``
objects, ``p[0]`` to ``p[n - 1]``. Every ``p[i]`` / ``*(p+i)`` access whose
base is ``p`` then carries the obligation ``0 <= i < n``:

.. code-block:: cpp

   using cppverify::valid;

   int get(const int* p, int n, int i)
     cv::pre(valid(p, n) && 0 <= i && i < n)              // in bounds -> verifies
     cv::post(cv::result == p[i])
   { return p[i]; }

   int last(const int* p, int n)
     cv::pre(valid(p, n) && n >= 1)
   { return p[n]; }   // FAILS: p[n] is one past the end

.. code-block:: text

   Verified: get [backend=z3]
   example.cpp:10:10: error: verification failed: last [bounds] [backend=z3] [reason=counterexample]
      10 | { return p[n]; }   // FAILS: p[n] is one past the end
         |          ^
   example.cpp:10:10: note: counterexample: p = 1, n = 1

``<cppverify.h>`` declares ``valid`` for every pointee type, so the same
marker describes an ``int`` buffer, a ``char`` buffer, or an array of
structs. Like the header's spec collections it exists only for
verification: Sema rejects it in executable code. Programs written before
the header declare the marker themselves, and that still works; a ``cppverify::spec``
function named ``valid`` taking a pointer and an integer is the same marker:

.. code-block:: cpp

   cv::spec bool valid(const long* p, int n) { return true; }   // one per type

   long last_long(const long* p, int n)
     cv::pre(valid(p, n) && n >= 1)
   { return p[n - 1]; }   // verifies

The marker also entails ``n >= 0``. For ``n > 0``, ``p`` must be non-null and
abstractly valid; ``n == 0`` permits null. This prevents a contradictory
negative extent or a nonempty null buffer from becoming a proof assumption.
Typed pointer offsets are scaled to target bytes using ``sizeof(T)`` while this
obligation remains the half-open element bound ``0 <= i < n``.

For sound discovery, ``valid(p, n)`` must be a positive top-level conjunction
clause, ``p`` must be the bare complete-object pointer or a pointer field of
a parameter's object (``s->data``), and each pointer may have only one
marker. Shifted, disjunctive, conditional, or duplicate markers
are rejected instead of being interpreted as unconditional extents.

At a modular call, a callee extent ``valid(q, length)`` is instantiated by an
argument only after proving that its ``length`` elements are contained in one
of the caller's objects; for ``q = p + offset``, that the subrange is
nonnegative and contained in the caller's extent. The same inclusive ``[0, n]`` position proof governs
same-array pointer subtraction, while dereferences keep the half-open
``[0, n)`` access rule. Pointer differences additionally prove that the element
distance is representable by target ``ptrdiff_t``.

Inside a loop the bound is discharged the same way an invariant is — a fill or
copy loop is proven memory-safe from its guard and invariant.

A pointer with **no** ``valid`` declaration addresses a single object, as
Frama-C's ``\valid`` guards and Verus permissions require:

.. cppverify-example: fails second

.. code-block:: cpp

   int second(int* p)
     cv::pre(p != nullptr)
   { return p[1]; }   // FAILS: p addresses one int

Pointer arithmetic itself must stay within the object's closed range
``[0, n]`` (the one-past position included), because forming a pointer
further out is already undefined:

.. cppverify-example: fails far

.. code-block:: cpp

   int far(int* p)
     cv::pre(valid(p, 2))
   {
     int *q = p + 10;   // FAILS: outside [0, 2]
     return 0;
   }

The object of a pointer is the one it came from, its *origin*: arithmetic
keeps it, assignment copies it, and branches and loops join the
possibilities (:doc:`../../language/pointers`). A pointer stepped one past the
end of ``p`` cannot be dereferenced even where another object starts. When
the origin is unknown (a pointer loaded from memory), the object may be any
parameter's object, or the object at a base known to be valid, such as a
callee's result.

Enumeration values
------------------

A conversion to an enumeration without a fixed underlying type must produce a
value in the enumeration's range (C++17 [dcl.enum]); for ``enum Color { Red,
Green }`` that is ``0`` or ``1``:

.. cppverify-example: fails pick

.. code-block:: cpp

   enum Color { Red, Green };

   Color pick(int k)
     cv::pre(k >= 0 && k <= 5)
   { return (Color)k; }   // FAILS: k = 2 is not a Color

Builtins
--------

A builtin can be undefined for an argument too. GCC leaves the count of the
leading or trailing zero bits of 0 undefined, so ``__builtin_clz(x)`` and
``__builtin_ctz(x)`` must not see ``x == 0``, an obligation of kind
``builtin-argument`` at the call:

.. cppverify-example: fails lowest

.. code-block:: cpp

   int lowest(unsigned x)
     cv::post(cv::result < 32)
   { return __builtin_ctz(x); }   // FAILS: x = 0

The other bit builtins, ``__builtin_popcount``, ``__builtin_parity``,
``__builtin_ffs``, and ``__builtin_bswap*``, are defined for every argument
(see :doc:`../../language/functions-loops`).

Signed vs. unsigned
-------------------

This distinction is load-bearing. **Signed** overflow is UB in C++ and is
checked. **Unsigned** overflow is *defined* modular wraparound, so it is **never
flagged**. Contract arithmetic is exact, so a contract about the wrapped
value says so with ``% 2^N``:

.. code-block:: cpp

   unsigned mix(unsigned a, unsigned b) cv::post(cv::result == (a + b) % 4294967296)
   { return a + b; }            // verifies: unsigned wrapping is legal

Width follows the target
------------------------

Overflow is checked at the type's real bit width (from the target data model):
``int`` at 32 bits, ``long`` / ``long long`` at 64. So a sum that overflows
``int`` but fits ``long`` is correctly accepted at ``long``:

.. code-block:: cpp

   long sum(long a, long b)
     cv::pre(a == 2000000000 && b == 2000000000)
     cv::post(cv::result == 4000000000)        // 4e9 > INT_MAX, fits in int64
   { return a + b; }                   // verifies — long is modeled at 64-bit

Mixed ``int``/``long`` arithmetic sign-extends the narrower operand, just like
C++.

Loops and branches
------------------

UB obligations are **path-guarded** and checked **per iteration**. An overflow
that can only happen on a branch you never take, or after an early ``return``
that excludes the bad input, is not reported. Inside a loop, the obligation is
checked in the inductive step — so an accumulator that can overflow on some
iteration is caught even though the first few iterations are fine. (The fix is
the same as for any loop: an invariant that bounds the accumulator. See
:doc:`ch12-loops-in-practice`.)

Contracts are C++ too
---------------------

A contract is evaluated as C++ where the function is called and where it
returns, so it must be defined there, just as the body must. A precondition
that divides by ``items`` before it says ``items > 0`` is undefined for the
very input it means to exclude:

.. code-block:: cpp

   int per_item(int total, int items)
     cv::pre(total / items <= 100 && items > 0)
     cv::post(cv::result <= 100)
   {
     return total / items;
   }

.. code-block:: text

   per.cpp:2:17: error: verification failed: contract of per_item [division-by-zero] [backend=z3] [reason=counterexample]
       2 |   cv::pre(total / items <= 100 && items > 0)
         |           ~~~~~~^~~~~~~
   per.cpp:2:17: note: counterexample: items = 0
   Verified: per_item [backend=z3]

The body verifies, since its proof assumes the precondition. The contract does
not: a clause is checked where the clauses and operands before it hold, so
``cv::pre(items > 0 && total / items <= 100)`` is defined. A postcondition is
checked the same way in the state the function returns in, and a trusted
contract in every state it allows. Callers do not rely on a contract that may
be undefined; see :doc:`../../language/functions-loops`.

Asserts and calls that do not return
------------------------------------

An ``assert`` is not undefined behavior when it fails: the program aborts.
But a verified function should never abort, so a failed ``assert``, and any
call that does not return (``abort``, ``exit``, ``std::terminate``,
``__builtin_unreachable``), is an obligation of its own, of kind
``unreachable``: no execution may reach it. After ``assert(c)``, ``c``
therefore holds, and an assert documents a fact the proof checks. With
``NDEBUG`` an ``assert`` is nothing, as compiled:

.. cppverify-example: fails ratio

.. code-block:: cpp

   #include <cassert>

   int ratio(int total, int parts)
     cv::pre(0 <= total && total <= 1000)
     cv::post(cv::result >= 0)
   {
     assert(parts > 0 && "parts must be positive");
     return total / parts;
   }

.. code-block:: text

   ratio.cpp:7:3: error: verification failed: ratio [unreachable] [backend=z3] [reason=counterexample]
       7 |   assert(parts > 0 && "parts must be positive");
         |   ^
   /usr/include/assert.h:105:9: note: expanded from macro 'assert'
     105 |       : __assert_fail (#expr, __ASSERT_FILE, __ASSERT_LINE,             \
         |         ^
   ratio.cpp:7:3: note: counterexample: total = 0, parts = 0
   ratio.cpp:7:3: note: takes the false branch

The division needs ``parts != 0``, which the assert establishes, and the
assert can fail: a caller may pass ``parts == 0``. Adding
``cv::pre(parts > 0)`` makes both hold.

What is not covered yet
-----------------------

Checked today: core expression definedness, local scalar/flat-record definite
initialization, object bounds of accesses and pointer arithmetic, enumeration
ranges, and bounded local fixed arrays (element bounds and per-element
initialization). The bounded
local scalar ``new``/``delete`` subset additionally checks initialized heap
reads, live dereferences, exact-base deletion, double deletion, target
alignment, and non-overlap of simultaneous allocations.

General pointer provenance, array allocation (``new[]``) and arrays other
than bounded local fixed arrays, strict aliasing, placement construction, and
subobject lifetime remain outside the model. Parameter buffers use
abstract validity/initialization assumptions rather than concrete caller
allocation state. See :doc:`ch19-dynamic-storage` and the full layering plan in
``docs/UB-CHECKING.md``.
