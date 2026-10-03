Chapter 18 — Undefined behavior
===============================

Proving a function meets its postcondition is only half of what "correct" means
for runtime C++. The other half is that the function is **well-defined** in the
first place — that it never executes undefined behavior (UB). This chapter is
about the second obligation. Core expression definedness is always on, and
memory checking is on by default (``--no-check-ub`` turns it off).

Two obligations, not one
------------------------

For an ``exec`` function with ``pre``/``post`` there are really two things to
prove:

#. **Safety** — every operation is well-defined (no UB).
#. **Functional** — ``pre ∧ code ⇒ post``.

The functional obligation is **meaningless without the safety one**. If the code
can execute UB, the real program has *no* defined behavior at all, so a proof of
``post`` against any model says nothing about the binary. UB-freedom comes first.

And it is the **tool's** job to generate the safety obligations — not yours. You
write ``pre`` and ``post``; the verifier derives "this operation must not
overflow / must not divide by zero" from the code. If your precondition is too
weak to rule the UB out, it reports the exact counterexample.

Why functional verification alone would be blind
-------------------------------------------------

Machine arithmetic wraps modulo ``2^N``. A proof about the wrapped value of
an overflowing addition would describe an execution C++ does not define:

.. cppverify-example: fails add

.. code-block:: cpp

   int add(int a, int b) post(result == a + b) { return a + b; }

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
the signed-minimum divided by minus one case, invalid shifts, and non-null
abstract-valid dereferences. They also follow operations executed inside lifted
``constexpr`` functions.

Memory checking, the default on every backend (``--check-ub``), proves that
each access and each pointer step stays in its object, and that a conversion
to an enumeration lands in its value range. It discovers ``valid(p, n)``
before that marker's trivial spec body is inlined. ``--no-check-ub`` turns it
off; it does not control the always-on checks above.

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
     - valid count; signed left operand/range follows C++17 rules
   * - ``*p``, ``p[i]``, ``p->field``
     - base is non-null and satisfies the abstract validity predicate

The classic example — the tool tells you the precondition you forgot:

.. code-block:: cpp

   int abs_unguarded(int x) post(result >= 0)
   { return x < 0 ? -x : x; }

   int abs_guarded(int x) pre(x > -2147483648) post(result >= 0)
   { return x < 0 ? -x : x; }

.. code-block:: text

   abs.cpp:2:3: error: verification failed: abs_unguarded [...::overflow@2:3]
     (counterexample: x [type=i32] = -2147483648)
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

   #include <cppverify.h>
   using cppverify::valid;

   int get(const int* p, int n, int i)
     pre(valid(p, n) && 0 <= i && i < n)              // in bounds -> verifies
     post(result == p[i])
   { return p[i]; }

   int last(const int* p, int n)
     pre(valid(p, n) && n >= 1)
   { return p[n]; }   // FAILS: p[n] is one past the end

.. code-block:: text

   Verified: get [backend=z3]
   error: verification failed: last [...::bounds@11:10] (counterexample:
     n = 1, p = 1)

``<cppverify.h>`` declares ``valid`` for every pointee type, so the same
marker describes an ``int`` buffer, a ``char`` buffer, or an array of
structs. Like the header's spec collections it exists only for
verification: Sema rejects it in executable code. Programs written before
the header declare the marker themselves, and that still works; a ``spec``
function named ``valid`` taking a pointer and an integer is the same marker:

.. code-block:: cpp

   spec bool valid(const long* p, int n) { return true; }   // one per type

   long last_long(const long* p, int n)
     pre(valid(p, n) && n >= 1)
   { return p[n - 1]; }   // verifies

The marker also entails ``n >= 0``. For ``n > 0``, ``p`` must be non-null and
abstractly valid; ``n == 0`` permits null. This prevents a contradictory
negative extent or a nonempty null buffer from becoming a proof assumption.
Typed pointer offsets are scaled to target bytes using ``sizeof(T)`` while this
obligation remains the half-open element bound ``0 <= i < n``.

For sound discovery, ``valid(p, n)`` must be a positive top-level conjunction
clause, ``p`` must be the bare complete-object pointer, and each pointer may
have only one marker. Shifted, disjunctive, conditional, or duplicate markers
are rejected instead of being interpreted as unconditional extents.

At a modular call, a callee extent ``valid(q, length)`` may be instantiated by
``q = p + offset`` only after proving the subrange is nonnegative and contained
in the caller's extent. The same inclusive ``[0, n]`` position proof governs
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
     pre(p != nullptr)
   { return p[1]; }   // FAILS: p addresses one int

Pointer arithmetic itself must stay within the object's closed range
``[0, n]`` (the one-past position included), because forming a pointer
further out is already undefined:

.. cppverify-example: fails far

.. code-block:: cpp

   int far(int* p)
     pre(valid(p, 2))
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
     pre(k >= 0 && k <= 5)
   { return (Color)k; }   // FAILS: k = 2 is not a Color

Signed vs. unsigned
-------------------

This distinction is load-bearing. **Signed** overflow is UB in C++ and is
checked. **Unsigned** overflow is *defined* modular wraparound, so it is **never
flagged**. Contract arithmetic is exact, so a contract about the wrapped
value says so with ``% 2^N``:

.. code-block:: cpp

   unsigned mix(unsigned a, unsigned b) post(result == (a + b) % 4294967296)
   { return a + b; }            // verifies: unsigned wrapping is legal

Width follows the target
------------------------

Overflow is checked at the type's real bit width (from the target data model):
``int`` at 32 bits, ``long`` / ``long long`` at 64. So a sum that overflows
``int`` but fits ``long`` is correctly accepted at ``long``:

.. code-block:: cpp

   long sum(long a, long b)
     pre(a == 2000000000 && b == 2000000000)
     post(result == 4000000000)        // 4e9 > INT_MAX, fits in int64
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

What is not covered yet
-----------------------

Checked today: core expression definedness, local scalar/flat-record definite
initialization, object bounds of accesses and pointer arithmetic, and
enumeration ranges. The bounded
local scalar ``new``/``delete`` subset additionally checks initialized heap
reads, live dereferences, exact-base deletion, double deletion, target
alignment, and non-overlap of simultaneous allocations.

General pointer provenance, arrays, strict aliasing, placement construction,
and subobject lifetime remain outside the model. Parameter buffers use
abstract validity/initialization assumptions rather than concrete caller
allocation state. See :doc:`ch19-dynamic-storage` and the full layering plan in
``docs/UB-CHECKING.md``.
