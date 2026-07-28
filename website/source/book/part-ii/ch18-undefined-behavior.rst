Chapter 18 — Undefined behavior
===============================

Proving a function meets its postcondition is only half of what "correct" means
for runtime C++. The other half is that the function is **well-defined** in the
first place — that it never executes undefined behavior (UB). This chapter is
about the second obligation. Core expression definedness is always on;
``--check-ub`` additionally enables declared buffer-extent checks.

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

Machine values use bit-vectors, whose arithmetic wraps. If the verifier checked
only the final equality, this would be a tautology even on an overflowing path:

.. code-block:: cpp

   int add(int a, int b) post(result == a + b) { return a + b; }

CppVerify therefore inserts a signed-overflow assertion before each evaluated
addition. The function fails without any optional flag when the precondition
admits overflow. Bit-vectors still model the machine result faithfully, but
definedness must be established before that result can justify a contract.

Core safety and the bounds option
---------------------------------

.. code-block:: bash

   cpp-verify            file.cpp     # contracts + core expression definedness
   cpp-verify --check-ub file.cpp     # additionally use valid(p,n) extents

Always-on checks cover signed arithmetic and negation overflow, zero divisors,
the signed-minimum divided by minus one case, invalid shifts, and non-null
abstract-valid dereferences. They also follow operations executed inside lifted
``constexpr`` functions.

The historically named ``--check-ub`` option is now specifically the Z3/BMC
extent rollout: it discovers ``valid(p, n)`` before that marker's trivial spec
body is inlined and generates access, modular-slice, and same-array-position
obligations. It does not control the always-on checks above.

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

   int abs(int x) post(result >= 0)
   { return x < 0 ? -x : x; }
   //   FAILS: counterexample x = INT_MIN  (negating INT_MIN overflows)

   int abs(int x) pre(x > -2147483648) post(result >= 0)
   { return x < 0 ? -x : x; }
   //   verifies

Array out-of-bounds
-------------------

Reading or writing past the end of a buffer is the most consequential memory UB
(it is the buffer-overflow CVE class). To check it, declare the buffer's length
with ``valid(p, n)`` in a precondition; then every ``p[i]`` / ``*(p+i)`` access
whose base is ``p`` carries the obligation ``0 <= i < n``:

.. code-block:: cpp

   spec bool valid(int* p, int n) { return true; }   // length marker

   int get(int* p, int n, int i)
     pre(valid(p, n) && 0 <= i && i < n)              // in bounds -> verifies
     post(result == p[i])
   { return p[i]; }

   int last(int* p, int n)
     pre(valid(p, n) && n >= 1)
   { return p[n]; }   // --check-ub -> FAILS: p[n] is one past the end

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
copy loop is proven memory-safe from its guard and invariant. An access through a
pointer with **no** ``valid`` declaration is not bounds-checked because the
verifier has no length to use. Its non-null/abstract-valid dereference
obligation still applies.

Signed vs. unsigned
-------------------

This distinction is load-bearing. **Signed** overflow is UB in C++ and is
checked. **Unsigned** overflow is *defined* modular wraparound, so it is **never
flagged**:

.. code-block:: cpp

   unsigned mix(unsigned a, unsigned b) post(result == a + b)
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
initialization, and (with ``--check-ub``) declared-buffer bounds. The bounded
local scalar ``new``/``delete`` subset additionally checks initialized heap
reads, live dereferences, exact-base deletion, double deletion, target
alignment, and non-overlap of simultaneous allocations.

General pointer provenance, arrays, strict aliasing, placement construction,
and subobject lifetime remain outside the model. Parameter buffers use
abstract validity/initialization assumptions rather than concrete caller
allocation state. See :doc:`ch19-dynamic-storage` and the full layering plan in
``docs/UB-CHECKING.md``.
