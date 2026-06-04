Chapter 18 — Undefined behavior
===============================

Proving a function meets its postcondition is only half of what "correct" means
for runtime C++. The other half is that the function is **well-defined** in the
first place — that it never executes undefined behavior (UB). This chapter is
about the second obligation and the ``--check-ub`` flag that turns it on.

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

Why functional verification alone is blind
-------------------------------------------

By default, machine arithmetic *wraps* in the model. So this verifies:

.. code-block:: cpp

   int add(int a, int b) post(result == a + b) { return a + b; }

Under wrapping, ``a + b == a + b`` is a tautology — the postcondition holds even
when ``a + b`` overflows. The bug is invisible to functional verification. Turn
on UB checking and the same function fails, with a counterexample on ``a + b``.

Turning it on
-------------

.. code-block:: bash

   cpp-verify            file.cpp     # functional only (wraps silently)
   cpp-verify --check-ub file.cpp     # functional + UB freedom

``--check-ub`` is opt-in today — the migration path while existing code grows the
preconditions it always needed. The end state is on-by-default for ``exec``
functions, because that is what makes the runtime contract mean something.

What is checked (Layer A)
-------------------------

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

The classic example — the tool tells you the precondition you forgot:

.. code-block:: cpp

   int abs(int x) post(result >= 0)
   { return x < 0 ? -x : x; }
   //   --check-ub  ->  FAILS: counterexample x = INT_MIN  (negating INT_MIN overflows)

   int abs(int x) pre(x > -2147483648) post(result >= 0)
   { return x < 0 ? -x : x; }
   //   --check-ub  ->  verifies

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

Inside a loop the bound is discharged the same way an invariant is — a fill or
copy loop is proven memory-safe from its guard and invariant. An access through a
pointer with **no** ``valid`` declaration is not bounds-checked (you have opted
out for that pointer). Use-after-lifetime and uninitialized reads are not yet
checked.

Signed vs. unsigned
-------------------

This distinction is load-bearing. **Signed** overflow is UB in C++ and is
checked. **Unsigned** overflow is *defined* modular wraparound, so it is **never
flagged**:

.. code-block:: cpp

   unsigned mix(unsigned a, unsigned b) post(result == a + b)
   { return a + b; }            // verifies with --check-ub: unsigned wrapping is legal

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

Checked today: integer UB (overflow, division) and **array out-of-bounds**.
The remaining memory-safety UB — **use-after-lifetime** and **uninitialized
reads** — is not yet checked (it needs object-lifetime tracking). Pointer
provenance, strict aliasing, and alignment are explicitly assumed away. The full
design and layering plan live in ``docs/UB-CHECKING.md``.
