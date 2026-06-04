Integers
========

Integer semantics depend on where the value lives.

.. list-table::
   :header-rows: 1

   * - Kind
     - Semantics
   * - ``spec``
     - Mathematical ``Int`` (unbounded, no overflow)
   * - ``constexpr`` in contracts
     - Machine bit-vector
   * - ``proof`` / ``exec``
     - Machine bit-vector

Machine integers are encoded as bit-vectors, so they overflow exactly as the
hardware would. Spec-world integers are unbounded mathematics — you state the
ranges you need and reason without overflow.

Width and signedness
---------------------

Each machine integer's **bit width** comes from the target's data model
(``ASTContext::getTypeSize``), so ``int`` is checked at 32 bits and ``long`` /
``long long`` at 64 bits on an LP64 target. Mixed-width arithmetic
(``(long)a + b``) sign-extends the narrower operand, exactly as C++ does.

**Signedness** is tracked too, and it matters: signed overflow is undefined
behavior in C++, while unsigned overflow is *defined* modular wraparound. The
verifier treats them differently — see below.

(Currently ``int8``/``int16`` are modeled as 32-bit ``int``, and heap cells are
32-bit; these are precision limits, not unsoundness at the ``int``/``long``
boundary.)

Undefined-behavior checking (``--check-ub``)
--------------------------------------------

By default the verifier proves your **functional** contract (``pre ∧ code ⇒
post``) under wrapping arithmetic. That alone is blind to overflow bugs: under
silent wrapping, ``post`` can still hold on the wrapped value.

Pass ``--check-ub`` and the verifier *also* proves the function is free of a
class of **undefined behavior** — and this obligation is generated for you from
the operations in the code. You only write ``pre``/``post``; if a precondition is
too weak to rule out the UB, it is reported with a counterexample telling you the
precondition your function actually needs.

What is checked (Layer A):

.. list-table::
   :header-rows: 1
   :widths: 40 60

   * - Operation
     - Obligation
   * - signed ``+`` ``-`` ``*``, unary ``-``
     - does not overflow (at the operand's width)
   * - ``/`` and ``%``
     - divisor ``!= 0``
   * - signed ``/`` ``%``
     - not ``INT_MIN / -1`` (which overflows)

**Unsigned arithmetic is never flagged** — C++ defines it as modular wraparound,
so no obligation is emitted.

.. code-block:: cpp

   int abs(int x) post(result >= 0)
   { return x < 0 ? -x : x; }
   // cpp-verify            abs.cpp  -> verifies (wraps silently)
   // cpp-verify --check-ub abs.cpp  -> FAILS: counterexample x = INT_MIN

   int abs(int x) pre(x > -2147483648) post(result >= 0)
   { return x < 0 ? -x : x; }      // the precondition the tool asked for -> verifies

   unsigned mix(unsigned a, unsigned b) post(result == a + b)
   { return a + b; }               // verifies even with --check-ub (defined wraparound)

``--check-ub`` is opt-in today (the migration path); it runs on the Z3 backend
for ``exec``/``proof`` functions. It does **not** yet cover memory-safety UB
(out-of-bounds, use-after-lifetime) — see :doc:`limitations`. The full design,
including the layering plan, is in ``docs/UB-CHECKING.md``.
