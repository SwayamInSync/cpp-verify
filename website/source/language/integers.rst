Integers
========

Integer semantics depend on where the value lives.

.. list-table::
   :header-rows: 1

   * - Kind
     - Semantics
   * - ``cppverify::spec``
     - Mathematical ``Int`` (unbounded, no overflow)
   * - ``constexpr`` in contracts
     - Machine integer (target width, wraps modulo ``2^N``)
   * - ``cppverify::proof`` / ``exec``
     - Machine integer (target width, wraps modulo ``2^N``)
   * - Contract arithmetic (``cppverify::pre``, ``cppverify::post``, invariants, assertions)
     - Mathematical ``Int`` on the values of C++ expressions

Contracts are mathematical, as in ACSL and Verus. ``+``, ``-``, ``*``,
``/``, ``%``, and unary ``-`` in a contract are exact, so
``cppverify::post(cppverify::result + 1 > cppverify::result)`` holds rather than overflowing. An implicit
conversion whose result C++ could change (a narrowing or a sign change) keeps
the value; a value-preserving one is an ordinary extension. Quantifier binders
are mathematical integers. A negative constant converted to an unsigned type
draws a warning, since the contract compares its exact value. An explicit
cast still converts and is checked; write wraparound explicitly as
``% 4294967296``.

Mathematical integers are unbounded, but ``/`` and ``%`` retain C++'s
truncate-toward-zero sign rules. Their total logical extension at a zero divisor
is quotient zero and remainder equal to the dividend. Executable machine
evaluation sites still emit a nonzero-divisor proof obligation.

Width and signedness
---------------------

Each machine integer's **bit width** comes from the target's data model
(``ASTContext::getTypeSize``), so ``int`` is checked at 32 bits and ``long`` /
``long long`` at 64 bits on an LP64 target. Mixed-width arithmetic
(``(long)a + b``) sign-extends the narrower operand, exactly as C++ does.
Narrow integers and extensions such as ``__int128`` retain their target widths;
the usual integral promotions are applied before arithmetic.

**Signedness** is tracked too, and it matters: signed overflow is undefined
behavior in C++, while unsigned overflow is *defined* modular wraparound. The
verifier treats them differently. Heap payloads are width-neutral mathematical
integers; typed loads and stores perform the required target-width conversions.

Solver encoding
---------------

How a machine integer reaches the solver is independent of its meaning.
``--int-encoding=bitvector`` uses solver bit-vectors. ``--int-encoding=integer``
uses mathematical integers kept in the type's range: every variable carries its
range, and every operation is reduced modulo ``2^N``, so wraparound, division by
zero, conversions, and overflow checks are exactly the bit-vector ones. Integers
combine far better with quantifiers and the heap, for example a 64-bit
``cppverify::forall`` over a buffer. The default ``auto`` uses integers for a query unless
it needs the bits of a non-constant operand (``a & b``, ``x << s``); masks such as
``x & 0xff`` and constant shifts are arithmetic and keep integers. Every mode
gives the same verdicts and counterexamples, so the flag is purely a
performance choice.

Mandatory C++ definedness
-------------------------

Executable and ``cppverify::proof`` code must be well-defined C++. CppVerify therefore
generates path-sensitive safety obligations automatically; these checks are not
optional because a functional proof about an undefined execution would be
meaningless.

Core checks include:

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
   * - ``<<`` and ``>>``
     - shift count is in range; signed left shift satisfies the C++17 rule
   * - pointer loads and stores
     - base pointer is non-null and abstractly valid
   * - mathematical value converted to a machine type
     - value is in the type's range

**Unsigned arithmetic is never flagged** — C++ defines it as modular wraparound,
so the machine operation wraps modulo ``2^N``. Contract arithmetic is
mathematical, though: ``a + b`` in a contract is the exact sum, so a
contract that means the wrapped value says so with ``% 2^N``.

.. code-block:: cpp

   int abs_unguarded(int x) cv::post(cv::result >= 0)
   { return x < 0 ? -x : x; }

   int abs_guarded(int x) cv::pre(x > -2147483648) cv::post(cv::result >= 0)
   { return x < 0 ? -x : x; }

   unsigned mix(unsigned a, unsigned b) cv::post(cv::result == (a + b) % 4294967296)
   { return a + b; }

   unsigned mix_wrong(unsigned a, unsigned b) cv::post(cv::result == a + b)
   { return a + b; }

.. code-block:: text

   abs.cpp:2:3: error: verification failed: abs_unguarded [...::overflow@2:3]
     (counterexample: x [type=i32] = -2147483648)
   Verified: abs_guarded [backend=z3]
   Verified: mix [backend=z3]
   abs.cpp:10:56: error: verification failed: mix_wrong [...::postcondition@10:56]
     (counterexample: result [type=u32] = 0, a [type=u32] = 1, ...)

Negating ``INT_MIN`` overflows, so ``abs_unguarded`` fails at the overflow
check with that input, and the precondition the tool asks for makes
``abs_guarded`` verify. ``mix_wrong`` claims the exact sum, which the
wrapped result is not when the sum reaches ``2^32``.

Memory bounds
-------------

Memory accesses are checked by default (``--check-ub``; ``--no-check-ub``
turns it off). Write ``valid(p, n)`` in a precondition to declare an extent:
every ``p[i]`` or ``*(p + i)`` access rooted at ``p`` must then prove
``0 <= i < n``, and pointer arithmetic must stay in ``[0, n]``. The marker
itself requires ``n >= 0`` and, for a positive extent, a non-null abstractly
valid pointer; extent zero permits null. A pointer without a ``valid``
declaration addresses a single object, so ``p[0]`` is fine and ``p[1]`` must
be proved inside that object, which fails. Typed pointer steps are converted
to target-byte offsets using ``sizeof(T)``, but bounds remain half-open
element bounds. The marker must be a positive top-level conjunction clause on
the bare pointer. See :doc:`pointers`.

Concrete extent, lifetime, alignment, and initialization metadata is tracked
for the bounded local scalar ``new``/``delete`` subset. General buffer
provenance and parameter-pointer extents remain abstract; see
:doc:`dynamic-storage` and :doc:`limitations`.

Lifted ``constexpr`` functions retain target machine widths. At each call the
verifier unfolds the body for C++ definedness checks, so signed overflow, invalid
shifts, and division undefined behavior cannot be justified by machine
wraparound.

Signed left shift follows the C++17 rule: the left operand must be nonnegative
and the shifted value must fit the corresponding unsigned type.  This permits
constructing the sign bit (for example, ``1 << 31`` for a 32-bit ``int``) while
still rejecting values beyond the unsigned range.

Calls crossing between mathematical ``cppverify::spec`` code and lifted machine
``constexpr`` code convert at each parameter and return boundary. A machine
result converts exactly to an unbounded integer; an unsigned result has already
wrapped at its target width, as C++ defines. A mathematical argument must fit
the machine parameter type.

A mathematical value never wraps into a C++ type:

- A spec result, and a length, element, or count of a spec collection,
  stays unbounded wherever it is used: in contracts and in ``cppverify::ghost`` and
  ``cppverify::proof`` code alike. Arithmetic, selections, and comparisons involving it
  are exact, and the implicit conversions of C++'s usual arithmetic
  conversions do not bound it, so ``cppverify::post(cppverify::result == total(x) + n)`` compares
  exact values and ``s.subrange(0, s.len() - 1)`` in a proof is exact. A
  comparison between a machine value and a mathematical one is exact.
- Storing such a value in a ``cppverify::ghost`` or ``cppverify::proof`` variable, passing it to a
  machine parameter, returning it, an explicit cast such as
  ``(int)total(x)``, and a bitwise operator applied to it convert it to a
  machine type. The conversion is defined only when the value fits, and it
  carries an ``overflow`` obligation instead of wrapping:

.. cppverify-example: fails too_big element

.. code-block:: cpp

   cv::spec int scaled(int x) { return x * 1000; }

   cv::proof void lemma(int x) cv::pre(x >= 0 && x <= 1000)
   { int value = scaled(x); }   // verifies: the value fits in int

   cv::proof void too_big(int x) cv::pre(x == 3000000)
   { int value = scaled(x); }   // FAILS (overflow): 3000000000 is not an int

   cv::proof void element(cppverify::seq s) cv::pre(s.len() > 0)
   { int x = s[0]; }            // FAILS (overflow): an element need not fit

- Executable code cannot call a spec function at all; see :doc:`ghost-proofs`.

Executable modular calls likewise apply Clang's formal-parameter and destination
conversions. Signedness, widening, and narrowing therefore occur before a
callee contract is instantiated and before a returned value is used by the
caller.

Exact ``int`` boundaries
------------------------

CppVerify's permanent acceptance suite proves recursive and iterative
implementations against unbounded mathematical specifications while retaining
32-bit signed ``int`` execution:

- factorial is verified for ``0 <= n <= 12``; computing ``13!`` is rejected
  because ``6227020800`` is not representable;
- Fibonacci is verified for ``0 <= n <= 46``; computing ``F(47)`` is rejected
  because ``2971215073`` is not representable.

These are C++ representation limits, not arbitrary verifier cutoffs. The
negative cases exercise the same path-sensitive signed-overflow obligations as
ordinary executable code.
