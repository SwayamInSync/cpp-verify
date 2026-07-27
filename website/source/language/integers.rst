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

Mandatory C++ definedness
-------------------------

Executable and ``proof`` code must be well-defined C++. CppVerify therefore
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

**Unsigned arithmetic is never flagged** — C++ defines it as modular wraparound,
so the machine bit-vector operation wraps normally.

.. code-block:: cpp

   int abs(int x) post(result >= 0)
   { return x < 0 ? -x : x; }
   // cpp-verify abs.cpp -> FAILS: counterexample x = INT_MIN

   int abs(int x) pre(x > -2147483648) post(result >= 0)
   { return x < 0 ? -x : x; }      // the precondition the tool asked for -> verifies

   unsigned mix(unsigned a, unsigned b) post(result == a + b)
   { return a + b; }               // verifies: unsigned wraparound is defined

Optional buffer bounds (``--check-ub``)
---------------------------------------

Array bounds require an explicit extent. Write ``valid(p, n)`` in a
precondition and run the Z3 backend with ``--check-ub``; every recognized
``p[i]`` or ``*(p + i)`` access rooted at ``p`` must then prove ``0 <= i < n``.
The marker itself requires ``n >= 0`` and, for a positive extent, a non-null
abstractly valid pointer; extent zero permits null. A pointer with no ``valid``
declaration is not bounds-checked, although ordinary dereference definedness
still applies. Typed pointer steps are converted to target-byte offsets using
``sizeof(T)``, but bounds remain half-open element bounds. The marker must be a
positive top-level conjunction clause on the bare pointer.

Concrete allocation extents, lifetime mutation, provenance, and alignment are
not modeled yet; see :doc:`limitations`.

Lifted ``constexpr`` functions retain target machine widths. At each call the
verifier unfolds the body for C++ definedness checks, so signed overflow, invalid
shifts, and division undefined behavior cannot be justified by bit-vector
wraparound.

Signed left shift follows the C++17 rule: the left operand must be nonnegative
and the shifted value must fit the corresponding unsigned type.  This permits
constructing the sign bit (for example, ``1 << 31`` for a 32-bit ``int``) while
still rejecting values beyond the unsigned range.

Calls crossing between mathematical ``spec`` code and lifted machine
``constexpr`` code perform an explicit conversion at each parameter and return
boundary.  In particular, an unsigned machine result wraps at its target width
before it is converted back to an unbounded mathematical integer.

Contract expressions retain the callee's semantics, so a mathematical spec
result remains unbounded while it is used for specification. If a spec result
is used as an executable value, it is first converted to the C++ destination
machine type; subsequent arithmetic therefore receives the usual overflow and
undefined-behavior checks.

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
