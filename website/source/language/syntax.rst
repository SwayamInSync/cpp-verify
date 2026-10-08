Contract syntax
===============

Every construct is written qualified by the namespace ``cppverify``:
``cppverify::pre(x > 0)``, ``cppverify::check(e)``, ``cppverify::forall(k, ...)``.
A namespace alias shortens it, and the examples of this reference use one:

.. code-block:: cpp

   namespace cv = cppverify;

   int abs_value(int x)
     cv::pre(x > -2147483647 - 1)
     cv::post(cv::result >= 0)
   {
     return x < 0 ? -x : x;
   }

- The parser recognizes a construct when the qualifier names the global
  namespace ``cppverify``, written ``cppverify::``, ``::cppverify::``, or
  through any alias. A word without the qualifier is ordinary C++: ``pre``,
  ``result``, ``ghost``, or ``check`` may name your own variables and
  functions, and no header of the standard library is affected.
- ``using namespace cppverify;`` does not make the bare words constructs;
  writing one bare where only the construct fits is an error that shows the
  qualified spelling.
- With ``-fverify-contracts``, the namespace and ``<cppverify.h>`` are
  available in every C++ file without an ``#include``. Without the flag the
  constructs are not recognized.
- C++26 contracts (``pre``, ``post``, ``contract_assert`` without a
  qualifier) belong to the compiler; cpp-verify neither parses nor verifies
  them.

Full table:

.. list-table::
   :header-rows: 1
   :widths: 26 22 52

   * - Syntax
     - Placement
     - Meaning
   * - ``cppverify::pre(expr)``
     - After ``)``
     - Precondition
   * - ``cppverify::post(expr)``
     - After ``)``
     - Postcondition
   * - ``cppverify::modifies(...)``
     - After ``)``, or after a loop's invariants
     - Writable cells, ranges ``p[lo : n]``, and objects ``*p``
   * - ``cppverify::aliases(p,q)``
     - After ``)``
     - Opt a pointer/reference address pair into aliasing
   * - ``cppverify::recommends(expr)``
     - Spec functions
     - Soft precondition
   * - ``cppverify::reads(p, n)``
     - Spec functions
     - Cells ``p[0..n)`` the spec depends on (checked)
   * - ``cppverify::when(c)``
     - Spec functions
     - Domain on which the body defines the spec
   * - ``cppverify::inductive``
     - Spec functions returning ``bool``
     - The least predicate the body defines (no ``cppverify::decreases``)
   * - ``cppverify::post(...) by { }``, ``cppverify::decreases(...) by { }``, ``cppverify::reads(...) by { }``
     - Spec function definitions
     - Proof steps for that clause's check
   * - ``cppverify::behavior(name, assumes)``
     - After ``)``, then its ``cppverify::pre``/``cppverify::post``
     - A case of the contract
   * - ``cppverify::complete_behaviors`` / ``cppverify::disjoint_behaviors``
     - After the behaviors
     - Some / at most one behavior applies
   * - ``cppverify::invariant(expr)``
     - After loop ``)``
     - Loop invariant
   * - ``cppverify::decreases(expr)``
     - Loop / function
     - Termination measure (required on executable loops)
   * - ``cppverify::decreases(*)``
     - Executable loop / function
     - Allow divergence; proofs are ``[partial]``
   * - ``cppverify::type_invariant(expr)``
     - In struct/class
     - Field invariant
   * - ``cppverify::ghost { }``
     - Statement
     - Proof-only block
   * - ``cppverify::ghost T x = e;``
     - Statement
     - Function-scoped ghost variable
   * - ``cppverify::check(e)``
     - Statement
     - Proof obligation
   * - ``cppverify::check(e) by { }``
     - Statement
     - Proof obligation with a local proof
   * - ``cppverify::calc { e0; op { } e1; ... }``
     - Statement
     - Chain of proved steps
   * - ``cppverify::reveal_with_fuel(f, n)``
     - In ``cppverify::ghost { }``
     - Unfold recursive spec ``f`` up to depth ``n``
   * - ``cppverify::reveal(f)`` / ``cppverify::hide(f)``
     - In ``cppverify::ghost { }``
     - Make spec ``f`` transparent / opaque locally
   * - ``cppverify::forall(i, lo, hi, e)``
     - Expression
     - Bounded ``∀`` over ``[lo, hi)``
   * - ``cppverify::exists(i, lo, hi, e)``
     - Expression
     - Bounded ``∃`` over ``[lo, hi)``
   * - ``cppverify::forall(i, e)`` / ``cppverify::exists(i, e)``
     - Expression
     - ``∀`` / ``∃`` over all integers
   * - ``cppverify::trigger(term)``
     - In a quantifier body
     - Instantiation pattern
   * - ``cppverify::choose(i, [lo, hi,] e)``
     - Expression
     - Some integer satisfying ``e``
   * - ``cppverify::old(expr)``
     - In ``cppverify::post`` / ``cppverify::invariant``
     - Pre-state value
   * - ``cppverify::result``
     - In ``cppverify::post``
     - Return value
   * - ``cppverify::spec T f(...)``
     - Decl
     - Spec function
   * - ``cppverify::proof void f(...)``
     - Decl
     - Proof function
   * - ``cppverify::seq`` / ``set`` / ``multiset`` / ``map``
     - ``<cppverify.h>``, included implicitly
     - Spec collections
   * - ``cppverify::valid(p, n)``
     - In ``cppverify::pre``
     - ``p`` points to ``n`` objects
