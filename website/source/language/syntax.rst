Contract syntax
===============

Requires ``-fverify-contracts``. Full table:

.. list-table::
   :header-rows: 1
   :widths: 26 22 52

   * - Syntax
     - Placement
     - Meaning
   * - ``pre(expr)``
     - After ``)``
     - Precondition
   * - ``post(expr)``
     - After ``)``
     - Postcondition
   * - ``modifies(...)``
     - After ``)``, or after a loop's invariants
     - Writable cells, ranges ``p[lo : n]``, and objects ``*p``
   * - ``aliases(p,q)``
     - After ``)``
     - Opt a pointer/reference address pair into aliasing
   * - ``recommends(expr)``
     - Spec functions
     - Soft precondition
   * - ``reads(p, n)``
     - Spec functions
     - Cells ``p[0..n)`` the spec depends on (checked)
   * - ``when(c)``
     - Spec functions
     - Domain on which the body defines the spec
   * - ``inductive``
     - Spec functions returning ``bool``
     - The least predicate the body defines (no ``decreases``)
   * - ``behavior(name, assumes)``
     - After ``)``, then its ``pre``/``post``
     - A case of the contract
   * - ``complete_behaviors`` / ``disjoint_behaviors``
     - After the behaviors
     - Some / at most one behavior applies
   * - ``invariant(expr)``
     - After loop ``)``
     - Loop invariant
   * - ``decreases(expr)``
     - Loop / function
     - Termination measure (required on executable loops)
   * - ``decreases(*)``
     - Executable loop / function
     - Allow divergence; proofs are ``[partial]``
   * - ``type_invariant(expr)``
     - In struct/class
     - Field invariant
   * - ``ghost { }``
     - Statement
     - Proof-only block
   * - ``ghost T x = e;``
     - Statement
     - Function-scoped ghost variable
   * - ``contract_assert(e)``
     - Statement
     - Proof obligation
   * - ``contract_assert(e) by { }``
     - Statement
     - Proof obligation with a local proof
   * - ``calc { e0; op { } e1; ... }``
     - Statement
     - Chain of proved steps
   * - ``reveal_with_fuel(f, n)``
     - In ``ghost { }``
     - Unfold recursive spec ``f`` up to depth ``n``
   * - ``reveal(f)`` / ``hide(f)``
     - In ``ghost { }``
     - Make spec ``f`` transparent / opaque locally
   * - ``forall(i, lo, hi, e)``
     - Expression
     - Bounded ``∀`` over ``[lo, hi)``
   * - ``exists(i, lo, hi, e)``
     - Expression
     - Bounded ``∃`` over ``[lo, hi)``
   * - ``forall(i, e)`` / ``exists(i, e)``
     - Expression
     - ``∀`` / ``∃`` over all integers
   * - ``trigger(term)``
     - In a quantifier body
     - Instantiation pattern
   * - ``choose(i, [lo, hi,] e)``
     - Expression
     - Some integer satisfying ``e``
   * - ``old(expr)``
     - In ``post`` / ``invariant``
     - Pre-state value
   * - ``result``
     - In ``post``
     - Return value
   * - ``spec T f(...)``
     - Decl
     - Spec function
   * - ``proof void f(...)``
     - Decl
     - Proof function
   * - ``cppverify::seq`` / ``set`` / ``multiset`` / ``map``
     - ``#include <cppverify.h>``
     - Spec collections
