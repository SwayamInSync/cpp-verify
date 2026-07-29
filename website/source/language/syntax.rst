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
     - After ``)``
     - Writable lvalues
   * - ``aliases(p,q)``
     - After ``)``
     - Opt a pointer/reference address pair into aliasing
   * - ``recommends(expr)``
     - Spec functions
     - Soft precondition
   * - ``invariant(expr)``
     - After loop ``)``
     - Loop invariant
   * - ``decreases(expr)``
     - Loop / function
     - Termination measure
   * - ``type_invariant(expr)``
     - In struct/class
     - Field invariant
   * - ``ghost { }``
     - Statement
     - Proof-only block
   * - ``contract_assert(e)``
     - Statement
     - Proof obligation
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