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
     - Opt out of non-aliasing
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
   * - ``spec T f(...)``
     - Decl
     - Spec function
   * - ``proof void f(...)``
     - Decl
     - Proof function