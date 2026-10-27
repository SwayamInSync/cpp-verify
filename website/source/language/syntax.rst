Contract syntax
===============

Every construct is written qualified by the namespace ``cppverify``:
``cppverify::pre(x > 0)``, ``cppverify::check(e)``, ``cppverify::forall(k, ...)``.
A namespace alias shortens it. The examples of this reference write the
constructs through the alias ``cv`` and use the names of ``<cppverify.h>``
(``valid``, ``seq``, ``set``, ``multiset``, ``map``) unqualified, as a file
does after ``namespace cv = cppverify;`` and ``using namespace cppverify;``:

.. code-block:: cpp

   namespace cv = cppverify;
   using namespace cppverify;

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

C++26 contracts
---------------

This compiler does not implement C++26 contracts. With ``-fverify-contracts``,
a bare ``pre(...)`` or ``post(...)`` after a function declarator is an error
whose fix-it writes the cpp-verify construct, and so is a bare
``contract_assert``:

.. cppverify-example: rejects

.. code-block:: cpp

   int positive(int x)
     pre(x > 0)
   {
     contract_assert(x > 0);
     return x;
   }

.. code-block:: text

   bare.cpp:2:3: error: C++26 contract specifiers are not supported; a cpp-verify precondition is written 'cppverify::pre'
   bare.cpp:4:3: error: 'contract_assert' is a cpp-verify construct only when qualified: write 'cppverify::check'

Without the flag, Clang reads neither as a contract: ``pre(x > 0)`` there is
``error: expected function body after function declarator``.

One condition per clause
------------------------

Each clause takes exactly one expression. To state two conditions, join them
with ``&&`` or write two clauses, which mean the same: every ``cv::pre`` must
hold, and so must every ``cv::post``.

.. code-block:: cpp

   int clamp(int x)
     cv::post(cv::result >= 0 && cv::result <= 10)
   {
     return x < 0 ? 0 : x > 10 ? 10 : x;
   }

   int clamp_again(int x)
     cv::post(cv::result >= 0)
     cv::post(cv::result <= 10)
   {
     return x < 0 ? 0 : x > 10 ? 10 : x;
   }

Anything written after the expression, inside the parentheses, is an error.
A missing ``&&`` is the usual cause:

.. cppverify-example: rejects

.. code-block:: cpp

   int clamp(int x)
     cv::post(cv::result >= 0 cv::result <= 10)
   {
     return x < 0 ? 0 : x > 10 ? 10 : x;
   }

.. code-block:: text

   clauses.cpp:2:28: error: expected ')' after cppverify::post expression
       2 |   cv::post(cv::result >= 0 cv::result <= 10)
         |                            ^
   clauses.cpp:2:11: note: to match this '('
       2 |   cv::post(cv::result >= 0 cv::result <= 10)
         |           ^

Before 0.2, the parser kept the first condition and dropped the rest without
a word, so a clause with a missing ``&&`` checked less than it said: the
example above verified ``cv::result >= 0`` alone.

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
     - Statement anywhere in a function body, ghost blocks included
     - Unfold recursive spec ``f`` up to depth ``n`` in the whole function
   * - ``cppverify::reveal(f)`` / ``cppverify::hide(f)``
     - Statement anywhere in a function body, ghost blocks included
     - Make spec ``f`` transparent / opaque in the whole function
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
     - A top-level condition of ``cppverify::pre``; an error anywhere else
     - ``p`` points to ``n`` objects

Macros named like a construct
-----------------------------

The preprocessor runs before the parser sees a construct, so a function-like
macro named like a construct expands inside the qualified name. A header that
defines ``check(condition)`` breaks every ``cppverify::check`` after it:

.. cppverify-example: rejects

.. code-block:: cpp

   #define check(condition) ((void)0)

   int positive(int x)
     cv::pre(x > 0)
   {
     cv::check(x > 0);
     return x;
   }

.. code-block:: text

   macros.cpp:6:7: error: expected unqualified-id

``#undef check`` after the header's ``#include`` restores the construct:

.. code-block:: cpp

   #define check(condition) ((void)0)
   #undef check

   int positive(int x)
     cv::pre(x > 0)
   {
     cv::check(x > 0);
     return x;
   }

.. code-block:: text

   Verified: positive [backend=z3]

An object-like macro has the same effect on a construct written without
parentheses, such as ``cv::result``.

On Apple platforms (macOS, iOS, and the others), ``<AssertMacros.h>``, which
some of Apple's framework headers include, defines ``check(assertion)`` unless
``__ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES`` is ``0``. With
``-fverify-contracts`` on an Apple target, the compiler therefore defines it
to ``0`` before any header, unless the command line defines it, and
``cppverify::check`` works next to that header. The header then defines only
its ``__Check``, ``__Require``, and ``__Verify`` macros, the names Apple
recommends. A file that uses the old names (``check``, ``require``,
``verify``, and their variants) can switch to the ``__`` names, or keep the
old ones with ``-D__ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES=1`` on
the command line; ``cppverify::check`` then works only after an ``#undef
check``. Defining it to ``1`` with ``#define`` in the source also works, with
a ``-Wmacro-redefined`` warning.
