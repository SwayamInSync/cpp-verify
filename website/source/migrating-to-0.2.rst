Migrating from 0.1 to 0.2
=========================

0.2.0 keeps 0.1's contract language, every construct written qualified
(``cppverify::pre``, or ``cv::pre`` through an alias), and the same LLVM
23.1.3 and Z3 4.13.4. This page lists what a user of 0.1.1 has to know or
change: source that is now an error, verdicts that change on unchanged
source, command lines, output formats, and Lean projects. Each item says
what to do; :doc:`release-notes` describes every change, with examples.

Versions
--------

- LLVM 23.1.3 and Z3 4.13.4, built in: unchanged.
- cvc5: tested from 1.1.2 to 1.4.2 (0.1.1 was tested with 1.1.2 only);
  ``cpp-verify --version`` names the range.
- Lean: projects pin ``leanprover/lean4:v4.35.0`` (0.1.1 pinned
  ``v4.32.2``). See `Lean projects`_.

Source that must change
-----------------------

**A clause takes one expression.** 0.1.1 kept the first condition of a
clause and dropped the rest without a word, so a clause with its ``&&``
missing checked less than it said. It is now an error:

.. cppverify-example: rejects

.. code-block:: cpp

   int clamp10(int x)
     cv::post(cv::result >= 0 cv::result <= 10)
   {
     return x < 0 ? 0 : x > 10 ? 10 : x;
   }

.. code-block:: text

   clamp.cpp:2:28: error: expected ')' after cppverify::post expression

Add the ``&&``.

**A contract must be defined where it is evaluated.** Each precondition is
checked where the ones before it hold, each postcondition in the state the
function returns in, with the checks an operation gets in a body
(:doc:`language/functions-loops`). A clause that may be undefined fails as
``contract of f``, and a caller that relies on it is ``Unresolved`` with
reason ``callee.contract``. Test a value before you use it:

.. code-block:: cpp

   int ratio(int a, int b)
     cv::pre(a / b > 0 && b > 0)
     cv::post(cv::result > 0)
   {
     return a / b;
   }

   int ratio_fixed(int a, int b)
     cv::pre(b > 0 && a / b > 0)
     cv::post(cv::result > 0)
   {
     return a / b;
   }

.. code-block:: text

   ratio.cpp:2:13: error: verification failed: contract of ratio [division-by-zero] [backend=z3] [reason=counterexample]
   Verified: ratio [backend=z3]
   Verified: ratio_fixed [backend=z3]

``ratio``'s body is right for every input its contract admits; the contract
itself divides by ``b`` before it requires ``b > 0``.

**Verification-only constructs stay out of executable code.** These compiled
in 0.1.1 and meant something other than they said; each is now an error:

- ``cv::forall`` and ``cv::exists`` in executable code (0.1.1 compiled an
  undefined value), as ``cv::choose`` already was: move them into a contract
  or ghost code (:doc:`language/expressions`);
- a call of a spec function in a generic lambda (0.1.1 failed to link)
  (:doc:`language/ghost-proofs`);
- ``valid(p, n)`` anywhere but as a top-level condition of a precondition,
  where it meant ``true``: ``cv::post(valid(cv::result, 4))`` verified for a
  function returning ``nullptr`` (:doc:`language/pointers`).

**A trusted declaration no longer trusts its definition.** In 0.1.1, a
definition took the ``[[cppverify::trusted]]`` of a header declaration and
was never checked. A definition is now trusted only by a mark of its own:
mark it if it must stay trusted, or expect it to be verified, and perhaps to
fail (:doc:`language/functions-loops`).

**Member functions the verifier does not support are errors.** 0.1.1 ignored
contracts on member functions with a warning. A contracted virtual function,
destructor, or conversion function, or a member function of a class with
bases, is now an error naming it (:doc:`language/structs`).

**A spec template is named by its specialization** in ``cv::hide``,
``cv::reveal``, and ``cv::reveal_with_fuel``: ``cv::hide(at<4>)``. The
template's name alone is an error, ``reference to overloaded function could
not be resolved`` (:doc:`language/ghost-proofs`).

**Apple's assertion macros.** On Apple targets, ``-fverify-contracts`` defines
``__ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES`` to 0, so that
``<AssertMacros.h>`` no longer defines a ``check(assertion)`` macro that
expands inside ``cv::check(...)``. Code that used the unprefixed ``check``,
``require``, or ``verify`` macros uses ``__Check``, ``__Require``, and
``__Verify``, or defines the macro to 1 on its command line
(:doc:`language/syntax`).

**clang-format** writes a range footprint ``p[lo : n]``, where 0.1.1 wrote
``p [lo:n]``: reformatting changes those lines (:doc:`language/tooling`).

Verdicts that change on unchanged source
----------------------------------------

**Fixes of wrong results.** 0.1.1 reported ``Verified`` for some false
claims. Each is fixed, so a function that verified may now fail or be
unresolved, and the failure is real: undefined contracts (above), recursion
through ``cv::choose``, values a spec reads through a pointer (now exact, they
wrapped at the machine type), and results that rest on Lean proofs (they now
rest on the callee contracts and spec facts their modules use, as a solver's
do). :doc:`release-notes` lists them under "Wrong results fixed".

**Contracts that 0.1.1 ignored are verified.** These bring new obligations,
and possibly new failures, to source that did not change:

- member functions, verified as functions of ``this``, and constructors,
  which must initialize every member (:doc:`language/structs`);
- class invariants, assumed on entry to every public member function and
  checked where it returns, established by every constructor, and held by
  objects passed by reference or pointer (0.1.1 checked by-value records
  only);
- templates, in each specialization the translation unit instantiates; a
  contracted template that nothing instantiates is reported
  (:doc:`language/functions-loops`);
- ``assert(c)`` (0.1.1: ``unsupported statement``), and calls that do not
  return (``abort``, ``exit``): reaching one fails a check of the new kind
  ``unreachable``, and after ``assert(c)``, ``c`` holds. With ``NDEBUG`` an
  ``assert`` is nothing;
- ``std::min`` and ``std::max`` of two integers mean what the standard says,
  and the C library's ``abs``, ``memcpy``, ``memmove``, ``memset``, and
  ``memcmp`` have models; any other function of the standard library is an
  error naming it (:doc:`language/pointers`);
- a function without a contract, which stopped every caller in 0.1.1
  (``call to function without a verification contract``), is inlined where
  verified code calls it: its body is checked at the arguments each caller
  passes, and a failure in it fails the caller, shown at the helper's
  operation with its variables named ``helper::x``. One that cannot be
  inlined (it recurses, returns a record by value, or allocates, among
  others) still needs a contract, and the error says which
  (:doc:`language/functions-loops`).

**One unsupported construct costs its function.** In 0.1.1 it stopped the
file, with no verdicts. Now that function is ``Unresolved`` with reason
``construct.unsupported``, the others are verified, and the exit status is 1,
as before (:doc:`language/tooling`).

**Failures that were not real.** 0.1.1 reported failures for correct C++ in
several places, among them a loop that never repeats (``do { ... } while
(0)``), null minus null, signed left shifts under ``-std=c++20``, values read
through ``new`` pointers, slices passed through a copy, and callee frames
inside the caller's. These verify now; nothing needs changing.

**Budgets.** A function's complete query gets a fixed amount of solver work
(6 million Z3 resource units) instead of 500 ms, with ``--timeout`` as the
bound in time, so fewer results depend on the machine's load. A result that
was ``Unresolved`` with ``solver.timeout`` may now be decided, and the other
way round under heavy load (:doc:`language/tooling`).

**Lemmas that time out.** A proof function that ended ``Unresolved`` with
``solver.timeout`` is now tried by the automatic inductions too, which can
prove it (``[by induction on j]``). They start once the direct attempt has
spent its timeout, so such a lemma now takes longer before its verdict
(:doc:`book/part-ii/ch13-spec-and-proof-functions`).

Command lines
-------------

No option was removed or renamed. What changes:

- **An option selects the backend that uses it, and one the run would not use
  is an error**, so nothing is verified: ``--unroll`` selects BMC, and beside
  another ``--backend`` it is an error (0.1.1 ran Z3 and reported an unbounded
  ``Verified``); ``--lean-out`` and ``--lean-project`` select Lean, and
  ``--timeout`` and the other solver budgets are errors with Lean export.
  :doc:`language/tooling` lists each message.
- **A compiler error stops its file**, and cpp-verify exits with status 1;
  0.1.1 printed the error, went on, and could exit with 0. A ``.h`` input is
  compiled as C++.
- **Memory**: ``--max-query-nodes`` defaults to 4 million expression nodes
  (0.1.1: no limit), and ``--memory-limit`` (8192 MB by default) bounds Z3's
  queries together and each cvc5 process. A function over either is
  ``Unresolved`` with ``query.size-limit`` or ``solver.memory-limit``; raise
  the limit on the command line where a larger function must run.
- **Ctrl-C** ends the run: the functions not finished are ``Interrupted``
  (reason ``interrupted``), and the exit status is 130.
- **Archive replay** (``--obligation-in``) reports ``Proved obligations: f
  (dependencies not checked in replay)``, JSON status ``proved-obligations``,
  where 0.1.1 reported ``Verified``: a module alone is not the facts its
  verdict rests on.

New options change nothing unless used: ``--function``, ``--list-functions``,
``--quiet``, ``--time-report``, ``--max-failures``, ``--confirm-bound``,
``--dump-smt2``, ``--contracts-out`` and ``--check-contracts`` (with
``clang++ -fverify-contracts-out``), and ``--diagnostics-format=sarif`` and
``=github``.

Output formats
--------------

**Text.** A failure is a Clang error at the part that fails, with its line,
a caret, the check's kind, and notes for the counterexample, in source names,
and the steps of its path:

.. code-block:: cpp

   int square(int x)
     cv::post(cv::result >= 0)
   {
     return x * x;
   }

.. code-block:: text

   square.cpp:4:12: error: verification failed: square [overflow] [backend=z3] [reason=counterexample]
       4 |   return x * x;
         |          ~~^~~
   square.cpp:4:12: note: counterexample: x = 46341
   Summary: 1 failed in 0.0 s

0.1.1 printed one line for it, of the form ``verification failed: f
[fn_...::overflow@4:3] (counterexample: x [ssa=x_0] [type=i32] = ...;
trace: ...)``. A run now ends with a ``Summary:`` line, and the ``Verified:
spec axiom`` lines need ``--verbose``. Anything that reads the text output
needs updating; JSON is the format meant for tools.

**Compile-time verification** (``clang++ -fverify-contracts``) reports each
result as a diagnostic of its own: a failure or an unresolved result is an
error, a warning belongs to ``-Wcppverify`` (so ``-Wno-cppverify`` and
``-Werror=cppverify`` work), a proof is a remark (``-Rcppverify``), and
``-fdiagnostics-format=sarif`` carries them all. 0.1.1 printed text and one
error, ``cppverify: verification failed``.

**JSON** records are ``cppverify.diagnostic/2`` (0.1.1:
``cppverify.diagnostic/1``). Every record names its function and where it is
declared, a failure's range ends after its last character, a failure gives
its counterexample (``model``) and path (``trace``) as the text does,
compiler diagnostics are records with status ``frontend``, and a run ends
with a ``cppverify.summary/1`` record; ``--time-report`` adds
``cppverify.time/1`` records. New values a consumer may meet: the statuses
``interrupted`` and ``proved-obligations``, the reasons ``interrupted`` and
``solver.memory-limit``, and the check kinds ``unreachable`` and
``builtin-argument`` (:doc:`language/tooling`).

**Archives** are written as ``cppverify.obligation/6``, and 0.2 reads ``/1``
to ``/6``. 0.1.1 writes ``/2`` and cannot read ``/6``. Semantic hashes keep
format 4.

Lean projects
-------------

The next time cpp-verify writes a project that 0.1 generated, it moves the
project to 0.2's pin, with a warning, and to its layout:

- the toolchain pin becomes ``leanprover/lean4:v4.35.0``; install that Lean,
  and update a proof that no longer builds with it;
- goals are named by their function and the hash of their statement, not by
  position, and their proofs move to the new names with them; a proof whose
  statement changed, or whose function is gone, moves to ``Stale/``, which
  ``--lean-prune-stale`` removes;
- each function's goals are a module of their own,
  ``CppVerify/Goals/<function>.lean``; a ``User.lean`` that imports
  ``CppVerify.Generated`` keeps working;
- goals are printed in Lean's own precedence, with typed numerals, and with
  SMT-LIB's division by zero: a proof that relied on the old printing may no
  longer check;
- each new goal is first tried by ``cppverify_auto`` (``--no-lean-auto``
  turns that off, ``--lean-auto-timeout`` bounds each goal);
- certification no longer elaborates the project's source: it checks each
  proof's type against its goal and the axioms it uses, function by function.

See :doc:`book/part-ii/ch17-backends-modular-calls`.
