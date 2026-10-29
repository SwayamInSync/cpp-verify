Commands and flags
==================

Standalone verifier
-------------------

.. code-block:: bash

   cpp-verify --version
   cpp-verify file.cpp
   cpp-verify --quiet file.cpp
   cpp-verify --verbose file.cpp
   cpp-verify --list-functions file.cpp
   cpp-verify --function='parse_*' --function=encode file.cpp
   cpp-verify --time-report file.cpp
   cpp-verify file.cpp -- -I include -DNDEBUG
   cpp-verify src/a.cpp src/mathx.cpp -- -I include
   cpp-verify --contracts-out=a.cppverify src/a.cpp -- -I include
   cpp-verify --check-contracts a.cppverify mathx.cppverify
   cpp-verify --backend=z3 file.cpp
   cpp-verify --backend=cvc5 file.cpp
   cpp-verify --backend=portfolio file.cpp
   cpp-verify --backend=race file.cpp
   cpp-verify --backend=bmc --unroll=3 file.cpp
   cpp-verify --backend=lean --lean-out=goal.lean file.cpp
   cpp-verify --backend=lean --lean-project=proof file.cpp
   cpp-verify --backend=lean --lean-project=proof --lean-certify file.cpp
   cpp-verify --lean-fallback=proof file.cpp
   cpp-verify --no-check-ub file.cpp
   cpp-verify --profile-quantifiers file.cpp
   cpp-verify --timeout=20000 file.cpp
   cpp-verify --confirm-bound=4 file.cpp
   cpp-verify --max-failures=0 file.cpp
   cpp-verify --jobs=4 --proof-cache=.cppverify-cache file.cpp
   cpp-verify --solver-rlimit=500000 --max-query-nodes=50000 file.cpp
   cpp-verify --memory-limit=4096 file.cpp
   cpp-verify --diagnostics-format=json file.cpp
   cpp-verify --diagnostics-format=sarif file.cpp > results.sarif
   cpp-verify --diagnostics-format=github file.cpp
   cpp-verify --dump-ir=1,2,3,4 file.cpp
   cpp-verify --lower-only --dump-ir=1,2,3,4 file.cpp
   cpp-verify --lower-only --obligation-out=goals.cpv file.cpp
   cpp-verify --obligation-in=goals.cpv --backend=z3

``cpp-verify`` is a Clang tooling driver: it always adds ``-std=c++17`` and ``-fverify-contracts``.
Other compiler flags come from the ``compile_commands.json`` beside the file or in a directory
above it, or in the directory ``-p DIR`` names; a file the database does not list gets the
flags of a listed neighbour. Without a database the file is compiled with those two flags
alone. Flags after ``--`` replace the database, and ``--extra-arg=FLAG`` adds one flag either
way.

Several files given to one run are verified one after the other and
settled together: a contract one file declares without a definition holds
for a proof once its definition's verification in another file establishes
it (see :doc:`functions-loops`). Their results are printed once every file
is verified, in the order given.

Files verified apart record their contracts instead:
``--contracts-out=FILE`` (or ``clang++ -fverify-contracts
-fverify-contracts-out=FILE``) writes a ``cppverify.contracts/1`` record of
the contracts the file verifies, whether it establishes each and on which
contracts of other files that rests, and of its proofs that rest on
contracts of other files, which say so (``[assumes=f]``).
``cpp-verify --check-contracts RECORD...`` settles the records and prints
each proof that relies on a contract not established, at the proof's
function, then a line that counts them; its exit status is non-zero when
there is one.

Input files and compiler errors
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Every input is compiled as C++, a header too: a ``.h`` file given as input is
a C++ header, and its functions are verified like those of a ``.cpp`` file.

.. code-block:: cpp

   inline int clamp100(int x)
     cv::post(cv::result <= 100)
   {
     return x > 100 ? 100 : x;
   }

.. code-block:: text

   $ cpp-verify mathx.h --
   Verified: clamp100 [backend=z3]

A compiler error stops the file it belongs to, whether it is in the file or
in its command line: the file is not verified, the next input files are, and
``cpp-verify`` exits with status 1.

.. code-block:: text

   $ cpp-verify abs.cpp -- -fbogus-flag
   error: unknown argument: '-fbogus-flag'
   Error while processing abs.cpp.

Before 0.2, an error in a command line was printed and then ignored: the
file was verified anyway, under other options than the ones given, and
``cpp-verify`` exited with status 0. A ``.h`` input was compiled as C, which
printed ``error: invalid argument '-std=c++17' not allowed with 'C'``.

A construct that cpp-verify does not represent yet, in a function it
verifies, is an error at that construct, shown with its line and a caret as a
compiler error is. It costs that function alone: the function is
``Unresolved`` with reason ``construct.unsupported``, every other function of
the file is verified, and ``cpp-verify`` exits with status 1
(:doc:`limitations` lists what is not represented).

.. cppverify-example: rejects

.. code-block:: cpp

   int pick(int x)
     cv::post(cv::result >= 0)
   {
     if (x < 0) throw x;
     return x;
   }

   int bump(int x)
     cv::pre(x < 100)
     cv::post(cv::result == x + 1)
   {
     return x + 1;
   }

   int picked(int x)
     cv::post(cv::result >= 0)
   {
     int r = pick(x);
     return r;
   }

.. code-block:: text

   pick.cpp:4:14: error: pick: throw is unsupported: exceptions are not modeled
       4 |   if (x < 0) throw x;
         |              ^~~~~~~
   Verified: bump [backend=z3]
   Unresolved: picked [backend=z3] [reason=callee.contract] (relies on the contract of pick (it uses a construct the verifier does not support), which is not established)

What others may rely on stays:

- a caller of an executable or proof function whose body is not represented
  is verified against its contract, which nothing establishes, so it is
  ``Unresolved`` with reason ``callee.contract``, as ``picked`` above;
- a function whose contract is not represented leaves nothing to rely on: a
  call of it is ``construct.unsupported`` where it is (``a call of lookup,
  whose contract is not available``);
- a spec whose body or contract is not represented has no definition, and a
  function that reaches it, through its body, its contract, or a callee's
  contract, is not verified: ``Unresolved`` with reason
  ``construct.unsupported`` (``relies on choice, which uses a construct the
  verifier does not support``). An uncontracted ``constexpr`` helper that
  verified code calls is such a spec.

An error about the function as a whole, such as a recursion without a
measure, points at its name. With ``--diagnostics-format=json`` the record of
a function's first error carries its verdict and the range, here
``"function":"pick"``, ``"status":"unresolved"``,
``"reason":"construct.unsupported"``, and ``"source":{"column":14,
"end_column":20,"end_line":4,"file":"pick.cpp","line":4}``. Before 0.2 such an
error stopped the file, so that no function of it got a verdict, and named
only the function: ``error: pick: unsupported statement: CXXThrowExpr``.

The message names the construct as C++ does: ``goto``, labels, a computed
``goto``, ``throw`` and ``try``, inline assembly, a statement expression, a
compound literal, a lambda, a pointer into a string literal or to
``__func__``. A construct without a name of its own is ``this expression is
unsupported`` or ``this statement is unsupported``, with Clang's class name
in parentheses for a bug report: an OpenMP directive is ``this statement is
unsupported (OMPSimdDirective)``. Each is reported once: a variable whose
initializer was rejected, and a call that was, report nothing more where
they are used. Before 0.2 the message gave Clang's class name alone
(``unsupported expression: StmtExpr``), a lambda was ``aggregate
initialization and copying are unsupported``, a string literal used as a
pointer was ``array-to-pointer decay of automatic storage is unsupported``,
and each use of a variable whose initializer was rejected added ``read of
uninitialized local value``.

What a run prints
~~~~~~~~~~~~~~~~~

A run prints a verdict for each function it verifies, in source order, then
one line that counts them:

.. code-block:: cpp

   namespace cv = cppverify;

   cv::spec int twice(int x) { return 2 * x; }

   int add_one(int x)
     cv::pre(x < 100)
     cv::post(cv::result == x + 1)
   {
     return x + 1;
   }

   int add_two(int x)
     cv::pre(x < 100)
     cv::post(cv::result == twice(x))
   {
     return x + 2;
   }

.. code-block:: text

   Verified: add_one [backend=z3]
   summary.cpp:14:23: error: verification failed: add_two [postcondition] [backend=z3] [reason=counterexample]
      14 |   cv::post(cv::result == twice(x))
         |            ~~~~~~~~~~~^~~~~~~~~~~
   summary.cpp:14:23: note: counterexample: x = 3, result = 5
   summary.cpp:16:3: note: returns 5
      16 |   return x + 2;
         |   ^
   Summary: 1 verified, 1 failed in 0.0 s

A failure prints as Clang prints an error: the kind of check that fails
(``[postcondition]``), the backend and the reason, and the source with a caret
under the part of the check that fails (below); then a note with the
counterexample's values by their source
names, in the order the source declares them (``result`` last), each with
the values it takes along the path in turn (``i = 0 -> 1``), not those of
branches the path does not take, and a reference as the address it refers to
(``&r = 4``); then a note at each step
of the path it takes: the branches, the calls with their arguments, a loop's
entry and an arbitrary iteration of it, the memory it writes, and the value it
returns. A path of more than ten steps shows its first and last five. A step
inside a macro is shown where the macro is used, and an operation whose own
check fails is no step of the path: a failing check in ``return e;`` ends the
path before the return. A value
the counterexample does not determine is ``<unknown>``. JSON keeps what the
text leaves out (see `Structured diagnostics`_). Errors and warnings show their
source line the same way; verdicts are one line each.

The part of a check that fails is the one the counterexample's values make
false:

- in a clause written as a conjunction, its first conjunct that is false:
  for ``cv::post(0 <= cv::result && cv::result <= 50)`` and a result of 51,
  ``cv::result <= 50``. A disjunction fails only when every part of it does,
  and is shown whole;
- for a check that an operation is defined (``[overflow]``,
  ``[division-by-zero]``, ``[bounds]``, ...), the operation, with the caret
  at its operator, under the conditions around it (a branch, the left side
  of ``&&``), not the statement it is in;
- for a callee's precondition, the call, with the caret at the callee's
  name. A note shows the callee's clause that does not hold there, its
  conjunct that is false.

.. code-block:: cpp

   namespace cv = cppverify;

   int half(int x)
     cv::pre(0 <= x && x % 2 == 0)
     cv::post(cv::result * 2 == x)
   {
     return x / 2;
   }

   int odd_half(int y)
     cv::pre(0 <= y && y <= 100)
   {
     return half(2 * y + 1);
   }

   int area(int w, int h)
     cv::pre(0 <= w && 0 <= h)
   {
     int a = w * h + 1;
     return a;
   }

.. code-block:: text

   Verified: half [backend=z3]
   half.cpp:13:10: error: verification failed: odd_half [precondition] [backend=z3] [reason=counterexample]
      13 |   return half(2 * y + 1);
         |          ^~~~~~~~~~~~~~~
   half.cpp:13:10: note: counterexample: y = 0
   half.cpp:4:27: note: this precondition does not hold at the call
       4 |   cv::pre(0 <= x && x % 2 == 0)
         |                     ~~~~~~^~~~
   half.cpp:13:10: note: calls half(1)
      13 |   return half(2 * y + 1);
         |          ^
   half.cpp:19:17: error: verification failed: area [overflow] [backend=z3] [reason=counterexample]
      19 |   int a = w * h + 1;
         |           ~~~~~~^~~
   half.cpp:19:17: note: counterexample: w = 1, h = 2147483647
   Summary: 1 verified, 2 failed in 0.0 s

At ``w = 1`` the product fits and the sum overflows, so the caret is at
``+``. When the values do not decide which part is false (one that needs a
spec the checker cannot evaluate), the failure is shown at the whole
condition, or for an operation at its statement. A check inside a lifted
``constexpr`` helper is shown at the statement that calls the helper, as
before. Before 0.2 every failure was: the whole clause, the statement for an operation or a call, and the
callee's clause was not shown.

The summary counts each kind of verdict the run reported (verified, which
includes ``Certified`` and ``Proved (z3+lean)``, failed, unresolved,
bounded-safe, trusted, lowered, exported, interrupted), gives the reasons of
the unresolved ones (``2 unresolved (spec.fuel 1, solver.timeout 1)``), and
the time the run took. A function the verifier does not represent counts as
unresolved, ``construct.unsupported``. The summary covers every file of the
run. In JSON it is the last record, and in SARIF a property of the run (see
`Structured diagnostics`_); ``--list-functions`` and archive replay
(``--obligation-in``), which prints a line per module, have none.

- ``--quiet`` prints only what needs attention: failures, unresolved results,
  errors, warnings, bounded results, and interrupted functions, then the
  summary. For the example, the error line and the summary.
- ``--verbose`` also lists each spec function that needs no check, a
  non-recursive spec without a postcondition: ``Verified: spec axiom: twice``.
  Such a line is not a verdict and the summary does not count it. Before 0.2
  it was printed always.
- ``--list-functions`` lists the functions a run would verify, each with its
  location and kind (``function``, ``spec``, ``constexpr spec``, ``proof``,
  ``trusted``), and verifies none; errors about functions the verifier does
  not represent are printed as a run prints them:

.. code-block:: text

   summary.cpp:3:14: spec twice
   summary.cpp:5:5: function add_one
   summary.cpp:12:5: function add_two

``--function=PATTERN`` reports only the functions whose names match the glob
pattern (``*``, ``?``, ``[...]``; repeatable, a function matching any is
reported), as ``Verified`` and the other lines print the name: ``Ring::push``,
``total<short>``; an inductive predicate is reported with the checks generated
for it (its step's termination and induction, its rule proofs). Every verdict
it reports is the one a run of the whole file gives: the functions whose
contracts those verdicts rely on are verified too, round by round, and so
are all spec and proof functions, whose facts any
proof may use; their results are not printed, and a selected function that
relies on a callee whose verification fails is ``Unresolved`` with
``callee.contract`` exactly as in a whole run. An executable function no
reported verdict relies on is not verified at all. The exit status follows
what is reported: 0 when every reported verdict is a proof. A pattern that
matches no function is an error. With ``--list-functions`` it narrows the
listing.

``--time-report`` adds, after a file's verdicts, where its run spent its time,
then each function it reported, the busiest first. Here ``small_power``'s
counterexample is confirmed by a proof after inductions are tried, ``grows``
is proved by induction, and ``after_loop`` fails after a loop that
unrolling then checks:

.. code-block:: text

   $ cpp-verify --time-report file.cpp
   ...
   Time report (seconds): conversion 0.001, verification 4.412, settling 0.151
        total  lowering   solving  induction  certification  confirmation  function
        4.559     0.001     4.408      3.917          7.577         0.150  small_power
        1.767     0.001     1.766      0.014          3.292         0.000  grows
        0.062     0.002     0.022      0.000          0.000         0.038  after_loop
        0.027     0.001     0.026      0.000          0.000         0.000  fibo
        0.026     0.001     0.025      0.000          0.000         0.000  proved
        0.022     0.001     0.021      0.000          0.000         0.000  pow2
   Summary: 4 verified, 2 failed in 4.6 s

For the run:

- **conversion**: from the parsed file to the functions the verifier
  verifies (Clang's parsing comes before it; the summary's time covers it);
- **verification**: verifying every function, at once with several jobs;
- **settling**: what follows: the verdicts that rest on other functions'
  contracts and on spec facts, confirmations by proof, Lean certification.

For a function:

- **total**: its verification, and the confirmations of its counterexamples
  by proof that run after every function is verified;
- **lowering**: preparing its checks, and passivizing and lowering them to
  obligations;
- **solving**: in the backends: encoding, solving, checking counterexamples,
  inductions, and a proof's vacuity checks;
- **induction**: the part of solving spent on automatic inductions;
- **certification**: checking the solvers' counterexamples against the true
  definitions, summed over the checks; with several jobs they run at once,
  so it can exceed solving;
- **confirmation**: unrolling the loops after a failure (``--confirm-bound``)
  and confirming a counterexample by proof.

A function's total is its lowering, solving, and confirmation. With
``--diagnostics-format=json`` the report is records of the schema
``cppverify.time/1``: one for the run, whose ``seconds`` has
``conversion``, ``verification``, and ``settling``, then one per function,
with ``function`` and the six ``seconds`` of its row. The report needs source
verification (not ``--obligation-in``).

On a terminal, a line on standard error counts the functions done as they
finish (``[12/40] parse_header``); the results follow once every verdict is
settled. ``--progress`` shows the line anywhere, and ``--progress=false``
hides it.

``cpp-verify --help`` shows each time limit's default (``--timeout``,
30000 ms).

Stopping a run with Ctrl-C
~~~~~~~~~~~~~~~~~~~~~~~~~~

Ctrl-C (``SIGINT``) stops the run at once, however long its queries are:

- every solver stops, Z3 and cvc5 alike, and so does a counterexample check
  in progress;
- each function whose verification had not finished is reported as
  ``Interrupted: f`` (JSON ``"status":"unresolved"`` with reason
  ``interrupted``), and its partial results are not printed;
- a proof that rests on the contract of an interrupted function is not
  established, so its caller is ``Unresolved`` with reason
  ``callee.contract``; a proof that rests only on finished functions keeps
  its verdict;
- the input files not yet read are skipped, and ``cpp-verify`` exits with
  status 130, as a shell expects after Ctrl-C;
- a second Ctrl-C ends the process at once, without a report.

.. cppverify-example: fragment

.. code-block:: cpp

   int fast(int x)
     cv::pre(0 <= x && x < 100)
     cv::post(cv::result == x + 1)
   {
     return x + 1;
   }

   cv::proof void cubes(int x, int y, int z)   // no solver settles this
     cv::pre(x > 0 && y > 0 && z > 0)
     cv::post(x * x * x + y * y * y != z * z * z)
   {
   }

.. code-block:: text

   $ cpp-verify --timeout=600000 slow.cpp --
   ^C
   Verified: fast [backend=z3]
   slow.cpp:8:16: Interrupted: cubes
   $ echo $?
   130

Before 0.2, Ctrl-C printed an LLVM crash report and the run went on, or the
process crashed, because each Z3 check installed its own signal handler.

Versions
~~~~~~~~

``cpp-verify --version`` shows the cpp-verify release and repository revision, the LLVM
release it is built on, and each backend: the Z3 linked into it, and the cvc5 and Lean
(``lake``) it finds on ``PATH`` with their versions. cvc5 is tested with 1.1.2, the
release Ubuntu 24.04 packages, and 1.4.2, the newest: CI runs the test suite with each.
A query that needs a constant array, as every one over sets, multisets, and maps does,
sets cvc5's ``arrays-exp`` option itself, which 1.4 requires. Every Lean
project pins ``leanprover/lean4:v4.35.0``, and certification runs that toolchain whatever
elan's default is: through elan it names the pin, since elan otherwise picks a toolchain
by the working directory, and a ``lake`` outside elan must report the pinned Lean. A
project an earlier release generated, pinned to ``leanprover/lean4:v4.32.2`` by 0.1, is
moved to the current pin the next time cpp-verify writes it, with a warning; a proof that
no longer builds needs updating for the new Lean. Any other pin is an error.

When cpp-verify crashes
~~~~~~~~~~~~~~~~~~~~~~~

A crash is a bug in cpp-verify, never a verdict about the program. The process
stops with a stack dump that starts like this:

.. code-block:: text

   PLEASE submit a bug report to https://github.com/SwayamInSync/cpp-verify/issues/ and include the crash backtrace and instructions to reproduce the bug.
   Stack dump:
   0.	Program arguments: cpp-verify crash.cpp --

Report it there with the whole output, the command, the output of
``cpp-verify --version``, and the smallest source that reproduces it. ``clang++``
from the same build names the same address. A build directory configured before
0.2 keeps LLVM's address in its CMake cache; configure it again with
``-UBUG_REPORT_URL``, or use a new one.

Options that select a backend, and options a run would not use
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An option that only one backend uses selects that backend when ``--backend``
is not given:

.. list-table::
   :header-rows: 1
   :widths: 40 60

   * - Option
     - Selects
   * - ``--unroll=N``
     - ``--backend=bmc``
   * - ``--lean-out=FILE``, ``--lean-project=DIR``
     - ``--backend=lean``

So ``cpp-verify --unroll=4 file.cpp`` runs bounded model checking and prints
results such as ``Verified: swapped_difference [backend=bmc, bound=0]``.

An option that the run would not use is an error naming what it needs, and
nothing is verified:

.. list-table::
   :header-rows: 1
   :widths: 45 55

   * - Command
     - Error
   * - ``--backend=z3 --unroll=3``
     - ``error: --unroll requires --backend=bmc``
   * - ``--backend=z3 --cvc5-path=PATH``
     - ``error: --cvc5-path requires --backend=cvc5, --backend=portfolio, or --backend=race``
   * - ``--backend=cvc5 --profile-quantifiers``
     - ``error: --profile-quantifiers requires a backend that runs Z3: z3, portfolio, race, or bmc``
   * - ``--lean-out=FILE --timeout=60000``
     - ``error: --timeout requires a backend that runs an SMT solver``
   * - ``--proof-cache-max-mb=N`` without ``--proof-cache``
     - ``error: --proof-cache-max-mb and --proof-cache-max-entries require --proof-cache``
   * - ``--lean-fallback-scope=all`` without ``--lean-fallback``
     - ``error: --lean-fallback-scope requires --lean-fallback``
   * - ``--lean-prune-stale`` without ``--lean-project`` or ``--lean-fallback``
     - ``error: --lean-prune-stale requires --lean-project or --lean-fallback``
   * - ``--no-lean-auto`` without ``--lean-project`` or ``--lean-fallback``
     - ``error: --no-lean-auto requires --lean-project or --lean-fallback``
   * - ``--lean-auto-timeout=N`` without ``--lean-project`` or ``--lean-fallback``
     - ``error: --lean-auto-timeout requires --lean-project or --lean-fallback``

Lean export runs no solver, so every solver option is an error with
``--backend=lean``, ``--lean-out``, or ``--lean-project``, the same way as
``--timeout`` above: ``--timeout``, ``--collection-timeout``,
``--certify-timeout``, ``--function-timeout``, ``--solver-rlimit``,
``--memory-limit``, and ``--int-encoding``. ``--max-query-nodes`` bounds what
is built for every backend, Lean's included. ``--lean-fallback`` runs Z3
first, and accepts all of them.

The same rules hold when replaying an archive: ``--check-ub`` and
``--profile-quantifiers`` are errors there, since an archive keeps the checks
it was written with, and ``--unroll`` must match the bound a BMC archive
records. Before 0.2, ``--lean-out`` and ``--lean-project`` needed an explicit
``--backend=lean``, ``--unroll`` without ``--backend=bmc`` ran Z3 and reported
an unbounded ``Verified``, and the other options above were ignored without a
word.

Backends
--------

.. list-table::
   :header-rows: 1
   :widths: 22 78

   * - Flag
     - Meaning
   * - ``--backend=z3``
     - Default. Weakest precondition + Z3 (loops via contracts on the WP path).
   * - ``--backend=cvc5``
     - Encode each canonical obligation as standalone SMT-LIB2 and run an
       installed cvc5. ``unsat`` is ``Verified``, ``sat`` is ``Failed``, and
       unavailable/malformed/unknown execution is ``Unresolved``.
   * - ``--backend=portfolio``
     - Strictly run Z3 and cvc5 on each ordered canonical obligation. Only
       matching ``unsat`` results are ``Verified`` and matching ``sat`` results
       are ``Failed``. A timeout, missing solver, malformed output, unsupported
       query, or opposite verdict is ``Unresolved``; decisive disagreement uses
       reason ``backend.inconsistent-results``.
   * - ``--backend=race``
     - Run Z3 and cvc5 at once on each function, as Frama-C's prover list:
       the first proof or certified counterexample stands and stops the
       other solver. Where neither settles the function, the obligations
       each proved are joined, and the function is ``Verified`` when they
       cover all of them (``[backend=z3+cvc5]``). The tag names the solver
       that settled it. Unlike ``portfolio`` it never waits for agreement:
       every proof and every counterexample is already sound on its own.
   * - ``--cvc5-path=FILE``
     - Use this cvc5 executable instead of searching ``PATH``. cvc5 is an
       optional system dependency and is not vendored.
   * - ``--backend=bmc``
     - Incrementally unroll loops from zero through ``--unroll=N`` (default 10),
       stopping at the first counterexample, complete unwinding proof,
       unresolved query, or maximum frontier. A spec's own checks have no
       loops and run as with Z3 (reported as ``z3``). As Kani reports an
       unreachable check, a bounded result that no execution reaches is
       ``[vacuous]`` with a warning: an unsatisfiable precondition, or
       ``no execution finishes within N loop iterations``.
   * - ``--backend=lean``
     - Write an unchecked Lean 4 scratch-pad to ``--lean-out``. This path does
       not run Z3 and reports ``Exported``, never ``Verified``. Multi-function
       output uses one shared preamble and identity-qualified theorem names.
   * - ``--lean-project=DIR``
     - With ``--backend=lean``, which it selects, generate a pinned editable project. Generated
       semantics live in a module per function, ``CppVerify/Goals/<function>.lean``,
       with each spec they apply declared once in ``CppVerify/Specs.lean``: by
       its definition when the pinned Lean proves that it terminates, the
       verdict kept in ``.cppverify/specs``, and opaque otherwise; a
       proof imports its function's module, so certification compiles again
       only the proofs of a function whose goals changed, and a generated
       file is written only when its text changes. Reusable lemmas and
       per-obligation proof files are preserved across regeneration. A goal
       is named by its function and the hash of its statement
       (``cppverify_one_99bcee_postcondition_cd6bdfcd``), and its proof file,
       ``CppVerify/Proofs/<function>/<goal>.lean``, records that hash, so a
       proof stays with its statement: it moves with a renamed function,
       a proof whose statement changed or whose function is gone is kept in
       ``Stale/`` with a note, and it comes back when a goal has its
       statement again. A warning names every move. A project 0.1 generated
       is moved to these names, with the names its proofs use
       (:doc:`../book/part-ii/ch17-backends-modular-calls`). Each goal
       ``G`` also has a readable form, ``G.readable``, its assumptions as
       hypotheses named by where they come from (``h_pre_1``,
       ``h_call_next_2``, ``h_x_1`` for the definition of ``x_1``), and a
       bridge ``G.of_readable : G.readable → G`` that the kernel checks with
       the generated file, so a proof of either form proves ``G``. A stub
       applies the bridge and introduces every name. Each new goal is first
       given to ``cppverify_auto`` (``CppVerify/Auto.lean``), with the pinned
       Lean if it is installed: a goal it proves gets that proof, and the
       export says how many, as in ``Exported: lean obligation: next
       (cppverify_auto proved 3 of 3 goals)``; any other goal gets a stub that
       says it was tried (:doc:`../book/part-ii/ch17-backends-modular-calls`).
       Each
       goal means what its obligation means: every operator keeps its
       grouping under Lean's precedence, a numeral has its type (``Nat``
       would read ``2 - 3`` as 0), a Boolean is a proposition
       (``↔``), machine division by zero is SMT-LIB's
       (``BitVec.smtUDiv``, ``BitVec.smtSDiv``), as in the solvers, and
       ``decide`` evaluates the machine comparisons at constants
       (:doc:`../book/part-ii/ch17-backends-modular-calls`).
   * - ``--lean-certify``
     - Build the active project with the pinned Lean 4.35.0, each proof file on
       its own and without ``sorry`` (``--jobs`` of them at once), then check
       the compiled modules with a
       program that elaborates none of the user's source: the kernel replays
       every module of the project a proof imports, the proof must state
       exactly its goal, and it may depend on no axiom but ``propext``,
       ``Quot.sound``, and ``Classical.choice``. A function whose goals all
       pass is ``Certified``; one that has a goal that fails is ``Unresolved``,
       with the obligation and why, such as ``the proof of
       fn_…::postcondition@8:37: …_proof proves True, not …``, whatever the
       other functions' proofs are. Certification runs whatever else failed,
       before the facts verdicts rest on are settled: a result proved in
       Lean rests on the callee contracts and spec facts its module uses, as
       a solver's does, and gets the same qualifiers and vacuity checks (run
       with Z3). Requires ``--lean-project`` or ``--lean-fallback``.
   * - ``--lean-fallback=DIR``
     - On the Z3 or strict-portfolio path, export functions that remain
       ``Unresolved`` to an editable Lean project, for example
       ``Exported: lean fallback: f [z3: 18 of 20 proved; lean: 2 exported]``.
       Initial export remains a non-success result. Rerun with
       ``--lean-certify`` after completing the preserved proof files: a
       function whose exported goals all kernel-check reports
       ``Proved (z3+lean)`` (JSON ``"status":"mixed-proof"`` with an
       ``evidence`` record), or ``Certified`` when Lean checked every goal.
       A certified counterexample stays a failure, and the project gets its
       refutation, ``CppVerify/Refutations/<function>/<goal>.lean``; with
       ``--lean-certify`` a refutation that checks adds ``(confirmed in
       Lean)`` to the failure (JSON ``"lean_refuted": true``), one Lean
       cannot decide a warning, and one Lean decides the other way makes the
       function ``Unresolved`` (``backend.inconsistent-results``).
   * - ``--lean-fallback-scope=unproved|all``
     - ``unproved`` (default) exports only the obligations the solver did not
       prove individually; each keeps the goal name it has in a complete
       export. ``all`` exports every obligation of the function, so success
       is ``Certified``. Requires ``--lean-fallback``. A fallback run
       examines in Lean only what its solver leaves unresolved, so it leaves
       the proofs of the other obligations and functions where they are.
   * - ``--lean-prune-stale``
     - Delete the proofs a Lean project keeps in ``Stale/``, after the
       regeneration has taken back those a goal has the statement of:
       ``warning: removed the 4 Lean proofs kept in Stale/, as
       --lean-prune-stale asks``. Without it, nothing is ever deleted but an
       unedited stub. Requires ``--lean-project`` or ``--lean-fallback``.
   * - ``--no-lean-auto``
     - Write a stub for each new Lean goal without trying ``cppverify_auto``
       on it. Requires ``--lean-project`` or ``--lean-fallback``.
   * - ``--lean-auto-timeout=N``
     - Milliseconds of wall-clock time ``cppverify_auto`` may spend on one
       new goal, its kernel check included (default 20000; ``0`` disables). A
       goal that takes longer gets a stub, as in ``automation:
       cppverify_auto 3 did not prove it within 20 s``. Requires
       ``--lean-project`` or ``--lean-fallback``.
   * - ``--unroll=N``
     - Maximum BMC loop bound, which selects ``--backend=bmc``. Source verification
       explores ``0..N``; lower-only and archive replay retain one exact recorded bound,
       which a replayed ``--unroll`` must match, and only a BMC archive has one.
   * - ``--check-ub``
     - The default. On every backend, prove each memory access lies in an
       object: a ``valid(p, n)`` precondition declares a buffer extent, and a
       pointer without one addresses a single object. Indexed accesses,
       pointer arithmetic, modular sub-slices, and same-array pointer
       positions are checked. Extent markers must be positive top-level
       conjunction clauses on bare pointers. See :doc:`integers` and
       :doc:`pointers`.
   * - ``--no-check-ub``
     - Turn memory checking off. Core expression definedness (overflow,
       division, shifts, and dereferences of null or dead storage) is always
       checked. Region ``cppverify::modifies`` footprints then forget the whole heap at
       a call. Neither flag applies to archive replay: an archive keeps the checks
       it was written with.
   * - ``--profile-quantifiers``
     - For a quantified Z3 query left unresolved, rerun it counting each
       quantifier's instantiations and report the busiest, by the source
       location of the quantifier (``note: the quantifier at L:C was
       instantiated N times, up to generation G``; JSON
       ``quantifier_profile``). Use it to find matching loops and poor
       triggers. Needs a POSIX host, source verification, and a backend that
       runs Z3: ``z3``, ``portfolio``, ``race``, or ``bmc``.
   * - ``--timeout=N``
     - Per-query solver timeout in milliseconds (default 30000; ``0`` disables).
       A query that exceeds it is reported as unresolved instead of hanging.
       Not accepted with ``--backend=lean``, which runs no solver.
   * - ``--certify-timeout=N``
     - The milliseconds checking one counterexample against the true
       definitions may take (default half of the query timeout; ``0`` lets
       it take the query's own time). A slow check leaves the rest of the
       query's time to other models and later stages; when it is reached the
       reason says so (``the time one counterexample check may take (N ms,
       --certify-timeout) was spent``).
       Not accepted with ``--backend=lean``, which runs no solver.
   * - ``--collection-timeout=N``
     - Per-query timeout for a function whose queries involve sequences,
       sets, multisets, or maps, whose theories need more search (default
       twice ``--timeout``; ``0`` disables).
       Not accepted with ``--backend=lean``, which runs no solver.
   * - ``--solver-rlimit=N``
     - Deterministic per-query Z3/cvc5 resource budget (default ``0``, disabled).
       Exhaustion is ``Unresolved``. Z3 reports ``solver.resource-limit``;
       cvc5 may report the conservative ``solver.unknown``.
       Not accepted with ``--backend=lean``, which runs no solver.
   * - ``--max-query-nodes=N``
     - The expression nodes the verifier may build for one function (default
       4000000; ``0`` disables): its proof obligations and the facts about the
       specs they apply, counted as they are built, a shared node once. A
       function over it is ``Unresolved`` with reason ``query.size-limit``,
       under every backend; cvc5's scripts and archive records, which state
       shared terms in full, are checked against it too. See
       `Memory limits`_.
   * - ``--memory-limit=MB``
     - The megabytes the solvers may use (default 8192; ``0`` disables): Z3's
       queries together, and each cvc5 process. A query that reaches it is
       ``Unresolved`` with reason ``solver.memory-limit``. Not accepted with
       ``--backend=lean``, which runs no solver. See `Memory limits`_.
   * - ``--int-encoding=MODE``
     - Solver representation of machine integers for Z3, cvc5, portfolio, and
       BMC: ``auto`` (default; integers reduced modulo ``2^N`` unless a query
       needs the bits of a non-constant operand, then bit-vectors),
       ``integer``, or ``bitvector``. Every mode is exact; only solver
       performance differs. Not accepted with ``--backend=lean``. See :doc:`integers`.
   * - ``--jobs=N``
     - Solver workers, shared by every function and obligation: functions
       are verified at once, a function's obligations run on the same
       workers, and its whole query races them. Results are published in
       source order (default: every physical core, or ``CPPVERIFY_JOBS``;
       ``0`` selects every core). Lean export remains serial; ``cppverify_auto``
       and certification run this many Lean processes at once (default: every
       physical core).
   * - ``--function-timeout=N``
     - Milliseconds all queries of one function may take together (default
       ten times ``--timeout``; ``0`` disables). See `Time limits`_.
       Not accepted with ``--backend=lean``, which runs no solver.
   * - ``--proof-cache=DIR``
     - Persist successful dependency-scoped Z3 or BMC proofs. In portfolio mode
       this caches only the Z3 component and cvc5 still runs on every query.
       Standalone cvc5 does not use this cache. Failed,
       unresolved, and bounded-safe results are never proof-cache entries.
       Corrupt or incompatible entries are rejected rather than treated as hits.
   * - ``--proof-cache-max-mb=N``
     - Bound proof-cache storage in MiB (default 1024; ``0`` disables the byte
       limit). Requires ``--proof-cache``.
   * - ``--proof-cache-max-entries=N``
     - Bound the number of proof-cache records (default 100000; ``0`` disables
       the entry limit). Requires ``--proof-cache``.
   * - ``--diagnostics-format={text,json,sarif,github}``
     - Select Clang-style text (default); JSON Lines of
       ``cppverify.diagnostic/2`` records ending with a
       ``cppverify.summary/1`` record; one SARIF 2.1.0 log at the end of the
       run; or the text with a GitHub workflow annotation for each error and
       warning (see `Structured diagnostics`_).
   * - ``--lower-only``
     - Run Clang conversion, backend-specific preparation, passivization,
       canonical Obligation IR construction, spec-axiom encoding, and selected
       Z3/SMT-LIB translation without calling a solver. Supported for Z3, cvc5,
       portfolio, and BMC.
   * - ``--dump-smt2=DIR``
     - Write every query sent to Z3 or cvc5 to ``DIR``, each as a script the
       solver replays on its own (see `Solver queries as scripts`_).
   * - ``--obligation-out=FILE``
     - Write deterministic, versioned backend-neutral modules with portable
       source attribution and SHA-256 semantic identities. Multiple modules are
       concatenated in one archive.
   * - ``--obligation-in=FILE``
     - Validate and replay an archive without reparsing C++. Supports Z3, cvc5,
       strict portfolio, ``--lower-only``/Layer 3-4 dumps, Lean scratch
       export, and Lean projects (``--lean-project``, with certification).
       Archives
       produced after BMC unrolling retain their bound and replay with BMC
       unwinding semantics, in Lean too; applying BMC to an untransformed
       archive is rejected because unrolling must run before obligation
       lowering.
       Each module is replayed on its own, without the callee and trusted
       contracts, spec facts, partiality, and vacuity its source verdict
       rests on: a module whose obligations all hold reports ``Proved
       obligations: f (dependencies not checked in replay)`` (JSON
       ``"status":"proved-obligations"``), never ``Verified``.

``--lower-only`` is deliberately different from compiler ``-fno-verify``.
``-fno-verify`` stops after Clang syntax and contract semantic checks;
``--lower-only`` exercises the complete verification pipeline through backend
encoding. A successful run prints ``Lowered: function``. That means the formula
was constructed and encoded, **not** that its obligations are true.

Backend results are intentionally distinct. Z3 ``unsat`` reports ``Verified``;
a ``sat`` model reports a failed source obligation once it is checked against
the true definitions (otherwise ``Unresolved`` with a reason); timeout and
``unknown`` report ``Unresolved``. cvc5 follows the same mapping, and its models
are checked the same way, then shown the same way: a failure's counterexample
and path, in text and in JSON's ``counterexample``, ``model``, and ``trace``,
come from the checked model.
Portfolio mode requires agreement; an agreed ``sat`` result uses Z3's typed
model and trace, while disagreement or incomplete secondary evidence is
``Unresolved``. BMC reports ``BoundedSafe: f [backend=bmc, bound=N]`` when only its unwinding
obligation fails at the maximum frontier, and reports ``Verified`` only when an
explored bound proves complete unwinding. Text diagnostics publish the terminal
``bound``, all attempted ``bounds``, and the count of successful ordered queries
reused across prefixes. JSON uses ``bound``, ``explored_bounds``, and
``reused_queries``. Lean generation reports ``Exported``. Only the pinned,
admission-free kernel workflow reports ``Certified``.

Solver queries as scripts
-------------------------

``--dump-smt2=DIR`` writes each query cpp-verify sends to a solver as an
SMT-LIB script that the solver runs on its own: ``z3 FILE`` or ``cvc5
FILE``, with no other flags. Such a file is what a solver's bug report
needs, what compares two solver versions on the same query, and what shows
the exact formula behind a verdict. On ``clamp.cpp`` (from
:doc:`../book/part-ii/ch17-backends-modular-calls`):

.. code-block:: text

   $ cpp-verify --dump-smt2=queries clamp.cpp
   ...
   $ find queries -type f | sort
   queries/clamp-14e9c9/missing-return-7-3.z3-c326aaab.smt2
   queries/clamp-14e9c9/overflow-8-5.z3-19b38e3e.smt2
   queries/clamp-14e9c9/postcondition-5-23.z3-d86b7e26.smt2
   queries/clamp-14e9c9/whole.z3-3a4644f7.smt2

A function's queries are in a directory named by the function and the start
of the SHA-256 hash of its identity, so overloads stay apart; each file is
named by its obligation (``postcondition-5-23``, the postcondition at line 5,
column 23), or ``whole`` for every obligation at once, then the solver and
the start of the hash of the script itself. A name depends only on the query,
so the same query is the same file in every run, and two checks of one
obligation (a refinement round after the first check, say) are two files.
A check that cpp-verify adds is named after the function and the check,
every character but a letter, a digit, or ``_`` made ``_``: ``f_smoke``
holds the vacuity checks of ``f``, and ``f_decreases`` the termination check
of a spec ``f``.

A file starts with comments that say what it is, then the options cpp-verify
gives the solver, as commands, then the query and its check. After the check
come ``(get-model)`` when the answer was ``sat``, and the answer cpp-verify
got:

.. code-block:: text

   ; cpp-verify 0.2.0-dev, z3 4.13.4
   ; clamp: the postcondition check at clamp.cpp:5:23 (fn_5f5a35636c616d7069::postcondition@5:23)
   ; replay: z3 clamp-14e9c9/postcondition-5-23.z3-d86b7e26.smt2
   (set-option :timeout 30000)
   (set-option :rlimit 6000000)
   (set-option :smt.mbqi true)
   (set-option :smt.qi.eager_threshold 0.0)
   (declare-fun __result_1 () Int)
   (declare-fun x_0 () Int)
   ...
   (check-sat)
   (get-model)
   ; cpp-verify: sat

.. code-block:: text

   $ cd queries && z3 clamp-14e9c9/postcondition-5-23.z3-d86b7e26.smt2
   sat
   (
     (define-fun __result_1 () Int
       (- 1))
     ...
     (define-fun x_0 () Int
       (- 2))
   )

- **Which queries.** Every check a solver makes: the whole query and each
  obligation's, every refinement round, the probes of a bounded domain, the
  native-definition pass, the inductions, the confirmations, the vacuity and
  contract checks, and the queries of an archive's replay. A query is
  written before its check, so one that never returns still leaves its
  file, and the answer is appended when the check ends: ``sat``, ``unsat``,
  ``unknown`` with Z3's reason (``unknown (timeout)``), or, for cvc5, ``no
  answer`` with what went wrong. ``--lower-only`` checks nothing, so it
  writes nothing, and Lean writes its own project.
- **Options.** For Z3, the time the check was given (``:timeout``, which
  can be less than ``--timeout`` for a check late in a query's budget), the
  resource limit, and the quantifier settings, and ``(check-sat-using smt)``
  where cpp-verify solves a quantified query with the ``smt`` tactic. For
  cvc5, its command-line options (``--seed=0``, ``--tlimit-per=N``, ...) as
  ``(set-option ...)`` commands.
- **Replaying.** ``z3 FILE`` with the version in the first line (``z3
  --version``; cpp-verify links Z3 4.13.4) and ``cvc5 FILE`` give the answer
  cpp-verify got for most queries. Z3's search on a quantified query depends
  on the order in which its terms were created, and a replay creates them
  as it reads the file, in another order than cpp-verify did, so such a
  query can end differently, typically ``unknown`` where cpp-verify got an
  answer.
- **Errors.** A directory that cannot be written is a warning at the end of
  the run (``warning: --dump-smt2: cannot create ...``); verdicts do not
  change.

Time limits
-----------

Three limits bound how long verification takes:

- ``--timeout`` bounds **one** solver query (default 30 s). A query that
  reaches it is unknown, never a proof or a counterexample.
- ``--collection-timeout`` replaces it for queries over sequences, sets,
  multisets, or maps (default twice ``--timeout``).
- ``--function-timeout`` bounds **all** queries of one function together,
  measured in wall-clock time from the function's first query (default ten
  times ``--timeout``, so five minutes).

A function rarely needs only one query. The verifier tries the whole
function as one query, then each obligation on its own, and may retry a
query in another integer encoding, by induction, or with refined
definitions; with ``--int-encoding=bitvector`` and ``--timeout=5000``,
``extent_separation.cpp``'s ``copy`` spends 32 s across such queries before
it is proved. The function budget lets that happen while still stopping a
function that would otherwise run for hours, such as one with hundreds of
hard obligations. Each query gets at most the time the function has left,
and once it is spent no further query starts: the function is
``Unresolved`` with reason ``solver.timeout`` and the message ``the
function's time (--function-timeout) is spent``. Nothing else changes, so a
result is never worse than ``Unresolved`` because of the budget.

Choosing the limits:

- Interactive use: the defaults. A function that reaches the budget is
  usually one to split, or to help with lemmas, assertions, or
  ``cppverify::reveal_with_fuel``.
- A large function that legitimately needs many queries (many obligations
  verified on one job): raise ``--function-timeout``, or set it to ``0``.
- Continuous integration with a time allowance per function: set
  ``--function-timeout`` to that allowance; ``--timeout`` then only bounds
  single queries inside it.
- With ``--jobs`` above one, a function's queries run at once, so the same
  budget covers more of them.

The limits are wall-clock times and depend on the machine. For results that
must repeat exactly across machines, use ``--solver-rlimit``, a
deterministic per-query budget of solver steps.

None of these limits applies to Lean, which runs no solver; ``cppverify_auto``
has a limit of its own, ``--lean-auto-timeout``. Lean
certification (``--lean-certify``) gives each ``lake`` step 300 seconds:
building the generated module, compiling your module, compiling each proof,
and the final check. A step that takes longer leaves every result
``Unresolved`` with reason ``lean.export-failed``, and its message gives the
command's error.

Memory limits
-------------

Two limits bound the memory verification takes:

- ``--max-query-nodes`` bounds what the verifier builds for **one** function
  (default 4,000,000 expression nodes): its proof obligations, and the facts
  about the specs they apply. Both are counted as they are built and stop at
  the limit, so a function over it ends before it takes the memory. A node
  that several terms share is counted once, as it takes memory once.
- ``--memory-limit`` bounds the solvers (default 8192 MB): Z3's queries
  together, since Z3 runs inside cpp-verify, and each cvc5 process on its
  own.

A function that reaches either is ``Unresolved``, never a proof or a
counterexample, and every function whose proof relies on its contract is
``Unresolved`` with reason ``callee.contract``. Nothing else changes.

The proof obligations of a function grow faster than its code. Each check is
proved from everything before it (the preconditions, the statements, and the
earlier checks): its obligation states each as an assumption, sharing its
terms with the other obligations, so a function whose checks follow many
statements takes about their number times its checks' (not times their
sizes). With two, four, and eight checks like the four below, the
obligations take 259, 523, and 1,375 nodes. With a limit of 400:

.. cppverify-example: flags --max-query-nodes=400
.. cppverify-example: unresolved steps
.. code-block:: cpp

   int steps(int x)
     cppverify::pre(0 <= x && x <= 100)
     cppverify::post(cppverify::result == x + 4)
   {
     int y = x;
     y = y + 1;
     cppverify::check(y == x + 1);
     y = y + 1;
     cppverify::check(y == x + 2);
     y = y + 1;
     cppverify::check(y == x + 3);
     y = y + 1;
     cppverify::check(y == x + 4);
     return y;
   }

.. code-block:: text

   steps.cpp:1:5: Unresolved: steps [backend=z3] [reason=query.size-limit] (the proof obligations would take at least 427 expression nodes, more than the limit of 400 (--max-query-nodes): each check repeats every assumption before it, so split the function or raise the limit)

The count is where building stopped, so the function needs at least that
many. Its obligations take 523 nodes, and the checks that a proof is not
vacuous build programs of their own, the largest with 901: with
``--max-query-nodes=901`` the function verifies. Under ``--lower-only`` the
same is an error, ``Z3 lowering failed: steps``, since no obligations were
built. A function split into functions with
contracts keeps each one's obligations small: a call repeats the callee's
contract, not its body.

The default admits the largest function of the test suite,
``iterative_fibonacci`` in ``safe_fib.cpp`` (375,000 nodes, with the
definitions of the specs it applies), ten times over; the ULEB128 case study
(:doc:`../case-studies/llvm-uleb128`) takes under 200,000 a function. A node
takes about 600 bytes, and Z3's encoding of it about five times that, so the
default lets one function take up to about 12 GB; with more than one job,
each job builds the obligations of its own function at once.

An SMT-LIB script, which the cvc5 backend writes, and an archive record
(``--obligation-out``) state each term in full: a subterm that several
obligations share is written at each of its places, so they are larger than
what is built. Each is checked against the same limit, as the nodes it
would state: a module whose script would be larger is ``Unresolved`` with
``query.size-limit`` under cvc5 (``its SMT-LIB script would state more than
N expression nodes``), and one whose record would be larger is an error with
``--obligation-out``.

The facts about the specs a function applies include each spec's definition,
unfolded as deep as its fuel. A spec that applies itself twice doubles with
every level: at fuel 40, ``fibo``'s unfolding would have about 2^40 copies of
its body. Its unfolding stops where it passes the limit, which, at the
default, takes a few seconds:

.. cppverify-example: flags --max-query-nodes=200000
.. cppverify-example: unresolved unfolds
.. code-block:: cpp

   cppverify::spec int fibo(int n)
     cppverify::decreases(n)
   {
     return n <= 1 ? n : fibo(n - 1) + fibo(n - 2);
   }

   int unfolds(int n)
     cppverify::pre(n == 3)
     cppverify::post(cppverify::result == fibo(3))
   {
     cppverify::ghost { cppverify::reveal_with_fuel(fibo, 40); }
     return 2;
   }

.. code-block:: text

   Verified: spec decreases: fibo
   fibo.cpp:7:5: Unresolved: unfolds [backend=z3] [reason=query.size-limit] (the facts about the specs it applies (at each application, their definitions unfolded as deep as their fuel, and their postconditions) would take at least 228066 expression nodes, more than the limit of 200000 (--max-query-nodes): lower the fuel cppverify::reveal_with_fuel gives, or raise the limit)

cpp-verify enforces ``--memory-limit`` while Z3 checks a query: every 10 ms
it compares what Z3 has allocated, all its queries together, with the limit,
and stops the query once it is past it. A matching loop, in which every
instance of a quantifier makes a term that matches it again, takes memory
until something stops it; without the limit that is the timeout, at 2 GB
after 20 s:

.. cppverify-example: flags --memory-limit=100 --timeout=60000
.. cppverify-example: unresolved matching_loop
.. code-block:: cpp

   cppverify::spec int g(int n)
     cppverify::decreases(n)
   {
     return n <= 0 ? 0 : g(n - 1);
   }

   void matching_loop(int a)
     cppverify::pre(cppverify::forall(k, cppverify::trigger(g(k)) == g(k + 1) + 1))
   {
     cppverify::ghost { cppverify::hide(g); }
     cppverify::check(g(a) > 100);
   }

   int small(int x)
     cppverify::pre(x < 100)
     cppverify::post(cppverify::result == x + 1)
   {
     return x + 1;
   }

.. code-block:: text

   Verified: spec decreases: g
   loop.cpp:11:3: Unresolved: matching_loop [backend=z3] [reason=solver.memory-limit] (proof obligation fn_5f5a31336d61746368696e675f6c6f6f7069::assertion@11:3: Z3 reached the memory limit: its queries share 100 MB (--memory-limit))
   Verified: small [backend=z3]

The memory of a stopped query is freed, so the next one runs within the
limit. Since Z3's queries share it, one that passes it stops every query
running beside it, which, like the time limits on a loaded machine, can leave
a function ``Unresolved`` that would verify alone; with ``--jobs=1`` a query
has the limit to itself. Under ``--int-encoding=bitvector`` a query stopped
for memory is retried in the integer encoding, as after a timeout.

cvc5 runs as a process of its own, which may allocate up to the limit. Past
it an allocation fails and cvc5 stops (``std::bad_alloc``, its SAT solver's
``OutOfMemoryException``, or GMP's ``Cannot allocate memory``), and the query
is ``Unresolved`` with reason ``solver.memory-limit``: ``cvc5 ran out of memory: each cvc5 process
may use N MB (--memory-limit)``. The limit is applied on Linux, to the data
the process may allocate, and on Windows, to its committed memory; on macOS,
which applies no such limit to the memory a process maps, cvc5 is not
bounded. With several jobs, as many cvc5 processes may run at once. An
allocation that fails where cvc5 does not check it crashes cvc5 instead
(``cvc5 terminated by signal 11``), which is reported as
``solver.invocation-failed``, since a crash need not come from memory; at a
few megabytes it happens at limits that differ between cvc5's versions and
builds.

Choosing the limits:

- Interactive use: the defaults. A function over ``--max-query-nodes`` is
  usually one to split into functions with contracts.
- A machine with little memory: lower ``--jobs`` first, since each job
  builds one function's obligations at once, then the two limits.
- Continuous integration with a memory allowance: give ``--memory-limit``
  the solvers' share, and ``--max-query-nodes`` the rest divided by
  ``--jobs`` and by 3,000 bytes.

Parallel solving and proof caching
----------------------------------

``--jobs`` sets one pool of exactly that many workers. Each function is a
task on it, with its own backends; its obligations are tasks on the same
pool (a task waiting for them runs its own unstarted ones itself, never
another function's, so the pool never grows and a function whose queries
are done reports at once), and
with workers to spare its whole query races the obligations solved one by
one: both are exact, so a proof by either decides the function and
interrupts the other. A query over sequences is also solved without the
sequence index facts, which help proofs but slow the search for
counterexamples. Dumps, archives, and diagnostics are buffered per
function and published in source order, and the cross-function steps (callee
contracts, spec termination, trust) run after every function. Each worker
owns a fresh Z3 context/solver or a separate cvc5 process; no solver state is
shared between workers. The first failing source obligation is therefore
identical for ``--jobs=1`` and ``--jobs=N`` even if worker completion order
differs. The complete query of a function without spec functions first gets
a fixed amount of solver work (Z3 resource units), with the query timeout
only as a bound in time, so on a loaded machine it stops where it stops on
an idle one, unless the timeout passes first; once it has found a
counterexample, the obligations that choose the failure to report get the
same work each. Likewise, the search for the least and greatest values of a
spec's argument, which finds a counterexample at the end of its range, is
bounded by solver work and by the CPU time of its own thread, which the load
of other processes does not use up. Lean generation stays serial; ``cppverify_auto`` and
certification run Lean processes side by side; what they find does not depend
on how many, but a goal whose automation is near ``--lean-auto-timeout`` may
finish in time under one load and not under another. The compile-time
verifier (``clang++ -fverify-contracts``) always uses one job and the default
limits; use ``cpp-verify`` for ``--jobs`` and the other options.

With ``--proof-cache``, CppVerify solves and caches individual ordered
obligations. A cache key combines the dependency-scoped semantic hash, semantic
hash format, backend namespace, adapter version, and exact Z3 version. BMC uses a
separate namespace, and its unroll provenance is semantic, so a bounded proof
cannot satisfy an unbounded Z3 lookup or another bound. Target widths, layout
constants, UB instrumentation, spec fuel, and other relevant choices are already
lowered into the canonical goal and its reachable declarations.

Only ``Verified`` obligations are written, using immutable records and atomic
replacement. Counterexamples, timeouts, resource exhaustion, unknown results,
and ``BoundedSafe`` frontiers are solved again. A malformed or unreadable lookup
produces ``cache.corrupt`` or ``cache.io-failed`` rather than proof success.
Failure to store a fresh proof is reported as cache-error telemetry but does
not invalidate that solver verdict. The cache is pruned to its limits once,
after the run's last lookup, so functions verified side by side see the same
entries; a failure to prune is reported as a warning. Pruning still runs after
cache errors, retries capacity-limited writes after eviction, and removes
abandoned atomic-write files after 24 hours while leaving newer concurrent
writes alone. Text results show ``[cache=hits/queries]`` and JSON records carry
``cache.hits``, ``cache.misses``, and ``cache.errors``. The same cache is usable
during source verification and canonical archive replay. It is a trusted local
memoization store, not a portable proof certificate: do not share a cache
directory with untrusted writers. Use Lean certification when independent
kernel checking is required.

Structured diagnostics
----------------------

A failure names the kind of the check that fails, as ``[overflow]``. The
kind says what the check is:

- contracts: ``assertion``, ``precondition``, ``postcondition``,
  ``invariant-entry``, ``invariant-preserved``, ``termination``,
  ``type-invariant``, and ``cppverify::recommends``;
- C++ definedness: ``overflow`` (including a mathematical value converted to
  a machine type it does not fit), ``division-by-zero``, ``shift``,
  ``bounds``, ``dereference``, ``initialization``, ``pointer-difference``,
  ``deallocation``, and ``builtin-argument`` (an argument a builtin is
  undefined for, such as ``__builtin_clz(0)``);
- generated interfaces: ``pointer-validity`` (a pointer parameter, result, or
  ``valid(p, n)`` extent must denote valid storage), ``aliasing`` (implicit
  non-aliasing), ``frame`` (writes and callee effects stay within
  ``cppverify::modifies``), and ``missing-return``;
- ``unreachable``: a failed ``assert`` or a call that does not return
  (``abort``, ``exit``, ``std::terminate``, ``__builtin_unreachable``,
  ``__builtin_trap``) is reached;
- ``unwinding`` for a BMC bound, and ``unsupported`` for a construct the
  verifier rejects fail-closed.

The check that a function's contract is defined (see :doc:`functions-loops`)
is reported only when it fails, as ``contract of f``, with the definedness
kinds above; JSON records give ``f`` as the function.

JSON Lines
~~~~~~~~~~

``--diagnostics-format=json`` prints one ``cppverify.diagnostic/2`` record
per result, and the run ends with one ``cppverify.summary/1`` record, the
counts of the text summary by name (``verified``, ``failed``,
``unresolved`` with its ``reasons``, ``bounded_safe``, ``trusted``,
``lowered``, ``exported``, ``interrupted``). No record holds a time, so a
run's records are the same at any ``--jobs``; ``--time-report`` adds
``cppverify.time/1`` records. A record has:

- ``status`` (``verified``, ``failed``, ``unresolved``, ``warning``,
  ``frontend``, ...), ``severity`` (``error``, ``warning``, ``note``), and
  ``message``, the text of its line; for a failure, ``reason``;
- ``function``, and ``function_source``, the function's name where it is
  declared;
- ``source``, what the result is about: for a failure the part of its
  check that fails (see `What a run prints`_). A source is ``file``, ``line``, ``column``, ``end_line``,
  ``end_column``: from its first character to the column after its last, as
  SARIF and editors count, on presumed (``#line``) lines;
- for a failure, ``obligation`` with the check's ``id`` and ``kind``;
  ``counterexample``, the values as the note prints them; ``model``, every
  value with its source name, its internal SSA name (``ssa_name``), its sort
  (``bool``, ``i32``, ``u32``, ``math-i32``, ``pointer``, ``heap``, ...), and
  ``"on_path": false`` for a version of a branch the path does not take; and
  ``trace``, each step with its ``kind``, its ``text`` as the note prints it,
  and ``active``;
- for a failure at a call, ``related``: the callee's clause that does not
  hold, with its ``message`` and ``source``;
- ``notes``, ``backend``, ``bound``, ``trusts``, ``vacuous``, ``partial``,
  ``instantiated_at``, and the other qualifiers of the text.

The check's ID is source-anchored, such as
``function-identity::overflow@line:column#2``: the line and column of the
check as the verifier builds it, a clause's operator or the statement that
an operation or a call is in. The caret may point closer, at the part that
fails, and the ID stays. The local suffix only disambiguates checks of one kind at the same
anchor, so inserting or reordering an unrelated check does not renumber later
IDs unless its source anchor moves. Z3 model completion is disabled:
undetermined values print as ``<unknown>`` and become JSON ``null``. Signed
and unsigned bit-vectors are decoded to source-level decimal values.

The compiler's own diagnostics are records of status ``frontend``: a parse
error, a warning with its ``option`` (``-Wparentheses``), each with the notes
that follow it as ``related``, a message and a source each. They come before
the verifier's records of their file. Only an error in ``cpp-verify``'s own
options, which stops the run before it starts, stays text on standard error.

Before 0.2 the schema was ``cppverify.diagnostic/1``: a record had no
``function_source``, and none for a verified function at all; a source
started at the check's caret and ended at the first column of its last token;
the message held the check's ID and every value with its SSA name and sort;
compiler errors were text; and no record ended the run.

SARIF
~~~~~

``--diagnostics-format=sarif`` prints one SARIF 2.1.0 log when the run ends,
made from the same records, for GitHub code scanning and SARIF viewers. Each
record is a result, after Frama-C's mapping of property statuses: a proof
passes (``kind: pass``), a failure fails (``fail``, level ``error``), and a
result no verdict settles stays open (``open``). The result's rule is the
kind of the failing check (``postcondition``, ``overflow``, ...), or
``verified``, ``unresolved``, ``warning``, ``frontend``; its location is the
record's source and its function, its message the text with the
counterexample, and the path a code flow, each step at its line with its
text. A failure at a call has the callee's clause as a related location.
The run's properties hold the summary.

GitHub annotations
~~~~~~~~~~~~~~~~~~

``--diagnostics-format=github`` prints the text, and after each error and
warning a workflow command that GitHub Actions turns into an annotation on
the source, its file relative to the working directory (the checkout, in a
workflow). For ``summary.cpp`` above, after the error and its notes:

.. code-block:: text

   ::error file=summary.cpp,line=14,col=12,endLine=14,endColumn=34,title=cpp-verify%3A postcondition::verification failed: add_two [postcondition] [backend=z3] [reason=counterexample]%0Acounterexample: x = 3, result = 5

A failure at a call adds the callee's clause to the message, with its place:
``%0Athis precondition does not hold at the call (half.cpp:4:27)``.

Counterexample traces may contain guarded branch, modular-call, loop,
heap-write, allocation/provenance, lifetime-end, deletion, and return events.
False guards are omitted; a guard the model does not determine is retained with
JSON ``"active": null`` rather than an invented path choice. Archives preserve
the same names, ranges, IDs, and trace data during replay, and a replayed
failure is shown at the same part of its check.

A failure may carry notes, printed after it as ``note:`` lines and in JSON as
``notes``: a counterexample that passes through a loop starts from any state
the loop's invariants allow, and what unrolling each loop then finds about
the same check, within ``--confirm-bound`` iterations (default 10; ``0``
skips it; only with the solver backends, since BMC unrolls already and Lean
runs no solver): an execution that fails it, a proof that none does, or no
failure within the bound. The search takes at most one query timeout. Unrolling
drops the loops' invariants and measures, so a failure of one gets no
search: it would find no copy of the check at any bound. A loop without
``cppverify::decreases`` is noted too (see :doc:`functions-loops`).

A function reports one failure: the first check that fails, in the order an
execution meets them. ``--max-failures=N`` reports the first ``N``, and
``--max-failures=0`` every one, each with its own counterexample and notes,
as Dafny reports every failing assertion of a method (only with
``--backend=z3``). A check after the first failure is solved in the
executions that pass the failing checks before it, as Boogie assumes an
assertion once it has checked it: its counterexample reaches it without
failing an earlier check, and a check that fails only where an earlier one
fails is not reported, since fixing that one fixes it. The summary still
counts each function once:

.. cppverify-example: flags --max-failures=0
.. code-block:: cpp

   namespace cv = cppverify;

   int three_bugs(int x, int y)
     cv::pre(x < 1000 && y < 1000)
     cv::post(cv::result > 0)
   {
     int q = 10 / y;
     int r = x + q;
     return r;
   }

.. code-block:: text

   $ cpp-verify --max-failures=0 three_bugs.cpp
   three_bugs.cpp:7:14: error: verification failed: three_bugs [division-by-zero] [backend=z3] [reason=counterexample]
       7 |   int q = 10 / y;
         |           ~~~^~~
   three_bugs.cpp:7:14: note: counterexample: x = 0, y = 0
   three_bugs.cpp:8:13: error: verification failed: three_bugs [overflow] [backend=z3] [reason=counterexample]
       8 |   int r = x + q;
         |           ~~^~~
   three_bugs.cpp:8:13: note: counterexample: x = -2147483648, y = -9, q = -1
   three_bugs.cpp:5:23: error: verification failed: three_bugs [postcondition] [backend=z3] [reason=counterexample]
       5 |   cv::post(cv::result > 0)
         |            ~~~~~~~~~~~^~~
   three_bugs.cpp:5:23: note: counterexample: x = 0, y = 11, q = 0, r = 0, result = 0
   three_bugs.cpp:9:3: note: returns 0
       9 |   return r;
         |   ^
   Summary: 1 failed in 0.0 s

Without the option only the first line is printed. The overflow's
counterexample divides by ``y = -9``, not by zero, and the postcondition's
returns from an execution with no undefined operation. In JSON each failure
is a record of its own.

Each non-success verification result also carries a stable reason code. Current
codes include ``counterexample``, ``solver.timeout``, ``solver.unknown``,
``solver.resource-limit``, ``solver.memory-limit``, ``solver.unavailable``,
``solver.invocation-failed``, ``solver.malformed-output``,
``query.size-limit``, ``encoding.failed`` (the obligations could not be
encoded for the solver; when Z3 rejected a call, the message quotes it:
``Z3 reported an error: ...``),
``obligation.invalid``, ``logic.unsupported``, ``query.missing``,
``backend.invalid-result``,
``backend.inconsistent-results``, ``bmc.incomplete-bound``,
``lean.export-failed``, ``cache.corrupt``, ``cache.io-failed``,
``spec.fuel``, ``spec.hidden``, ``spec.termination``, ``spec.reads``,
``spec.post``, ``spec.inductive``, ``proof.cycle``,
``counterexample.unchecked``,
``callee.contract``,
``decreases.missing``, ``construct.unsupported``, and ``interrupted``.

A result settled by an automatic induction says which, as ``[by induction
following fibo]`` (JSON ``induction``); an unresolved one lists the
inductions tried (``induction_tried``) and, when the solver proposed a
counterexample its check could not evaluate, that input and the application
it could not compute (``unchecked_counterexample``, with ``application`` and
``model``). A counterexample confirmed by a proof at its input names the
``cppverify::proof`` functions whose contracts the proof used (``confirmed_with``). For
example (other fields left out):

.. code-block:: text

   {"function":"even_mod","induction":"following even","status":"verified",...}
   {"function":"fibo_small","induction_tried":["following fibo","on n"],"reason":"spec.fuel","status":"unresolved","unchecked_counterexample":{"application":"fibo(1000000000)","model":[{"name":"n","ssa":"n_0","type":"i32","value":"1000000000"}]},...}
   {"confirmed_with":["fibo_at_least_5"],"function":"fibo_small","reason":"counterexample","status":"failed",...}

The last line is the same claim once the lemma ``fibo_at_least_5`` is
proved; see :doc:`../book/part-ii/ch13-spec-and-proof-functions`.

What a verified result rests on
-------------------------------

A verified result may carry qualifiers that say what the proof assumed:

- ``[partial]``: it holds only for terminating executions, after
  ``cppverify::decreases(*)`` here or in a callee (JSON ``"partial": true``).
- ``[trusts=f,g]``: it relies on the contracts of ``f`` and ``g``, marked
  ``[[cppverify::trusted]]``, directly or through verified callees (JSON
  ``"trusts": ["f", "g"]``). Each trusted function itself reports
  ``Trusted: f (contract assumed, not verified)`` (JSON ``"status":
  "trusted"``). See :doc:`functions-loops`.
- ``[vacuous]``: no execution reaches the claim, so it holds for no reason
  (JSON ``"vacuous": true``), with a warning naming the cause. A result that
  is ``Unresolved`` because it relies on a fact that is not established keeps
  it only where that fact cannot be the cause: an unsatisfiable precondition
  is still reported when the missing fact is a callee's contract.

A proof can only hold vacuously when an assumption excludes every execution,
and assumptions enter a function in a few places: its preconditions and type
invariants, its behaviors' assumptions, and the contracts of its callees.
Every ``Verified`` result is checked at each:

.. list-table::
   :header-rows: 1
   :widths: 35 65

   * - Cause
     - Warning
   * - The preconditions (with type invariants) are unsatisfiable.
     - ``f: the precondition is unsatisfiable, so every claim about it holds
       vacuously``
   * - No execution reaches the end of the function.
     - ``f: no execution reaches the end, so its postcondition holds
       vacuously; check the contracts it calls and its assumptions``
   * - A behavior's assumption contradicts the preconditions.
     - ``f: behavior b never applies: its assumption contradicts the
       preconditions, so its postconditions are never checked`` (the result
       itself is not ``[vacuous]``: the other behaviors were checked)
   * - A trusted contract cannot hold in the state of one call.
     - ``f: the trusted contract of g contradicts the state of this call, so
       everything after it holds vacuously``, at the call

A verified callee always returns, so only a trusted contract can end the
paths through a call. Unreachable code itself is not flagged: a defensive
``if (p == nullptr) return -1;`` under ``cppverify::pre(p != nullptr)`` is dead for a
good reason, and every claim the function makes is still checked on the
paths that remain.

Combining JSON or SARIF with IR dumps intentionally creates a mixed stream.
Malformed byte sequences in source or archive display text are rendered with
the Unicode replacement character, so every emitted JSON record remains valid
UTF-8.

Portable obligation archives
----------------------------

An archive holds the verification conditions of a file's functions, so they
can be checked again, by another solver or on another machine, without the
C++ source:

.. code-block:: cpp

   int abs_value(int x)
     cv::pre(x > -2147483647 - 1)
     cv::post(cv::result == (x < 0 ? -x : x))
   {
     return x < 0 ? -x : x;
   }

   int twice_abs(int x)
     cv::pre(-1000 < x && x < 1000)
     cv::post(cv::result >= 0)
   {
     int a = abs_value(x);
     return 2 * a;
   }

.. code-block:: text

   $ cpp-verify --obligation-out=abs.cpv abs.cpp --
   Verified: abs_value [backend=z3]
   Verified: twice_abs [backend=z3]
   $ cpp-verify --obligation-in=abs.cpv
   Proved obligations: abs_value (dependencies not checked in replay) [backend=z3] [semantic-hash=sha256:...]
   Proved obligations: twice_abs (dependencies not checked in replay) [backend=z3] [semantic-hash=sha256:...]

Replay proves each function's obligations, but a verdict also rests on
facts outside them: ``twice_abs`` is ``Verified`` only because
``abs_value``'s contract is, and an archive does not record that. Replay
therefore reports ``Proved obligations``, JSON status
``proved-obligations``, never ``Verified``. The same holds for what spec
facts, trusted contracts, ``[partial]``, and the vacuity checks add to a
source verdict. A counterexample in replay is still a failure: it is checked
against the definitions the archive carries. Before 0.2, replay printed
``Verified`` for each module whose obligations held, even when the source
run did not verify the function, for example when a callee's verification
failed.

An archive replays into a Lean project with ``--lean-project``, optionally
with ``--lean-certify``, ``--lean-prune-stale``, ``--no-lean-auto``,
``--lean-auto-timeout``, and ``--jobs``: the project gets the goals, specs,
and proof files a source run of the same program gives, and a module whose
goals all certify is ``Proved obligations`` ``[backend=lean]``. A bounded
record of BMC goes to Lean too, its bound stated with its goals; its
module is ``BoundedSafe`` when every goal but some unwinding goal
certifies (:doc:`../book/part-ii/ch17-backends-modular-calls`).
``--lean-fallback`` applies to source verification only.

``--obligation-out`` writes ``cppverify.obligation/6`` records only after exact
serialize/deserialize/validate/reserialize checks. Stable wire tags make the
format independent of C++ enum ordinals. The reader rejects malformed magic,
unsupported versions, truncation, invalid tags, inconsistent feature
declarations, duplicate identities, and oversized/deep expressions.
Schema v2 adds the precise obligation kinds; schema v3 each spec function's
termination measures, read like its definition, and, with source metadata,
where each assumption of a goal comes from, which names a hypothesis of a
readable Lean goal; schema v4, with source metadata, where each variable
version of a counterexample is defined, so a replayed counterexample lists the
values its path takes; schema v5 where each source range begins, its end
being the column after its last character; schema v6, with source metadata,
where each check's condition and a callee's clause lie, so a replayed failure
is shown at the part that fails. Records of schemas v5 to v2, and
of schema v1, which name only assertions, postconditions, and unwinding
checks, are still read; a counterexample replayed from one before v4 lists
the values of every version, a range from one before v5 begins at its
anchor and ends at the first column of its last token, and a failure
replayed from one before v6 is shown at its check's anchor.
Records cap integer widths at 4096 bits, expression depth at 4096, and
collections plus expression nodes/edges at 100,000 per record. It also rejects
embedded NULs, non-canonical numerals, inactive payload fields, ill-scoped
variables, conflicting module-wide free-symbol sorts across semantic and
diagnostic expressions, and contradictory complete/ordered queries before
backend dispatch.

Module and per-obligation SHA-256 hashes omit source paths and display-only
names, source ranges, internal positional and public source-anchored IDs,
obligation kinds other than ``unwinding``, traces, measures, and where
assumptions come from, so moving unchanged
source, inserting an unrelated earlier obligation, or changing display metadata
preserves an individual goal's semantic identity.
Archives still
retain that metadata for replay diagnostics. Failure-triggered
``cppverify::recommends`` warnings are diagnostic-only and do not make archive bytes depend
on a solver result. BMC transform provenance is semantic: it is retained in
archives and hashes so bounded obligations cannot be mistaken for unbounded
deductive proofs.

Before hashing or backend dispatch, source-built and replayed modules use the
same conservative canonicalizer. It folds Boolean constants, double negation,
constant conditionals, and reflexive equality/inequality, then removes logical
declarations unreachable from every ordered goal. Exact goal/query pairs and
required features are rebuilt and revalidated. Arithmetic, quantifiers,
pointer/heap terms, and assumptions are left intact. Semantic-hash format v2
introduced this canonical boundary, format v3 excluded positional and public
diagnostic identities, and format v4 keeps only whether an obligation is an
unwinding check.

Supported compiler
------------------

Contract syntax and ``-fverify-contracts`` exist **only in this repository's
Clang**. Use the shipped ``./build/bin/cpp-verify`` and
``./build/bin/clang++`` for any code that uses contracts — stock GCC or upstream
Clang reject the flag and the contract constructs. Code that those compilers
also build guards the constructs with the predefined ``__cppverify__``
(:doc:`syntax`, "Headers shared with other compilers"). (Building cpp-verify
itself from source is independent and works with any standard host compiler.)

Compile with contracts (``clang++``)
------------------------------------

.. code-block:: bash

   clang++ -std=c++17 -fverify-contracts -c file.cpp -o file.o   # compile + verify
   clang++ -std=c++17 -fno-verify -fsyntax-only file.cpp         # light syntax/semantics check

Two independent axes
~~~~~~~~~~~~~~~~~~~~~

Contract behaviour is governed by **two** switches, not one. Understanding the
split is the whole game:

.. list-table::
   :header-rows: 1
   :widths: 30 18 52

   * - Switch (flag)
     - Default
     - What it controls
   * - **Contract language**

       ``-fverify-contracts`` / ``-fno-verify-contracts``
     - off
     - Whether the parser recognises ``cppverify::pre``/``cppverify::post``/``cppverify::ghost``/``cppverify::spec``/… (and
       therefore whether CodeGen strips them). This is the **master** switch — with
       it off, the file is byte-identical to stock C++ and the verifier never runs.
   * - **Run the prover**

       ``-fno-verify``
     - on (when contracts are on)
     - Whether the SMT verifier runs (in a thread, parallel to code generation).
       The verifier runs by default once contracts are enabled; ``-fno-verify``
       skips it. There is no ``-fverify`` — it would just be the default.

``-fno-verify`` is meaningless without the contract language, so it **implies
-fverify-contracts** (unless you explicitly pass ``-fno-verify-contracts``). That
makes a lone ``-fno-verify`` a fast *light check*: it validates C++ syntax,
contract syntax, **and** contract semantics (the ``cppverify::old``/``cppverify::result`` placement and
bool-convertibility rules), but does **not** check your logic. Ideal for
editors, CI pre-flight, and LLM/agent loops.

Results in a compilation
~~~~~~~~~~~~~~~~~~~~~~~~

``clang++ -fverify-contracts`` reports what it verifies as its own
diagnostics, in the format ``cpp-verify`` prints: a failure is an error with
its notes, an unresolved result is an error, a warning is a warning in
``-Wcppverify`` (``-Wno-cppverify`` hides it and ``-Werror=cppverify`` makes it
an error), and a proof is a remark at its function, shown with
``-Rcppverify``. Colors,
``-fdiagnostics-format=sarif``, and editors that read the compiler's
diagnostics show them as they show Clang's:

.. code-block:: text

   $ clang++ -std=c++17 -fverify-contracts -Rcppverify -c summary.cpp -o summary.o
   summary.cpp:5:5: remark: Verified: add_one [backend=z3] [-Rcppverify]
       5 | int add_one(int x)
         |     ^
   summary.cpp:14:23: error: verification failed: add_two [postcondition] [backend=z3] [reason=counterexample]
      14 |   cv::post(cv::result == twice(x))
         |            ~~~~~~~~~~~^~~~~~~~~~~
   summary.cpp:14:23: note: counterexample: x = 3, result = 5
   summary.cpp:16:3: note: returns 5
      16 |   return x + 2;
         |   ^
   1 error generated.

Before 0.2 the compiler printed the verifier's lines as text, and then the
one error ``cppverify: verification failed``: ``-fdiagnostics-format=sarif``
gave a document without results, and ``-w`` and ``-Werror`` changed nothing.

Options of a compilation
~~~~~~~~~~~~~~~~~~~~~~~~

A compilation verifies with ``cpp-verify``'s defaults, Z3 and 30 seconds a
query, and one solver job. These options change that for the files they are
given to:

.. list-table::
   :header-rows: 1
   :widths: 38 62

   * - Option
     - Meaning (the ``cpp-verify`` option)
   * - ``-fverify-backend=z3|cvc5|portfolio|race|bmc``
     - The solver (``--backend``). Lean projects stay with ``cpp-verify``.
   * - ``-fverify-timeout=<ms>``
     - Each query's time (``--timeout``, 30000 by default, ``0`` disables);
       a query over collections gets twice it, and one function's queries
       together ten times it, as with ``cpp-verify``.
   * - ``-fverify-jobs=<n>``
     - Solver jobs for each compilation (``--jobs``), 1 by default, since a
       build compiles several files at once: ``make -j8`` with
       ``-fverify-jobs=2`` runs up to 16.
   * - ``-fverify-cache=<dir>``
     - Proofs kept in ``<dir>`` (``--proof-cache``), shared by every
       compilation that names it, so an unchanged obligation is not solved
       again.
   * - ``-fverify-report``, ``-fverify-report=<file>``
     - The results as JSON Lines records (``--diagnostics-format=json``),
       ending with the summary record, in ``<object>.cppverify.json`` beside
       the object file, or in ``<file>``.
   * - ``-fverify-contracts-out=<file>``
     - The contracts the file verifies and those it assumes, for
       ``cpp-verify --check-contracts`` (Contracts across files, in
       :doc:`functions-loops`).

An invalid value is an error of the compiler
(``error: invalid value 'lean' in '-fverify-backend=lean'``). A file without a
function to verify says nothing, as most files of a project have none;
``cpp-verify`` still warns ``no verifiable functions found`` for one. Before
0.2 a compilation always verified with the defaults, and every file without
contracts warned.

Verification in a CMake build
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Configure the build with this compiler
(``-DCMAKE_CXX_COMPILER=/path/to/build/bin/clang++``) and give the options to
the targets whose code has contracts:

.. code-block:: cmake

   option(VERIFY "Verify contracts while compiling" ON)
   if(VERIFY)
     target_compile_options(app PRIVATE -fverify-contracts -fverify-jobs=2
       -fverify-cache=${CMAKE_BINARY_DIR}/cppverify-cache -fverify-report)
   else()
     target_compile_options(app PRIVATE -fno-verify)
   endif()

A failure is an error of the compilation, so the build stops at it and
writes no object. ``-DVERIFY=OFF`` still checks the contracts' syntax and
meaning (``-fno-verify``), without the solver, for fast development builds,
and the objects are the same either way, since contracts emit no code. With
``-fverify-report`` each object's results lie beside it, for a CI step to
collect.

Quick lookup
~~~~~~~~~~~~

.. list-table::
   :header-rows: 1
   :widths: 34 14 14 38

   * - Flags (with ``clang++``)
     - Contracts
     - Verify
     - Result
   * - *(none)*
     - off
     - —
     - Plain C++: the constructs are not recognized, so a file that uses them does not
       compile. Zero overhead.
   * - ``-fverify-contracts``
     - on
     - **yes**
     - **Full**: compile **and** verify in parallel. A failed contract is a compile error.
   * - ``-fno-verify``
     - on *(implied)*
     - no
     - **Light**: parse + Sema + compile, skip the solver. Catches syntax/semantic
       errors, ignores logic.
   * - ``-fno-verify -fsyntax-only``
     - on *(implied)*
     - no
     - Fastest light check — no code generation either.
   * - ``-fno-verify-contracts``
     - off
     - —
     - Off entirely. Combined with ``-fno-verify``, the explicit *off* wins.

The standalone ``cpp-verify`` tool normally runs the **full** path (it adds
``-fverify-contracts`` for you and does no code generation);
``--lower-only`` is its explicit solver-free verification-IR mode.

Editor support
--------------

The build also produces ``clangd`` and ``clang-format`` from the same sources, so an editor
sees contracts exactly as the compiler does. With them:

- contract syntax and semantics errors appear as you type, with quick fixes for a
  construct written without its qualifier;
- hovering a construct (``cv::pre``, ``cv::forall``, ``cv::result``, ...) shows its
  documentation, and hovering a function shows its contract;
- go to definition, find references, rename, document highlights, and semantic
  highlighting reach into function clauses, loop clauses, and type invariants. Renaming a
  parameter, a spec function, or the alias ``cv`` updates every contract that uses it;
- completion after ``cv::`` lists the constructs with their documentation, and the
  ``<cppverify.h>`` collections;
- ``clang-format`` puts each clause on its own line and the body's brace below them, as it
  does for a trailing ``requires`` clause, and writes a range footprint as ``p[lo : n]``
  (before 0.2 it wrote ``p [0:n]``, as if the brackets began an Objective-C message):

  .. code-block:: text

     void fill(int *p, int n, int v)
       cv::pre(valid(p, n) && n >= 0)
       cv::modifies(p[0 : n])
       cv::post(cv::forall(k, 0, n, p[k] == v))
     {
       for (int i = 0; i < n; i = i + 1)
         cv::invariant(0 <= i && i <= n)
         cv::modifies(p[0 : n])
         cv::decreases(n - i)
       {
         p[i] = v;
       }
     }

clangd needs ``-fverify-contracts`` in each file's compile command. A
``compile_commands.json`` from a build that uses the flag provides it; otherwise add it in a
``.clangd`` file at the project root:

.. code-block:: yaml

   CompileFlags:
     Add: [-fverify-contracts]

Then point the editor at this clangd:

- **VS Code**: the clangd extension with ``"clangd.path": "/path/to/build/bin/clangd"``.
  Turn off the Microsoft C/C++ extension's own engine
  (``"C_Cpp.intelliSenseEngine": "disabled"``), which does not know the constructs.
- **Neovim** (nvim-lspconfig): ``cmd = { "/path/to/build/bin/clangd" }`` in the clangd setup.
- **Emacs**: ``eglot-server-programs`` or ``lsp-clients-clangd-executable``.
- **Others** (Sublime LSP, Zed, Helix, Qt Creator, Kate): set the clangd path in the
  language server settings.

A tool that does not use this build's parser (a stock clangd, Visual Studio's IntelliSense)
reports the constructs as errors, except those guarded by ``__cppverify__``, which it
does not define; a stock ``clang-format`` keeps every clause on the declarator's line. Tools built on this build's libclang see the contracts as well.

Contracts in Clang's other tools
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The contract constructs have a meaning for Clang's own analyses too: a
contract expression is never evaluated, and ghost code emits no code.

- A contract expression cannot throw, so ``noexcept`` of one is ``true``. It
  is not a constant expression either: a ``static_assert`` or an enumerator
  cannot use its value (``error: expression is not an integral constant
  expression``).

  .. code-block:: cpp

     static_assert(noexcept(cv::exists(k, 0, 3, k == 1)), "contracts do not throw");

- The static analyzer (``clang++ --analyze -fverify-contracts``) and the
  warnings computed from the control-flow graph skip ghost code and contract
  statements, so they analyze the code after them: a null dereference after a
  ``cv::ghost`` block or a ``cv::check`` is reported as it would be without them.
- libclang, and the tools built on it (``c-index-test``, the Python bindings,
  IDE indexers), shows each construct as an unexposed expression or statement
  (``CXCursor_UnexposedExpr``, ``CXCursor_UnexposedStmt``), with its operands
  as child cursors.
- A contract expression cannot appear in a mangled name yet: a template whose
  signature contains one, such as
  ``int (&)[sizeof(cv::exists(k, 0, 3, k == T()), T())]``, is reported when it is
  instantiated, with ``error: cannot yet mangle ExistsExpr expression``, as
  Clang reports other expressions without a mangling.

Before 0.2, ``noexcept`` of a contract expression crashed the compiler or
made it hang, as did a contract expression in a C++98 constant; the analyzer
ended every path at a ghost block, so it reported nothing after one; libclang
hid the constructs and, in a precondition, their operands; and a contract
expression in a template's signature was mangled to a malformed symbol.

Migrating from the keyword syntax
---------------------------------

Earlier versions wrote the constructs as keywords (``pre(x > 0)``,
``contract_assert(e)``). ``clang/tools/cpp-verify/cppverify-migrate.py`` rewrites C++
sources in place: each construct gains the qualifier and ``contract_assert`` becomes
``cppverify::check``, while comments and string literals stay as they are.

.. code-block:: bash

   python3 clang/tools/cpp-verify/cppverify-migrate.py src/*.cpp src/*.h
   python3 clang/tools/cpp-verify/cppverify-migrate.py --prefix=cv src/*.cpp  # writes cv::

With ``--prefix=cv``, declare ``namespace cv = cppverify;`` before the first construct.
Review the diff and compile with ``-fverify-contracts``: a construct the script missed is
an error whose fix-it writes the qualifier, which clangd offers as a quick fix.

IR dump layers
--------------

``--dump-ir`` accepts a comma-separated mask (or ``all``):

.. list-table::
   :header-rows: 1
   :widths: 12 88

   * - Layer
     - Content
   * - ``1`` / ``layer-1``
     - VCR IR — typed control flow, contracts preserved
   * - ``2`` / ``layer-2``
     - Passive IR — SSA, ``assume`` / ``assert``, heap versions
   * - ``3`` / ``layer-3``
     - Verification condition (logical formula)
   * - ``4`` / ``layer-4``
     - Z3 translation of the VC

Examples:

.. code-block:: bash

   cpp-verify --dump-ir=1 file.cpp
   cpp-verify --dump-ir=layer-3,layer-4 file.cpp
   cpp-verify --dump-ir file.cpp          # all layers

Layers are separated by a line of ``======`` in the output.

For lowering regressions, combine the dump with ``--lower-only``. This makes
VCR/passive/VC/Z3 ``FileCheck`` expectations independent of solver runtime:

.. code-block:: bash

   cpp-verify --lower-only --dump-ir=1 program.cpp
   cpp-verify --lower-only --dump-ir=2 program.cpp
   cpp-verify --lower-only --dump-ir=3 program.cpp
   cpp-verify --lower-only --dump-ir=4 program.cpp

Layer 4 still performs the complete Z3 encoding, including reachable spec
axioms, and fails closed on an encoding error. It only omits
``Solver.check()``.

Layer 3 is the canonical backend-neutral ``ObligationModule``. It prints the
same in-memory module consumed by Layer 4 and ordinary verification: explicit
logic sorts and required features, one complete counterexample query,
deterministic internal and source-anchored public obligation IDs/kinds, source
ranges, typed model metadata, guarded trace events, source encodings, and
equivalent ordered queries. A malformed, untyped, or unsupported term fails lowering rather than
becoming a proof-shaped default. Source-built dumps also report canonical
simplification node, rewrite, and dead-declaration counts.

Testing and coverage
--------------------

Regression tests live under ``clang/test/Verify/``, and lit runs them as
written, once the test tools that ``setup.sh`` does not build exist:

.. code-block:: bash

   ninja -C build FileCheck not count split-file llvm-config
   build/bin/llvm-lit clang/test/Verify

From the **repository root**:

.. list-table::
   :header-rows: 1
   :widths: 32 68

   * - Script
     - Purpose
   * - ``./scripts/run-verify-tests.sh``
     - A quick check without lit: run ``cpp-verify`` once on each test file,
       with only the backend and ``--no-check-ub`` of its RUN lines, for at
       most 60 s a file (``CPPVERIFY_TEST_TIMEOUT``). A file passes when it
       verifies, or reports an error where a RUN line expects one with
       ``not``; its FileCheck lines are not compared, and a long case study
       such as ``llvm_uleb128.cpp`` needs lit.
   * - ``./scripts/coverage-sweep.sh``
     - Fast profile merge after a normal build (from repo root).
   * - ``./scripts/coverage-verify.sh``
     - Full instrumented rebuild + sweep (slow; use when changing coverage setup).

Set ``CPPVERIFY_ENABLE_COVERAGE=ON`` on ``clangVerify`` only — not the whole LLVM tree.

``-DCPPVERIFY_SANITIZER="address;undefined"`` likewise builds only
``clangVerify`` and ``cpp-verify`` with the sanitizers, beside an
uninstrumented LLVM, Clang, and Z3. ``.github/workflows/cppverify-sanitize.sh
BUILD address`` runs every Verify test program that lit runs through such a
build and fails on any sanitizer report; CI does it every night. It turns off
poisoning by hand (``allow_user_poisoning=0``), which LLVM's allocators do in
the instrumented code's copies of their inline functions and not in the
libraries, and gives threads 1 GiB stacks.

ThreadSanitizer needs everything instrumented, since it sees only the
synchronization of instrumented code: ``-DLLVM_USE_SANITIZER=Thread`` builds
LLVM, Clang, the verifier, and the vendored Z3 with it. CI does this every
night too:

.. code-block:: bash

   cmake -S llvm -B build-tsan -G Ninja -DCMAKE_BUILD_TYPE=Release \
     -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
     -DLLVM_ENABLE_PROJECTS=clang -DLLVM_TARGETS_TO_BUILD=Native \
     -DLLVM_USE_SANITIZER=Thread
   ninja -C build-tsan cpp-verify
   .github/workflows/cppverify-sanitize.sh build-tsan thread 2

The last argument is how many programs run at once. Each runs with
``--jobs=4`` and a proof cache of its own, and a program whose tests use the
race backend runs on it when cvc5 is installed, so the thread pool, the cache,
and the races between solvers run concurrently. A program uses at most about
3 GB under ThreadSanitizer. In either mode a program that gives no result
within 900 s is reported too (``cppverify-sanitize: no result within 900 s``),
since a sanitizer runtime that hangs prints nothing. ``cppverify-tsan.supp`` suppresses the reports
inside Z3 4.13.4 itself and the calls LLVM's crash handler makes in a signal
handler, each with its reason. To look at one program, run it with the same
options:

.. code-block:: bash

   TSAN_OPTIONS=suppressions=.github/workflows/cppverify-tsan.supp \
     build-tsan/bin/cpp-verify --jobs=4 program.cpp --

ThreadSanitizer keeps each thread's calls on a shadow stack of 65536 frames
and does not check its end, so a deeper nesting overwrites the runtime's own
memory and the run crashes or hangs later, somewhere unrelated. The
counterexample checker nests that deep, so in a ThreadSanitizer build
``clang/lib/Verify/Backend/Certify.cpp`` is compiled with
``-fno-sanitize-thread-func-entry-exit``: its memory accesses are still
checked, but its frames do not appear in reported stacks. A TSan build of
``cpp-verify`` also counts each thread's nesting and stops at the limit with
exit status 1, naming the recursion. Built with the checker's hooks left in,
``suite/spec_automation.cpp`` stops so (paths shortened):

.. code-block:: text

   cpp-verify: ThreadSanitizer shadow stack full: 65472 nested calls
       #0 __sanitizer_print_stack_trace <null> (cpp-verify+0x42751f)
       #1 __wrap___tsan_func_entry clang/tools/cpp-verify/ShadowStackGuard.cpp:29:5 (cpp-verify+0x45efeb)
       #2 getSignificantBits llvm/include/llvm/ADT/APInt.h:1557:12 (cpp-verify+0xe34cac)
       #3 minimal clang/lib/Verify/Backend/Certify.cpp:20:41 (cpp-verify+0xe34cac)
       #4 clang::verify::CertInt::CertInt(llvm::APInt) clang/lib/Verify/Backend/Certify.cpp:23:45 (cpp-verify+0xe34cac)
       ...

A recursion reported so is compiled the same way, or made iterative.

New language features should have both semantic and structural oracles:

- real C++ positive and negative programs;
- exact Layer 1 VCR and Layer 2 passive-SSA expectations;
- Layer 3 Obligation IR checks for sorts, IDs, origins, and the decisive query,
  plus Layer 4 Z3 checks for its translation;
- ordinary solver checks for valid programs and deliberate false proofs.

Solver ``unknown`` never validates a feature. Structural lowering can still be
tested with ``--lower-only``, while proof acceptance remains blocked until a
backend returns a proof result.

Engine headers: :doc:`../api/index`.