Commands and flags
==================

Standalone verifier
-------------------

.. code-block:: bash

   cpp-verify --version
   cpp-verify file.cpp
   cpp-verify file.cpp -- -I include -DNDEBUG
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
   cpp-verify --jobs=4 --proof-cache=.cppverify-cache file.cpp
   cpp-verify --solver-rlimit=500000 --max-query-nodes=50000 file.cpp
   cpp-verify --diagnostics-format=json file.cpp
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
compiler error is. Like a compiler error it stops the file: no function of
the file gets a verdict (:doc:`limitations` lists what is not represented).

.. cppverify-example: rejects

.. code-block:: cpp

   int pick(int x)
     cv::post(cv::result >= 0)
   {
     switch (x) { case 1: return 1; default: return 0; }
   }

.. code-block:: text

   pick.cpp:4:3: error: pick: unsupported statement: SwitchStmt
       4 |   switch (x) { case 1: return 1; default: return 0; }
         |   ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An error about the function as a whole, such as a recursion without a
measure, points at its name. With ``--diagnostics-format=json`` the record
carries the range, here ``"source":{"column":3,"end_column":53,"end_line":4,
"file":"pick.cpp","line":4}``. Before 0.2 such an error named only the
function: ``error: pick: unsupported statement: SwitchStmt``.

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
(``lake``) it finds on ``PATH`` with their versions. cvc5 is tested with 1.1.2 and also
works with 1.4: a query that needs a constant array, as every one over sets, multisets,
and maps does, sets cvc5's ``arrays-exp`` option itself, which 1.4 requires. Every Lean
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

Lean export runs no solver, so every solver option is an error with
``--backend=lean``, ``--lean-out``, or ``--lean-project``, the same way as
``--timeout`` above: ``--timeout``, ``--collection-timeout``,
``--certify-timeout``, ``--function-timeout``, ``--solver-rlimit``,
``--max-query-nodes``, and ``--int-encoding``. ``--lean-fallback`` runs Z3
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
       semantics live in ``CppVerify/Generated.lean``; reusable lemmas and
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
       applies the bridge and introduces every name. Each
       goal means what its obligation means: every operator keeps its
       grouping under Lean's precedence, a numeral has its type (``Nat``
       would read ``2 - 3`` as 0), a Boolean is a proposition
       (``↔``), machine division by zero is SMT-LIB's
       (``BitVec.smtUDiv``, ``BitVec.smtSDiv``), as in the solvers, and
       ``decide`` evaluates the machine comparisons at constants
       (:doc:`../book/part-ii/ch17-backends-modular-calls`).
   * - ``--lean-certify``
     - Build the active project with the pinned Lean 4.35.0, each proof file on
       its own and without ``sorry``, then check the compiled modules with a
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
     - Reject a solver-backed canonical obligation module larger than ``N``
       expression nodes before verification, lower-only encoding, or a requested
       Z3 dump (default ``0``, disabled). Exhaustion is fail-closed with reason
       ``query.size-limit``.
       Not accepted with ``--backend=lean``, which runs no solver.
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
       ``0`` selects every core). Lean export remains serial.
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
   * - ``--diagnostics-format={text,json}``
     - Select Clang-style text (default) or versioned JSON Lines for verification
       results. JSON records use schema ``cppverify.diagnostic/1``.
   * - ``--lower-only``
     - Run Clang conversion, backend-specific preparation, passivization,
       canonical Obligation IR construction, spec-axiom encoding, and selected
       Z3/SMT-LIB translation without calling a solver. Supported for Z3, cvc5,
       portfolio, and BMC.
   * - ``--obligation-out=FILE``
     - Write deterministic, versioned backend-neutral modules with portable
       source attribution and SHA-256 semantic identities. Multiple modules are
       concatenated in one archive.
   * - ``--obligation-in=FILE``
     - Validate and replay an archive without reparsing C++. Supports Z3, cvc5,
       strict portfolio, ``--lower-only``/Layer 3-4 dumps, and Lean scratch
       export. Archives
       produced after BMC unrolling retain their bound and replay with BMC
       unwinding semantics; applying BMC to an untransformed archive is
       rejected because unrolling must run before obligation lowering.
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
are checked the same way.
Portfolio mode requires agreement; an agreed ``sat`` result uses Z3's typed
model and trace, while disagreement or incomplete secondary evidence is
``Unresolved``. BMC reports ``BoundedSafe: f [backend=bmc, bound=N]`` when only its unwinding
obligation fails at the maximum frontier, and reports ``Verified`` only when an
explored bound proves complete unwinding. Text diagnostics publish the terminal
``bound``, all attempted ``bounds``, and the count of successful ordered queries
reused across prefixes. JSON uses ``bound``, ``explored_bounds``, and
``reused_queries``. Lean generation reports ``Exported``. Only the pinned,
admission-free kernel workflow reports ``Certified``.

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

None of these limits applies to Lean, which runs no solver. Lean
certification (``--lean-certify``) gives each ``lake`` step 300 seconds:
building the generated module, compiling your module, compiling each proof,
and the final check. A step that takes longer leaves every result
``Unresolved`` with reason ``lean.export-failed``, and its message gives the
command's error.

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
same work each. Lean generation and certification stay serial. The compile-time
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

Failed Z3, cvc5, portfolio, and BMC results identify a source-anchored
obligation such as ``function-identity::overflow@line:column#2``. The kind says
what the obligation checks:

- contracts: ``assertion``, ``precondition``, ``postcondition``,
  ``invariant-entry``, ``invariant-preserved``, ``termination``,
  ``type-invariant``, and ``cppverify::recommends``;
- C++ definedness: ``overflow`` (including a mathematical value converted to
  a machine type it does not fit), ``division-by-zero``, ``shift``,
  ``bounds``, ``dereference``, ``initialization``, ``pointer-difference``,
  and ``deallocation``;
- generated interfaces: ``pointer-validity`` (a pointer parameter, result, or
  ``valid(p, n)`` extent must denote valid storage), ``aliasing`` (implicit
  non-aliasing), ``frame`` (writes and callee effects stay within
  ``cppverify::modifies``), and ``missing-return``;
- ``unwinding`` for a BMC bound, and ``unsupported`` for a construct the
  verifier rejects fail-closed.

The check that a function's contract is defined (see :doc:`functions-loops`)
is reported only when it fails, as ``contract of f``. Its obligations are
named ``function-identity::contract::kind@line:column`` with the definedness
kinds above, and JSON records give ``f`` as the function.

The local suffix only disambiguates obligations of one kind at the same anchor,
so inserting or reordering an unrelated obligation does not renumber later IDs
unless its source anchor moves. JSON records carry the kind as
``obligation.kind``. Diagnostics include inclusive source ranges and source
display names while retaining internal SSA names for unambiguous tooling.

Counterexample values carry exact sorts such as ``bool``, ``i32``, ``u32``,
``math-i32``, ``pointer``, and ``heap``. Z3 model completion is disabled:
undetermined values print as ``<unknown>`` and become JSON ``null``. Signed and
unsigned bit-vectors are decoded to source-level decimal values.

Counterexample traces may contain guarded branch, modular-call, loop,
heap-write, allocation/provenance, lifetime-end, deletion, and return events.
False guards are omitted; a guard the model does not determine is retained with
JSON ``"active": null`` rather than an invented path choice. Archives preserve
the same names, ranges, IDs, and trace data during replay.

Each non-success verification result also carries a stable reason code. Current
codes include ``counterexample``, ``solver.timeout``, ``solver.unknown``,
``solver.resource-limit``, ``solver.unavailable``,
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

``--diagnostics-format=json`` covers verification-result diagnostics.
Command-line validation and frontend parse errors may still use text. Combining
JSON diagnostics with IR dumps intentionally creates a mixed stream. Malformed
byte sequences in source or archive display text are rendered with the Unicode
replacement character, so every emitted JSON record remains valid UTF-8.

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

``--obligation-out`` writes ``cppverify.obligation/2`` records only after exact
serialize/deserialize/validate/reserialize checks. Stable wire tags make the
format independent of C++ enum ordinals. The reader rejects malformed magic,
unsupported versions, truncation, invalid tags, inconsistent feature
declarations, duplicate identities, and oversized/deep expressions.
Schema v2 adds the precise obligation kinds; schema v1 records, which name
only assertions, postconditions, and unwinding checks, are still read.
Records cap integer widths at 4096 bits, expression depth at 4096, and
collections plus expression nodes/edges at 100,000 per record. It also rejects
embedded NULs, non-canonical numerals, inactive payload fields, ill-scoped
variables, conflicting module-wide free-symbol sorts across semantic and
diagnostic expressions, and contradictory complete/ordered queries before
backend dispatch.

Module and per-obligation SHA-256 hashes omit source paths and display-only
names, source ranges, internal positional and public source-anchored IDs,
obligation kinds other than ``unwinding``, and traces, so moving unchanged
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
Clang reject the flag and the contract constructs. (Building cpp-verify itself from
source is independent and works with any standard host compiler.)

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
reports the constructs as errors; a stock ``clang-format`` keeps every clause on the
declarator's line. Tools built on this build's libclang see the contracts as well.

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