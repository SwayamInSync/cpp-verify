Release notes
=============

cpp-verify follows `Semantic Versioning <https://semver.org>`_. While the major
version is 0, a minor release (0.2.0) may change the contract language or the
meaning of a verdict, always with a migration path; a patch release (0.1.1)
fixes bugs and soundness issues without changing the language, and may move to
a newer point release of the same LLVM major. Moving to a new LLVM major
release changes what C++ the compiler accepts, so it takes a minor release.
``cpp-verify --version`` reports the release, the LLVM release it is built on,
and the backend versions. A build from ``main`` between releases reports the
next release with ``-dev``.

The data formats keep versions of their own, listed with each release.

0.2.0 (in development)
----------------------

The changes on ``main`` since 0.1.1, which 0.2.0 will ship. Each entry says
what 0.1.1 did and what happens now; the page it links shows an example with
the verifier's output.

Wrong results fixed
~~~~~~~~~~~~~~~~~~~

These made 0.1.1 report ``Verified`` for a claim that is false, or compile a
program that cannot work.

**A clause takes one expression.** ``cv::post(cv::result >= 0 cv::result <= 10)``,
with its ``&&`` missing, kept the first condition and dropped the rest without
a word, so the clause checked less than it said. Anything after a clause's
expression is now an error (:doc:`language/syntax`).

**Recursion through** ``cppverify::choose``. A call inside a choose's body was not
seen as a call of the function the choose is in, so a spec that applied
itself there skipped its termination check, and its contradictory definition
let a false claim verify. The call is now checked like any other recursive
call (:doc:`book/part-ii/ch13-spec-and-proof-functions`).

**Archive replay reports proved obligations, not** ``Verified``. Replay printed
``Verified`` for every module whose obligations held, although a source
verdict also rests on facts an archive does not carry, such as a callee's
contract. It now prints ``Proved obligations: f (dependencies not checked in
replay)``, JSON status ``proved-obligations`` (:doc:`language/tooling`).

**A spec reads exact values.** A value a spec body read through a pointer kept
its machine type, so ``p[0] + p[1]`` wrapped: a proof that the sum of
``2147483647`` and ``1`` is negative verified. Such reads are now mathematical
integers, as the rest of a spec is (:doc:`language/ghost-proofs`).

**Quantifiers in executable code are errors.** ``cv::forall`` and ``cv::exists``
outside contracts and ghost code compiled to an undefined value while the
verifier read them as quantifiers. They are now an error, as ``cv::choose``
already was (:doc:`language/expressions`).

**Spec functions in generic lambdas are errors.** A spec function called in a
generic lambda compiled, and the program failed to link. It is now reported
where it is written (:doc:`language/ghost-proofs`).

**Extent markers outside a precondition are errors.** ``valid(p, n)`` declares
an extent only as a top-level condition of a precondition. Anywhere else it
meant ``true``, so ``cv::post(valid(cv::result, 4))`` verified for a function
that returns ``nullptr``. In a postcondition, a loop invariant, a
``cppverify::check``, ghost code, or a spec function it is now an error for
that function (:doc:`language/pointers`).

**Clang's own analyses.** ``noexcept`` of a contract expression crashed or hung
the compiler, as did a contract expression in a C++98 constant; the static
analyzer reported nothing after a ghost block; libclang hid the constructs;
and a contract expression in a template's signature produced a malformed
symbol. Each now behaves by the construct's meaning (:doc:`language/tooling`).

**Lean goals keep their grouping.** The Lean export placed parentheses by a
precedence table of its own, not Lean's, so ``(a ^ b) + 1`` became
``a_0 ^^^ b_0 + 1``, which Lean reads as ``a ^^^ (b + 1)``. With
``r = (a ^ b) + 1`` and ``s = a ^ (b + 1)``, a Lean proof certified the false
``cppverify::check(r == s)``. A term of numerals alone was read in Lean's
``Nat``, so a proof certified ``cppverify::check(2 - 3 == 0)`` too, ``2 - 3``
being 0 there. Machine division by zero meant Lean's 0, not the value the
solvers and the counterexample checker give. Every operator now keeps its
grouping under Lean's precedence, every numeral has its type
(``(3 : Int)``), and division by zero is SMT-LIB's (``BitVec.smtUDiv``,
``BitVec.smtSDiv``)
(:doc:`book/part-ii/ch17-backends-modular-calls`).

Failures that were not real
~~~~~~~~~~~~~~~~~~~~~~~~~~~

These made 0.1.1 report a failure, or reject a function, for C++ that is
correct.

**Loops that never repeat.** A loop whose condition is the constant false, as in
``do { ... } while (0)`` macros, forgot the state it changed, and the code
after it could fail for values it never produces. Its state now carries over
(:doc:`language/functions-loops`).

**Null minus null.** The difference of two null pointers failed its
``pointer-difference`` check; it is 0, as C++ defines (:doc:`language/pointers`).

**C++20 shifts.** A signed left shift followed the C++17 rule in every mode, so
``-1 << 1`` failed under ``-std=c++20``. From C++20 it is the value C++20
defines (:doc:`language/integers`).

**Enumeration ranges.** A value of an enumeration without a fixed underlying
type could take values outside its range, so true claims failed with values
such as ``c = 4294967295``. Every such value is now assumed to be in the
range C++ gives it (:doc:`language/integers`).

**Values read through** ``new`` **pointers.** ``*p + 1`` on a pointer from ``new``
was rejected as arithmetic on the pointer; values read through such a
pointer are now ordinary integers (:doc:`language/dynamic-storage`).

**Out-parameters.** Passing storage that is not initialized yet to a function
that writes it (``int a; init(a);``) was a failure, or stopped the file; it is
now ``Unresolved`` with reason ``construct.unsupported``, until a contract can
say that a function writes its parameter first (:doc:`language/pointers`).

**Choices in counterexamples.** A counterexample could use a value of
``cv::choose`` that its body excludes, so true claims about a choice failed.
Every choice a counterexample uses is now checked against its body
(:doc:`book/part-ii/ch13-spec-and-proof-functions`).

**Reads clauses over a choice.** A spec whose body applies ``cv::choose`` to
memory failed its ``cppverify::reads`` check (``calls choose, which reads the
heap without a reads clause``), although its frame held every cell the choice
reads. The check now follows the loads of the choice's body, and the facts a
spec's checks assume, its induction hypothesis included, reach the
applications inside a choice too (:doc:`language/ghost-proofs`).

**Vacuity findings of downgraded results.** A result that is ``Unresolved``
because a fact it relies on is not established could still be marked
``[vacuous]``, from that very fact, and whether it was depended on the
solver's search. Such findings are now dropped
(:doc:`book/part-ii/ch16-when-verification-fails`).

**Slices passed through a copy.** A function that requires ``valid(p, n)``
accepted an argument only when it was written as a parameter plus an offset,
as in ``first(a + 1, 3)``. Other arguments failed with a counterexample, even
when the program was correct:

- a copy of such a pointer (``const int *q = a + 1; first(q, 3);``);
- a choice between pointers (``c ? a + 1 : b``);
- a pointer stepped in a loop;
- a result whose contract says where it points.

Such an argument is now accepted when its elements lie in one of the caller's
objects (:doc:`language/pointers`).

**Callee frames inside the caller's.** A call could fail its ``frame`` check
although the callee writes only cells the caller may write, in two cases:

- a callee that writes its one object (``modifies(*p)``) passed a cell the
  caller may write, as in ``set(a + 2, 5)`` under ``modifies(a[2])``;
- a pointer copied into an object the caller may write, as in
  ``int *q = a + 2; set(q, 5);`` under ``modifies(*a)``.

The callee's footprint is now compared with the caller's frame cell by cell
(:doc:`language/pointers`).

**Lean goals that could not be proved.** In a Lean goal a quantifier took
everything after it into its body, which made a goal with a quantified fact
before its conclusion say more than its obligation: the goal of a call that
must establish ``cv::pre(cv::forall(k, 0, n, k >= 0) && n < 8)`` had no
proof. A signed right shift of a signed right shift lost its parentheses, and
a spec applied under a quantifier, as in
``cv::forall(k, 0, n, total(k) >= 0)``, had its definition stated with ``k``
outside the quantifier: neither project built. ``decide`` could not evaluate
a machine comparison such as ``cppBvSlt``. Quantifiers are now closed before
what follows them, every operator keeps its grouping, a definition under a
quantifier is stated for every value of its variable, and ``decide``
evaluates the machine comparisons at constants
(:doc:`book/part-ii/ch17-backends-modular-calls`).

C++ that compiles now
~~~~~~~~~~~~~~~~~~~~~

**Contracts in templates.** A template whose contract depends on its
parameters did not compile. Its contracts now compile and instantiate, and
are ignored with a ``-Wcontract-unsupported`` warning; a template without
contracts no longer stops the file (:doc:`language/functions-loops`).

**Apple's assertion macros.** On Apple targets ``<AssertMacros.h>`` defines a
``check(assertion)`` macro, which turned every ``cppverify::check(...)`` after
it into ``error: expected unqualified-id``. ``-fverify-contracts`` now defines
``__ASSERT_MACROS_DEFINE_VERSIONS_WITHOUT_UNDERSCORES`` to ``0`` on Apple
targets unless the command line defines it, so the header defines only its
``__Check``, ``__Require``, and ``__Verify`` names (:doc:`language/syntax`).

**Records through pointers.** Through a pointer, 0.1.1 reached only a record's
direct fields (``p->x``). A nested field (``p->inner.y``), a field of an
element (``p[k].x``), and an element of an array member (``r->buf[i]``) were
errors, so a ring buffer, a fixed-capacity stack, or any record that holds its
storage inline could not be verified. Each of them is now a heap cell, at any
depth: code can read and write it, contracts and ``cppverify::modifies`` can
name it, and a reference can bind to it. Each index is checked against its own
array, so ``r->buf[8]``, which has the address of the next field, is still an
error (:doc:`language/structs`).

Running cpp-verify
~~~~~~~~~~~~~~~~~~

**Ctrl-C stops the run.** Ctrl-C printed an LLVM crash report and the run went
on, or crashed. It now stops every solver at once, reports each unfinished
function as ``Interrupted``, and exits with status 130
(:doc:`language/tooling`).

**Options select their backend, and unused options are errors.**
``--lean-out`` and ``--lean-project`` select Lean and ``--unroll`` selects BMC;
an option the run would not use, such as ``--unroll`` with ``--backend=z3``, or
``--timeout`` and the other solver budgets with Lean export, which runs no
solver, is an error that names what it needs, where it was ignored
(:doc:`language/tooling`).

**Compiler errors stop their file, and headers are C++.** An error in a command
line was printed and then ignored, and a ``.h`` input was compiled as C. Now
the file with the error is not verified and ``cpp-verify`` exits with status 1,
and a header is C++ (:doc:`language/tooling`).

**Long expressions.** An expression with hundreds of operations used memory
with the cube of its depth, and one with thousands crashed. The cost is now
quadratic (a 250-term sum lowers in about 5 s instead of 120 s), and an
expression nested more than 256 operations deep is reported where it is
(:doc:`language/limitations`).

**Errors point at the code.** An error about a construct the verifier does not
represent named only the function, as in ``error: pick: unsupported statement:
SwitchStmt``. It now gives the file, line, and column, and shows the line with
a caret under the construct, as a compiler error does; its JSON record carries
the range (:doc:`language/tooling`).

**Z3 errors.** A Z3 call that failed went unnoticed, and a later step could
report something unrelated. The query now ends ``Unresolved`` with reason
``encoding.failed`` and Z3's message (:doc:`language/tooling`).

**Parallel runs.** With more than one job, a function waiting for its own
queries could run another function's long query, delaying its result and
spending its ``--function-timeout``. A waiting function now runs only its own
queries (:doc:`language/tooling`).

**cvc5 1.4.** Every query over sets, multisets, and maps failed with cvc5 1.4,
which requires extended arrays for constant arrays; such a query now enables
them itself (:doc:`language/tooling`).

**clang-format.** A range footprint is written ``p[lo : n]``, not ``p [lo:n]``
(:doc:`language/tooling`).

Data formats
~~~~~~~~~~~~

Archives stay ``cppverify.obligation/2`` and JSON diagnostics
``cppverify.diagnostic/1``. JSON records may carry the status
``proved-obligations`` (archive replay) and the reason ``interrupted``
(Ctrl-C).

0.1.1
-----

A patch release of 0.1.0, on the same LLVM 23.1.3, with the same language and
data formats. Each fix changes how the verifier searches, or which entries the
proof cache keeps; none changes what a verdict means.

**Fixed: certified failures reported at once.** A false claim could take the
full query timeout, or end ``Unresolved`` with ``solver.timeout`` under load,
although the verifier had already found a certified counterexample for it.
Once a function's complete query is refuted, the individual obligations only
choose which failure is reported, the first in source order; they now get no
more time than the complete query had, and the complete query's
counterexample stands when they do not finish.

**Fixed: small counterexamples after a large one.** When the solver first
proposed a counterexample whose spec values are too large to compute
(``fibo`` at a billion, say), checking it used up the time of the search for a
small counterexample that follows, so a false claim could end ``Unresolved``
with ``spec.fuel`` on a loaded machine. The check's time is now its own. Such
a check still takes up to ``--certify-timeout``, so under heavy load the
result can still be ``spec.fuel``.

**Fixed: results that depended on earlier queries.** The Z3 backend solved
complete queries in one long-lived solver context, which with one job
(``--jobs=1``, as in the test suite) every function of a file shared. Z3 keeps
the state of the queries solved in a context, as far as an interrupted one
got, and that state steers its next search. On a loaded machine a false
claim could therefore end ``Unresolved`` with ``solver.timeout``, a file's
counterexamples could change from run to run, and after one function needed
an induction, every later query of the file only sought a proof. Every query
is now solved in a context of its own. A proof that fitted its time only in
an earlier query's context may now need a larger ``--timeout``.

**Fixed: counterexamples that only fast machines found.** When a model needs
spec values beyond the solver's unfoldings, the verifier tries the least and
greatest values the query allows for their arguments. It tried one end after
the other, and each end restarted from small steps after every overshoot, so
on slow cores the first end could use the whole of this probe's short budget,
and a false claim whose counterexample lay at the other end ended
``Unresolved`` with ``spec.fuel``. The ends now take turns, and each takes at
most about two checks per bit of its argument. This makes such results rarer,
not impossible: the probe keeps a short budget, so that it cannot hold up a
proof, and on a heavily loaded machine (the test suite on a 3-core macOS
runner) it can still run out.

**Fixed: proof cache pruning.** With ``--proof-cache`` and a limit small
enough to evict entries (``--proof-cache-max-entries``,
``--proof-cache-max-mb``), the cache was pruned after each function, which
could remove entries that functions verified at the same time had not looked
up yet. Whether such a function reported a corrupt entry (``cache.corrupt``)
or proved its obligations again then depended on scheduling. The cache is now
pruned once, after the run's last lookup, and a failure to prune is a warning
instead of ``cache-error`` telemetry on a result.

The solver's search depends on its search order, which differs between
platforms, so these showed more often on macOS arm64 (the known issue of
0.1.0). Time budgets are still wall-clock: a claim whose proof or
counterexample needs more time than its budget can end ``Unresolved`` on a
slow or loaded machine, and a larger ``--timeout`` gives it more.

0.1.0
-----

The first public release of cpp-verify: a Clang-based deductive verifier for a
documented subset of C++, with first-class contracts that Clang parses and
type-checks.

**Built on** LLVM 23.1.3. Z3 4.13.4 is built in. cvc5 (tested with 1.1.2) and
Lean 4.32.2 are optional and found on ``PATH``.

**Install.** Archives for Linux x86_64 and macOS arm64 are attached to the
release on GitHub; each holds ``cpp-verify``, ``clang``/``clang++``,
``clangd``, ``clang-format``, and Clang's headers. The macOS binaries are not
notarized; if macOS refuses to open one downloaded with a browser, run
``xattr -dr com.apple.quarantine`` on the unpacked directory. On other systems,
including Windows, build from source with ``setup.sh`` or ``setup.ps1``
(:doc:`index`).

**Language.** Every construct is written qualified, ``cppverify::pre(...)``,
or through an alias, ``cv::pre(...)``. ``-fverify-contracts`` includes
``<cppverify.h>`` implicitly and reserves no word, so every standard header
compiles. Sources in the earlier keyword syntax convert with
``clang/tools/cpp-verify/cppverify-migrate.py`` (:doc:`language/tooling`).

**Verification.** Function and loop contracts, spec and proof functions,
ghost code, quantifiers, ``cppverify::choose``, triggers, mathematical
collections, behaviors, inductive predicates, and automatic induction, over
integers, flat records, abstract buffers, scalar references, and constrained
pointer lifetimes. Backends: Z3 (default), cvc5, a strict Z3 and cvc5
portfolio, a race of both, bounded model checking, and Lean export and kernel
certification. On the solver backends ``Verified`` is a proof, a failure
(``error: verification failed``) is a counterexample checked against the true
definitions, and anything else is ``Unresolved`` with a reason. BMC reports
``BoundedSafe`` when no failure exists within its bound, Lean export
``Exported``, Lean certification ``Certified`` or ``Proved (z3+lean)``, and a
``[[cppverify::trusted]]`` contract ``Trusted``.

**Editors.** clangd from this release gives hover, go to definition, find
references, rename, and completion inside contracts, and clang-format lays
clauses out one per line (:doc:`language/tooling`).

**License.** cpp-verify, like LLVM, is distributed under the Apache License
v2.0 with LLVM Exceptions. Each archive includes ``LICENSE.TXT`` and, for the
built-in Z3, ``LICENSE-Z3.txt`` (MIT).

**Data formats.** Obligation archives ``cppverify.obligation/2`` (reads
``/1``), JSON diagnostics ``cppverify.diagnostic/1``, and semantic hash format
v4.

**Not yet verified.** Member functions, templates, floating point,
exceptions, lambdas, virtual dispatch, ``switch`` and range-``for``, and the
standard library's containers. Contracts on member functions are ignored with
a warning (``-Wcontract-unsupported``). A contracted function that uses one of
the others fails closed: the run stops with an error naming the construct and
reports no verdicts for the file. Contracts are not saved in precompiled
headers.
The full boundary is in :doc:`language/limitations`.

**Known issue.** The solver's time budgets are wall-clock, and Z3 does not
always search the same way on every platform. On macOS arm64, a false claim
that is hard for the solver is sometimes reported ``Unresolved`` (reason
``solver.timeout`` or ``spec.fuel``) where Linux reports its counterexample
within the same budget. Such a result is never a wrong verdict, and a larger
``--timeout`` gives the solver more time to settle it. 0.1.1 removes four
causes of such results; a claim that needs more time than its budget can still
end this way on a slow or loaded machine.
