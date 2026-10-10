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

0.1.1
-----

A patch release of 0.1.0, on the same LLVM 23.1.3, with the same language and
data formats. Each fix below changes how long the verifier searches, or which
entries the proof cache keeps; none changes what a verdict means.

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

**Fixed: proof cache pruning.** With ``--proof-cache`` and a limit small
enough to evict entries (``--proof-cache-max-entries``,
``--proof-cache-max-mb``), the cache was pruned after each function, which
could remove entries that functions verified at the same time had not looked
up yet. Whether such a function reported a corrupt entry (``cache.corrupt``)
or proved its obligations again then depended on scheduling. The cache is now
pruned once, after the run's last lookup, and a failure to prune is a warning
instead of ``cache-error`` telemetry on a result.

The solver's search for a counterexample depends on its search order, so the
first two showed on some programs on Linux and more often on macOS arm64 (the
known issue of 0.1.0).

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
``--timeout`` gives the solver more time to settle it. 0.1.1 fixes the cause
of the ``solver.timeout`` results seen in testing and makes the ``spec.fuel``
ones rarer.
