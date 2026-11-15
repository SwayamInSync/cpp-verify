# Contributing to cpp-verify

cpp-verify is a deductive verifier for C++ built into a fork of LLVM's Clang.
The root `CONTRIBUTING.md` is LLVM's own and is kept as it is; this page is
cpp-verify's. Issues and pull requests go to
[SwayamInSync/cpp-verify](https://github.com/SwayamInSync/cpp-verify), not
to LLVM.

## Build

```bash
git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
cd cpp-verify
./setup.sh                          # setup.ps1 on Windows
```

`setup.sh` builds Clang, `cpp-verify`, and Z3 4.13.4 from `third_party/z3`
into `build/`. After a change, rebuild what it touches:

```bash
ninja -C build cpp-verify clang
```

`docs/REPO_LAYOUT.md` says where everything is; the verifier is
`clang/lib/Verify/`, the contract language `clang/lib/Parse/ParseCppVerify.cpp`
and `clang/lib/Headers/cppverify.h`.

## Test

```bash
ninja -C build FileCheck not count split-file llvm-config VerifyTests
./build/bin/llvm-lit -sv clang/test/Verify          # the verifier's tests
./build/tools/clang/unittests/Verify/VerifyTests     # its unit tests
```

The tests that use cvc5 run when `cvc5` is on `PATH` (1.1.2 to 1.4.2), and
those that use Lean when `lake` is (Lean 4.35.0, through elan).

## What a change needs

A verifier is trusted for what it says, so a change is accepted with the
evidence that what it says is right:

- **A test that fails without the change.** For a new feature, the cases it
  supports and a wrong twin of each that must be refuted; for a fix, the
  input that went wrong. Run the test on `main` and say how it fails there.
- **No proof that holds by accident.** A test that expects `Verified` should
  also check that the proof is not vacuous (`CHECK-NOT: vacuous`), and a
  claim that is false must fail with a certified counterexample, never pass.
- **Mutants, for a change to the verifier's logic.** Break each part of the
  change on purpose (drop a check, flip a condition) and show that a test
  fails for each; list them in the pull request.
- **Documentation with real output.** A change users see updates the
  reference (`website/source/language/`), the book where it teaches the
  feature, and the release notes, with examples and the verifier's exact
  output. `docs/ARCHITECTURE.md` describes how it works.
- **The whole suite.** CI runs it on Linux (release and assertions builds),
  macOS, and Windows; locally, run at least the tests near the change.

## Report a problem

Use an issue form: a bug (a crash, a wrong message), a wrong verdict, or a
construct the verifier does not support. A wrong verdict, a `Verified` for a
claim that is false, is the most serious bug a verifier can have; see
[SECURITY.md](SECURITY.md).
