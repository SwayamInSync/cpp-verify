# CppVerify

**CppVerify** checks C++ against properties you write in the program itself — and reports whether those properties always hold, or shows you when they can fail.

Formal verification lets you treat correctness as an engineering artifact: you state what should be true, and the tool either proves it or gives you a precise reason it does not. CppVerify brings that discipline to everyday C++ without a separate language or annotation dialect.

📖 **[Documentation](https://swayaminsync.github.io/cpp-verify/)** — install guide, the book (Part I–II), language reference, and Doxygen API.

This repository is an [LLVM/Clang](https://github.com/llvm/llvm-project) fork (base `llvmorg-23.1.3`) with a verification engine in `clang/lib/Verify`, discharged by Z3, cvc5, or Lean.

## Install

**macOS**

```bash
brew install cmake ninja git
git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
cd cpp-verify
./setup.sh
```

**Linux**

```bash
sudo apt install cmake ninja-build build-essential git
git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
cd cpp-verify
./setup.sh
```

**Windows** — install [CMake](https://cmake.org/download/), [Ninja](https://github.com/ninja-build/ninja/releases), [Git](https://git-scm.com/download/win), [Python 3](https://www.python.org/downloads/windows/), and **Visual Studio Build Tools** (C++ workload). Run the commands from an x64 Developer PowerShell for VS 2022 (or an x64 Native Tools prompt), so that CMake finds the compiler; or pass `-Generator "Visual Studio 17 2022"` to `setup.ps1`.

```powershell
git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
cd cpp-verify
.\setup.ps1
```

Prebuilt archives for Linux x86_64 and macOS arm64 are attached to each [release](https://github.com/SwayamInSync/cpp-verify/releases).

Binaries: `build/bin/cpp-verify`, `build/bin/clang++`, `build/bin/clangd`, and `build/bin/clang-format` (on Windows, under `build\bin\`).

Z3 4.13.4 is built in: from the `third_party/z3` submodule, or, without it, cloned during the first build. See `third_party/README.md`. Two backends are optional and found on `PATH`:

- cvc5, for `--backend=cvc5`, `portfolio`, and `race` (tested with 1.1.2): `apt install cvc5` on Ubuntu 24.04, or a [cvc5 release](https://github.com/cvc5/cvc5/releases/tag/cvc5-1.1.2) for Linux, macOS, or Windows; `--cvc5-path` names another executable.
- Lean 4, for `--lean-certify` and `--lean-fallback`: install [elan](https://github.com/leanprover/elan); generated projects pin `leanprover/lean4:v4.32.2`.

`cpp-verify --version` shows the cpp-verify release, the LLVM release it is built on, and the Z3, cvc5, and Lean versions it uses.

### Manual build

```bash
cmake -S llvm -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra" \
  -DLLVM_TARGETS_TO_BUILD=Native \
  -DCPPVERIFY_VENDOR_Z3=ON \
  -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF
ninja -C build clang cpp-verify clangd clang-format
```

On macOS, also pass `-DCLANG_USE_XCSELECT=ON`, as `setup.sh` does, so that the built `clang++` finds the SDK without `SDKROOT`.

## Quick start

```cpp
int abs(int x)
  cppverify::pre(x >= -2147483647)   // every int except INT_MIN, whose negation overflows
  cppverify::post(cppverify::result >= 0)
{
  return x < 0 ? -x : x;
}
```

```bash
./build/bin/cpp-verify abs.cpp
./build/bin/clang++ -std=c++17 -fverify-contracts -c abs.cpp -o abs.o
```

Use `-fverify-contracts` on `clang++` so the constructs (`cppverify::pre`, `cppverify::post`, ...) are recognized; `cpp-verify` enables that flag automatically. Every construct is written qualified by the namespace `cppverify`, directly or through an alias such as `namespace cv = cppverify;`, so no word is reserved and C++26 `pre`/`post` stay the compiler's. `<cppverify.h>` needs no `#include`.

### Editors

`setup.sh` also builds `clangd` and `clang-format` from these sources. Point your editor's
clangd at `build/bin/clangd` and add `-fverify-contracts` to the compile flags: hover, go to
definition, find references, rename, and completion then work inside contracts, and
`clang-format` lays clauses out one per line. See the tooling page of the documentation.

### Supported compiler

Contract syntax (`cppverify::pre` / `cppverify::post` / `cppverify::invariant` / `cppverify::spec` / …) and the
`-fverify-contracts` flag exist **only in this repository's Clang**. To compile
or verify code that uses contracts, you must use the shipped tools:

- `./build/bin/cpp-verify file.cpp` — verify.
- `./build/bin/clang++ -fverify-contracts … file.cpp` — compile (also runs verification).

Stock GCC or upstream Clang will reject `-fverify-contracts` (unknown flag) **and**
the contract constructs (`use of undeclared identifier 'cppverify'` from Clang,
`expected initializer before 'cppverify'` from GCC). There is no contract support
outside the shipped Clang.

Note this is a separate matter from *building* cpp-verify itself from source:
that bootstrap step compiles ordinary C++ and works with **any** standard host
compiler — GCC or Clang (`setup.sh` uses `${CXX:-c++}`).

## Verification backends

| Backend | CLI | Role |
|---------|-----|------|
| **Z3** (default) | `cpp-verify file.cpp` | Weakest-precondition VCs + Z3 |
| **cvc5** | `cpp-verify --backend=cvc5 file.cpp` | Independent SMT-LIB2 solving |
| **Strict portfolio** | `cpp-verify --backend=portfolio file.cpp` | Matching Z3 + cvc5 verdicts only |
| **Race** | `cpp-verify --backend=race file.cpp` | Z3 and cvc5 at once; the first proof or certified counterexample stands |
| **BMC** | `cpp-verify --backend=bmc --unroll=N file.cpp` | Loop bounds 0 through `N`, solved with Z3; `BoundedSafe` when no failure exists within the bound |
| **Lean export** | `cpp-verify --backend=lean --lean-out=out.lean file.cpp` | Emit an unchecked `sorry` theorem; reports `Exported`, not `Verified` |
| **Lean project** | `cpp-verify --backend=lean --lean-project=dir file.cpp` | Generate an editable, pinned Lean 4 project from the obligations |
| **Lean fallback** | `cpp-verify --lean-fallback=dir file.cpp` | Route obligations Z3/portfolio left *unresolved* into a Lean project; once their proofs check, the function is `Proved (z3+lean)` |

Add `--lean-certify` to kernel-check every proof in a `--lean-project` tree with no
admissions, so a discharged obligation is machine-checked rather than assumed.

## Commands

| Command | Role |
|---------|------|
| `cpp-verify file.cpp` | Verify only (Z3) |
| `clang++ -fverify-contracts -c file.cpp` | Verify (parallel) + compile |
| `clang++ -fno-verify -c file.cpp` | Light check — contracts on (implied), skip the solver |
| `cpp-verify --no-check-ub file.cpp` | Verify without the default memory checks |

`-fverify-contracts` and `-fno-verify` are two axes: the first enables the contract language (and verifies by default); `-fno-verify` skips the solver and implies `-fverify-contracts`, so a lone `-fno-verify` is a fast syntax/semantics check. There is no `-fverify`.

### Undefined behavior

Proving `cppverify::post` is meaningless if the function can execute UB on the way there, so
safety obligations are generated by the tool, not written by you. **Core expression
definedness is always on**: signed overflow and negation, zero divisors, `INT_MIN / -1`,
invalid shifts, conversions to an enumeration outside its range, non-null dereference,
and definite initialization of locals — including operations inside lifted `constexpr`
functions. **Memory checking is on by default too**: every access and pointer step must
stay inside the object it addresses, a `valid(p, n)` extent declared in a precondition or
a single object. `--no-check-ub` turns memory checking off; core definedness stays on.

```bash
./build/bin/cpp-verify               file.cpp   # contracts, definedness, memory checks
./build/bin/cpp-verify --no-check-ub file.cpp   # without the memory checks
```

See [Chapter 18](https://swayaminsync.github.io/cpp-verify/book/part-ii/ch18-undefined-behavior.html)
and `docs/UB-CHECKING.md`.

### Solver control

```bash
./build/bin/cpp-verify --jobs=4 --proof-cache=.cppverify-cache file.cpp
./build/bin/cpp-verify --timeout=10000 --solver-rlimit=2000000 file.cpp
./build/bin/cpp-verify --int-encoding=bitvector file.cpp         # auto (default) | integer | bitvector
./build/bin/cpp-verify --diagnostics-format=json file.cpp        # JSON Lines, for editors/CI
./build/bin/cpp-verify --obligation-out=goals.cpv file.cpp       # backend-neutral archive
./build/bin/cpp-verify --dump-ir=1,2,3,4 file.cpp                # VCR, passive, Obligation IR, Z3
```

Z3 runs support deterministic isolated solving (`--jobs`) and positive-proof reuse
(`--proof-cache`). A query past `--timeout` or `--solver-rlimit` is reported as
*unresolved* rather than hanging — never as verified. `--int-encoding` only chooses
how machine integers reach the solver; every choice is exact, so it can change speed
but never a verdict. A failure names the function and the obligation that failed,
`<function identity>::<kind>@line:column`, e.g.
`verification failed: abs [fn_5f5a3361627369::overflow@5:3]`.

Chained modular calls (e.g. `return inc(inc(x))`) are lowered to temporaries automatically.
See [Chapter 17](https://swayaminsync.github.io/cpp-verify/book/part-ii/ch17-backends-modular-calls.html).

Contract syntax, flags, and limitations: **[language reference](https://swayaminsync.github.io/cpp-verify/language/index.html)**.

## Documentation

| Section | Link |
| -------- | ----- |
| The Book — Part I | [Foundations](https://swayaminsync.github.io/cpp-verify/book/part-i/index.html) |
| The Book — Part II | [Using CppVerify](https://swayaminsync.github.io/cpp-verify/book/part-ii/index.html) |
| Language reference | [Syntax & flags](https://swayaminsync.github.io/cpp-verify/language/index.html) |
| Case studies | [Verified real code](https://swayaminsync.github.io/cpp-verify/case-studies/index.html) |
| Release notes | [What each release supports](https://swayaminsync.github.io/cpp-verify/release-notes.html) |
| Verifier API | [Doxygen](https://swayaminsync.github.io/cpp-verify/doxygen/index.html) |

Build the site locally (it installs the Python requirements with `pip`, so run it in a virtual environment, `python3 -m venv .venv && . .venv/bin/activate`; it also needs Doxygen):

```bash
./website/scripts/build-docs.sh
# website/build/index.html  +  website/build/doxygen/
```

Design notes: `docs/DESIGN.md`, `docs/ARCHITECTURE.md`, `docs/UB-CHECKING.md` (index: `docs/README.md`).

## Tests

```bash
./scripts/run-verify-tests.sh              # fast executable-example sweep
./build/bin/llvm-lit -sv clang/test/Verify  # full lit suite (needs `ninja -C build FileCheck not count split-file llvm-config`)
```

Contributor coverage (instrument ``clangVerify`` only):

```bash
./scripts/coverage-sweep.sh       # after a normal build
./scripts/coverage-verify.sh      # full instrumented rebuild (slow)
```

## License

cpp-verify, like the LLVM project it is built on, is distributed under the [Apache License v2.0 with LLVM Exceptions](https://llvm.org/LICENSE.txt) (`LICENSE.TXT`). Z3, built into cpp-verify from `third_party/z3`, is under the MIT license (`third_party/z3/LICENSE.txt`).