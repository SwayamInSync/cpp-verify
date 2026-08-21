# CppVerify

**CppVerify** checks C++ against properties you write in the program itself — and reports whether those properties always hold, or shows you when they can fail.

Formal verification lets you treat correctness as an engineering artifact: you state what should be true, and the tool either proves it or gives you a precise reason it does not. CppVerify brings that discipline to everyday C++ without a separate language or annotation dialect.

📖 **[Documentation](https://swayaminsync.github.io/cpp-verify/)** — install guide, the book (Part I–II), language reference, and Doxygen API.

This repository is an [LLVM/Clang](https://github.com/llvm/llvm-project) fork (base `llvmorg-22.1.3`) with a verification engine in `clang/lib/Verify`, discharged by Z3, cvc5, or Lean.

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

**Windows** — install [CMake](https://cmake.org/download/), [Ninja](https://github.com/ninja-build/ninja/releases), [Git](https://git-scm.com/download/win), and **Visual Studio Build Tools** (C++ workload).

```powershell
git clone --recurse-submodules https://github.com/SwayamInSync/cpp-verify.git
cd cpp-verify
.\setup.ps1
```

Binaries: `build/bin/cpp-verify` and `build/bin/clang++` (on Windows, under `build\bin\`).

Z3 is vendored by default (`third_party/z3` submodule, or CMake FetchContent on first configure). See `third_party/README.md`. cvc5 is optional and is not vendored; install it (`apt install cvc5` or `brew install cvc5`) for `--backend=cvc5` and `--backend=portfolio`, or pass `--cvc5-path`.

### Manual build

```bash
cmake -S llvm -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_PROJECTS=clang \
  -DLLVM_TARGETS_TO_BUILD=Native \
  -DCPPVERIFY_VENDOR_Z3=ON \
  -DCPPVERIFY_PREFER_SYSTEM_Z3=OFF
ninja -C build clang cpp-verify
```

## Quick start

```cpp
int abs(int x)
  pre(x >= -2147483647)   // every int except INT_MIN, whose negation overflows
  post(result >= 0)
{
  return x < 0 ? -x : x;
}
```

```bash
./build/bin/cpp-verify abs.cpp
./build/bin/clang++ -std=c++17 -fverify-contracts -c abs.cpp -o abs.o
```

Use `-fverify-contracts` on `clang++` so `pre` / `post` are keywords. `cpp-verify` enables that flag automatically.

### Supported compiler

Contract syntax (`pre` / `post` / `invariant` / `spec` / …) and the
`-fverify-contracts` flag exist **only in this repository's Clang**. To compile
or verify code that uses contracts, you must use the shipped tools:

- `./build/bin/cpp-verify file.cpp` — verify.
- `./build/bin/clang++ -fverify-contracts … file.cpp` — compile (also runs verification).

Stock GCC or upstream Clang will reject `-fverify-contracts` (unknown flag) **and**
the contract keywords (`expected function body after function declarator` at
`pre(...)`). There is no contract support outside the shipped Clang.

Note this is a separate matter from *building* cpp-verify itself from source:
that bootstrap step compiles ordinary C++ and works with **any** standard host
compiler — GCC or Clang (`setup.sh` uses `${CXX:-c++}`).

## Verification backends

| Backend | CLI | Role |
|---------|-----|------|
| **Z3** (default) | `cpp-verify file.cpp` | Weakest-precondition VCs + Z3 |
| **cvc5** | `cpp-verify --backend=cvc5 file.cpp` | Independent SMT-LIB2 solving |
| **Strict portfolio** | `cpp-verify --backend=portfolio file.cpp` | Matching Z3 + cvc5 verdicts only |
| **BMC** | `cpp-verify --backend=bmc --unroll=N file.cpp` | Incremental bounds through `N`, then Z3 |
| **Lean export** | `cpp-verify --backend=lean --lean-out=out.lean file.cpp` | Emit an unchecked `sorry` theorem; reports `Exported`, not `Verified` |
| **Lean project** | `cpp-verify --lean-project=dir file.cpp` | Generate an editable, pinned Lean 4 project from the obligations |
| **Lean fallback** | `cpp-verify --lean-fallback=dir file.cpp` | Route obligations Z3/portfolio left *unresolved* into a Lean project |

Add `--lean-certify` to kernel-check every proof in a `--lean-project` tree with no
admissions, so a discharged obligation is machine-checked rather than assumed.

## Commands

| Command | Role |
|---------|------|
| `cpp-verify file.cpp` | Verify only (Z3) |
| `clang++ -fverify-contracts -c file.cpp` | Verify (parallel) + compile |
| `clang++ -fno-verify -c file.cpp` | Light check — contracts on (implied), skip the solver |
| `cpp-verify --check-ub file.cpp` | Also check declared buffer extents (`valid(p, n)`) |

`-fverify-contracts` and `-fno-verify` are two axes: the first enables the contract language (and verifies by default); `-fno-verify` skips the solver and implies `-fverify-contracts`, so a lone `-fno-verify` is a fast syntax/semantics check. There is no `-fverify`.

### Undefined behavior

Proving `post` is meaningless if the function can execute UB on the way there, so
safety obligations are generated by the tool, not written by you. **Core expression
definedness is always on**: signed overflow and negation, zero divisors, `INT_MIN / -1`,
invalid shifts, non-null dereference, and definite initialization of local scalars —
including operations inside lifted `constexpr` functions. `--check-ub` *additionally*
enables declared buffer-extent checks driven by `valid(p, n)`.

```bash
./build/bin/cpp-verify            file.cpp   # contracts + always-on definedness
./build/bin/cpp-verify --check-ub file.cpp   # additionally use valid(p, n) extents
```

See [Chapter 18](https://swayaminsync.github.io/cpp-verify/book/part-ii/ch18-undefined-behavior.html)
and `docs/UB-CHECKING.md`.

### Solver control

```bash
./build/bin/cpp-verify --jobs=4 --proof-cache=.cppverify-cache file.cpp
./build/bin/cpp-verify --timeout=10000 --solver-rlimit=2000000 file.cpp
./build/bin/cpp-verify --diagnostics-format=json file.cpp        # JSON Lines, for editors/CI
./build/bin/cpp-verify --obligation-out=goals.bin file.cpp       # backend-neutral archive
./build/bin/cpp-verify --dump-ir=1,2,3,4 file.cpp                # VCR, passive, Obligation IR, Z3
```

Z3 runs support deterministic isolated solving (`--jobs`) and positive-proof reuse
(`--proof-cache`). A query past `--timeout` or `--solver-rlimit` is reported as
*unresolved* rather than hanging — never as verified.

Chained modular calls (e.g. `return inc(inc(x))`) are lowered to temporaries automatically.
See [Chapter 17](https://swayaminsync.github.io/cpp-verify/book/part-ii/ch17-backends-modular-calls.html).

Contract syntax, flags, and limitations: **[language reference](https://swayaminsync.github.io/cpp-verify/language/index.html)**.

## Case study

The flagship evaluation verifies the unpadded 64-bit **ULEB128** buffer codec derived
from LLVM 22.1.3's `llvm/Support/LEB128.h` — termination, exact encoded length 1–10,
every continuation and terminator bit, in-bounds writes, an exact ten-cell frame, and
`decode(encode(value)) == value` for every `uint64_t`. See
[LLVM ULEB128](https://swayaminsync.github.io/cpp-verify/case-studies/llvm-uleb128.html),
which also states the extraction boundary (where the artifact differs from upstream and why).

A second study proves a **UTF-8 decoder cannot be tricked**: every accepted result
is a Unicode scalar value, never a surrogate, never an overlong encoding. Injecting
the historical defects gets them rejected with concrete witnesses — lead byte `C0`
yields `result = 64` (`@` smuggled as two bytes, the IIS / CVE-2008-2938 traversal
class), and dropping the `ED` ceiling yields `result = 55296`, exactly U+D800. See
[UTF-8 validation](https://swayaminsync.github.io/cpp-verify/case-studies/utf8-validation.html).

A third takes the **binary-search midpoint** — the `(lo + hi) / 2` overflow
that stood in *Programming Pearls* for two decades and in `java.util.Arrays` for
nine years. No contract asks for an overflow check; always-on definedness rejects it
on its own with the concrete `lo = 1073741825, hi = 1073741826` that breaks it, and
verifies the `lo + (hi - lo) / 2` form. See
[Binary search](https://swayaminsync.github.io/cpp-verify/case-studies/binary-search.html).

## Documentation

| Section | Link |
| -------- | ----- |
| The Book — Part I | [Foundations](https://swayaminsync.github.io/cpp-verify/book/part-i/index.html) |
| The Book — Part II | [Using CppVerify](https://swayaminsync.github.io/cpp-verify/book/part-ii/index.html) |
| Language reference | [Syntax & flags](https://swayaminsync.github.io/cpp-verify/language/index.html) |
| Case studies | [LLVM ULEB128](https://swayaminsync.github.io/cpp-verify/case-studies/llvm-uleb128.html) · [UTF-8 validation](https://swayaminsync.github.io/cpp-verify/case-studies/utf8-validation.html) · [Binary search](https://swayaminsync.github.io/cpp-verify/case-studies/binary-search.html) |
| Verifier API | [Doxygen](https://swayaminsync.github.io/cpp-verify/doxygen/index.html) |

Build the site locally:

```bash
./website/scripts/build-docs.sh
# website/build/index.html  +  website/build/doxygen/
```

Design notes: `docs/DESIGN.md`, `docs/ARCHITECTURE.md`, `docs/UB-CHECKING.md` (index: `docs/README.md`).

## Tests

```bash
./scripts/run-verify-tests.sh              # fast executable-example sweep
./build/bin/llvm-lit -sv clang/test/Verify  # full lit suite (needs `ninja -C build FileCheck not`)
```

Contributor coverage (instrument ``clangVerify`` only):

```bash
./scripts/coverage-sweep.sh       # after a normal build
./scripts/coverage-verify.sh      # full instrumented rebuild (slow)
```

## License

LLVM components use the [LLVM License](https://llvm.org/LICENSE.txt). See file headers in the tree.