# CppVerify

**CppVerify** checks C++ against properties you write in the program itself — and reports whether those properties always hold, or shows you when they can fail.

Formal verification lets you treat correctness as an engineering artifact: you state what should be true, and the tool either proves it or gives you a precise reason it does not. CppVerify brings that discipline to everyday C++ without a separate language or annotation dialect.

📖 **[Documentation](https://swayaminsync.github.io/cpp-verify/)** — install guide, the book (Part I–II), language reference, and Doxygen API.

This repository is an [LLVM/Clang](https://github.com/llvm/llvm-project) fork (base `llvmorg-22.1.3`) with a verification engine in `clang/lib/Verify`, discharged by Z3.

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

Z3 is vendored by default (`third_party/z3` submodule, or CMake FetchContent on first configure). See `third_party/README.md`.

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
| **BMC** | `cpp-verify --backend=bmc --unroll=N file.cpp` | Bounded loop unrolling, then Z3 |
| **Lean export** | `cpp-verify --backend=lean --lean-out=out.lean file.cpp` | Emit an unchecked `sorry` theorem; reports `Exported`, not `Verified` |

## Commands

| Command | Role |
|---------|------|
| `cpp-verify file.cpp` | Verify only (Z3) |
| `clang++ -fverify-contracts -c file.cpp` | Verify (parallel) + compile |
| `clang++ -fno-verify -c file.cpp` | Light check — contracts on (implied), skip the solver |

`-fverify-contracts` and `-fno-verify` are two axes: the first enables the contract language (and verifies by default); `-fno-verify` skips the solver and implies `-fverify-contracts`, so a lone `-fno-verify` is a fast syntax/semantics check. There is no `-fverify`.

```bash
./build/bin/cpp-verify --dump-ir=1,2,3,4 file.cpp   # VCR, passive, Obligation IR, Z3
```

Chained modular calls (e.g. `return inc(inc(x))`) are lowered to temporaries automatically.
See [Chapter 17](https://swayaminsync.github.io/cpp-verify/book/part-ii/ch17-backends-modular-calls.html).

Contract syntax, flags, and limitations: **[language reference](https://swayaminsync.github.io/cpp-verify/language/index.html)**.

## Documentation

| Section | Link |
| -------- | ----- |
| The Book — Part I | [Foundations](https://swayaminsync.github.io/cpp-verify/book/part-i/index.html) |
| The Book — Part II | [Using CppVerify](https://swayaminsync.github.io/cpp-verify/book/part-ii/index.html) |
| Language reference | [Syntax & flags](https://swayaminsync.github.io/cpp-verify/language/index.html) |
| Verifier API | [Doxygen](https://swayaminsync.github.io/cpp-verify/doxygen/index.html) |

Build the site locally:

```bash
./website/scripts/build-docs.sh
# website/build/index.html  +  website/build/doxygen/
```

Design notes: `docs/DESIGN.md`, `docs/ARCHITECTURE.md`.

## Tests

```bash
./scripts/run-verify-tests.sh
./build/bin/llvm-lit clang/test/Verify
```

Contributor coverage (instrument ``clangVerify`` only):

```bash
./scripts/coverage-sweep.sh       # after a normal build
./scripts/coverage-verify.sh      # full instrumented rebuild (slow)
```

## License

LLVM components use the [LLVM License](https://llvm.org/LICENSE.txt). See file headers in the tree.