# CppVerify — Clang fork for deductive C++ verification

> [!NOTE]
> **Documentation:** [https://swayaminsync.github.io/cpp-verify/](https://swayaminsync.github.io/cpp-verify/) (guide + language reference)
>
> **Quick start:** `./setup.sh` from the repository root (this tree).

> [!NOTE]
> LLVM CI workflows are limited (full builds are expensive). Build `clang` and `cpp-verify` locally and run `./build/bin/llvm-lit clang/test/Verify`.

> This is a fork of [LLVM/Clang](https://github.com/llvm/llvm-project) (pinned to
> `llvmorg-22.1.3`) extended to **CppVerify**: a deductive verification system
> for C++ built directly into the Clang.

CppVerify adds first-class contract syntax (`pre`, `post`, `invariant`,
`decreases`, `ghost`, `spec`, `proof`) to C++, type-checked by Clang Sema and
discharged by Z3 via a weakest-precondition calculus backend. It occupies an
entirely uncontested niche: the only deductive verifier for modern C++ built on
Clang, with native contract syntax rather than comments or macros.

## What it looks like

```cpp
spec int fibo(int n) decreases(n) {
    if (n <= 1) return n;
    return fibo(n - 1) + fibo(n - 2);
}

int safe_fib(int n)
  pre(n >= 0)
  pre(n <= 45)
  post(result == fibo(n))
{
    if (n <= 1) return n;
    int a = 0, b = 1, i = 2;
    while (i <= n)
      invariant(2 <= i && i <= n + 1)
      invariant(b == fibo(i - 1))
      decreases(n - i + 1)
    {
        int tmp = a + b;
        a = b;
        b = tmp;
        i++;
    }
    return b;
}
```

## Contract syntax reference

| Syntax                    | Where                             | Meaning                                                              |
| ------------------------- | --------------------------------- | -------------------------------------------------------------------- |
| `pre(expr)`               | After function `)`                | Precondition — caller must satisfy                                   |
| `post(expr)`              | After function `)`                | Postcondition — callee must establish; may use `result` and `old(x)` |
| `invariant(expr)`         | After `while`/`for` condition `)` | Loop invariant                                                       |
| `decreases(expr)`         | After `while`/`for` condition `)` | Termination measure                                                  |
| `ghost { ... }`           | Statement                         | Ghost block — proof steps, stripped by CodeGen                       |
| `contract_assert(expr)`   | Statement                         | Verification condition (not a runtime check)                         |
| `spec T f(...)`           | Declaration                       | Pure spec function — interpreted by verifier only                    |
| `proof void f(...)`       | Declaration                       | Ghost proof function — establishes lemmas                            |
| `forall(i, lo, hi, expr)` | Expression                        | Bounded universal quantifier                                         |
| `exists(i, lo, hi, expr)` | Expression                        | Bounded existential quantifier                                       |
| `old(expr)`               | Inside `post`                     | Value of `expr` at function entry                                    |
| `result`                  | Inside `post`                     | Return value of the enclosing function                               |

All contract syntax is gated behind `-fverify-contracts`. Without the flag,
none of these names are reserved — existing C++ that uses `pre`, `post`, etc.
as identifiers compiles unchanged.

## Build the cpp-verify clang compiler

```bash
cmake -S llvm -B build -G Ninja \
    -DCMAKE_BUILD_TYPE=Release \
    -DLLVM_ENABLE_PROJECTS="clang" \
    -DLLVM_TARGETS_TO_BUILD="X86,AArch64" \
    -DCMAKE_EXPORT_COMPILE_COMMANDS=ON

# Symlink compile_commands.json for clangd / IDE integration
ln -sf build/compile_commands.json compile_commands.json

ninja -C build clang -j$(nproc)
```

## Usage

```bash
# Verify only (Z3 backend)
./build/bin/cpp-verify -std=c++17 file.cpp

# Verify + compile (parallel SMT + stripped codegen)
./build/bin/clang++ -std=c++17 -fverify-contracts -c file.cpp -o file.o

# Compile with contracts, skip SMT
./build/bin/clang++ -std=c++17 -fverify-contracts -fno-verify -c file.cpp -o file.o

# Dump IR layers: 1=vcr 2=passive 3=vc 4=z3
./build/bin/cpp-verify --dump-ir=1,2 file.cpp

# Frontend introspection
./build/bin/clang++ -cc1 -fverify-contracts -dump-tokens file.cpp
./build/bin/clang++ -cc1 -fverify-contracts -ast-dump file.cpp
```

## Architecture

```
C++ source with contracts
    │
    ▼
Clang Frontend  (modified Parser + Sema + AST)
    │  Annotated AST with contract nodes
    ▼
ASTConverter    (Clang AST → Layer 1 VCR IR)
    │  Typed, control-flow-preserving IR
    ▼
Passivize       (Layer 1 → Layer 2 SSA)
    │  Havoc / assume / assert, no loops
    ▼
WP Calculus     (weakest precondition, backward pass)
    │  Verification conditions
    ▼
Z3 Encoding     (VCs → Z3 formulas, check UNSAT)
    │  sat / unsat / unknown
    ▼
Diagnostics     (Clang-style errors + counterexamples)
```

Normal compilation skips everything after the frontend: CodeGen simply ignores
all ghost/contract AST nodes.

## Competitive landscape

| Tool          | Frontend              | C++ support    | Contract syntax |
| ------------- | --------------------- | -------------- | --------------- |
| Frama-C       | Custom OCaml          | Prototype only | ACSL comments   |
| VCC           | Custom                | C only (dead)  | Macros          |
| VeriFast      | Custom                | No             | Comments        |
| CBMC          | Custom goto-cc        | Partial        | Assertions only |
| Verus         | Rust compiler         | No (Rust only) | First-class     |
| **CppVerify** | **Clang (this fork)** | **Native**     | **First-class** |
