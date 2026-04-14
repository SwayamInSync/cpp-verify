// RUN: %clang_cc1 -std=c++17 -fverify-contracts -ast-dump %s | FileCheck %s
// RUN: %clang_cc1 -std=c++17 -fverify-contracts -emit-llvm -o %t %s
// RUN: FileCheck -check-prefix=LLVM %s < %t
//
// Exhaustive test for ghost blocks and contract_assert:
// - Correct AST nodes
// - Multiple ghost blocks
// - Nested statements in ghost blocks
// - Zero codegen (no IR emitted for ghost content)

// ---------------------------------------------------------------------------
// 1. Basic ghost block with contract_assert
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} basic_ghost 'int (int)'
// CHECK: GhostBlockStmt
// CHECK:   CompoundStmt
// CHECK:     ContractAssertStmt
// CHECK:       BinaryOperator {{.*}} 'bool' '>='
int basic_ghost(int x)
  pre(x >= 0)
  post(result >= 0)
{
  ghost {
    contract_assert(x >= 0);
  }
  return x;
}

// ---------------------------------------------------------------------------
// 2. Multiple ghost blocks in one function
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} multi_ghost 'int (int)'
// CHECK: GhostBlockStmt
// CHECK:   ContractAssertStmt
// CHECK: GhostBlockStmt
// CHECK:   ContractAssertStmt
int multi_ghost(int x)
  pre(x >= 0)
  post(result == x + x)
{
  ghost {
    contract_assert(x >= 0);
  }
  int r = x + x;
  ghost {
    contract_assert(r == x + x);
  }
  return r;
}

// ---------------------------------------------------------------------------
// 3. Ghost block with multiple contract_assert
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} multi_assert 'int (int)'
// CHECK: GhostBlockStmt
// CHECK:   ContractAssertStmt
// CHECK:     BinaryOperator {{.*}} 'bool' '>='
// CHECK:   ContractAssertStmt
// CHECK:     BinaryOperator {{.*}} 'bool' '<'
// CHECK:   ContractAssertStmt
// CHECK:     BinaryOperator {{.*}} 'bool' '!='
int multi_assert(int x)
  pre(x >= 0)
  pre(x < 100)
{
  ghost {
    contract_assert(x >= 0);
    contract_assert(x < 100);
    contract_assert(x != -1);
  }
  return x;
}

// ---------------------------------------------------------------------------
// 4. Ghost block inside loop body
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} ghost_in_loop 'int (int)'
// CHECK: WhileStmt
// CHECK:   GhostBlockStmt
// CHECK:     ContractAssertStmt
int ghost_in_loop(int n)
  pre(n >= 0)
  post(result >= 0)
{
  int s = 0, i = 0;
  while (i < n)
    invariant(s >= 0)
    decreases(n - i)
  {
    ghost {
      contract_assert(s >= 0);
    }
    s = s + i;
    i = i + 1;
  }
  return s;
}

// ---------------------------------------------------------------------------
// 5. Ghost block inside if branch
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} ghost_in_if 'int (int)'
// CHECK: IfStmt
// CHECK:   GhostBlockStmt
// CHECK:     ContractAssertStmt
int ghost_in_if(int x)
  pre(x >= -100)
  post(result >= 0)
{
  if (x < 0) {
    ghost {
      contract_assert(x < 0);
    }
    return -x;
  }
  return x;
}

// ---------------------------------------------------------------------------
// 6. Ghost block with variable declarations (allowed inside ghost)
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} ghost_with_vars 'int (int)'
// CHECK: GhostBlockStmt
// CHECK:   CompoundStmt
// CHECK:     DeclStmt
// CHECK:       VarDecl {{.*}} tmp 'int'
// CHECK:     ContractAssertStmt
int ghost_with_vars(int x)
  pre(x >= 0)
{
  ghost {
    int tmp = x + 1;
    contract_assert(tmp > 0);
  }
  return x;
}

// ---------------------------------------------------------------------------
// 7. Empty ghost block
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} empty_ghost 'int (int)'
// CHECK: GhostBlockStmt
// CHECK:   CompoundStmt
int empty_ghost(int x) {
  ghost {
  }
  return x;
}

// ---------------------------------------------------------------------------
// 8. Ghost block with complex assertion expression
// ---------------------------------------------------------------------------
// CHECK: FunctionDecl {{.*}} ghost_complex 'int (int, int)'
// CHECK: GhostBlockStmt
// CHECK:   ContractAssertStmt
// CHECK:     BinaryOperator {{.*}} 'bool' '&&'
int ghost_complex(int a, int b)
  pre(a >= 0)
  pre(b >= 0)
{
  ghost {
    contract_assert(a >= 0 && b >= 0);
  }
  return a + b;
}

// ---------------------------------------------------------------------------
// Verify ghost blocks produce no IR (codegen)
// ---------------------------------------------------------------------------
// Ghost code should NOT appear in LLVM IR output.

// basic_ghost: only has x as parameter, ghost block stripped
// LLVM: define {{.*}} @_Z11basic_ghosti(i32 {{.*}} %x)
// LLVM: ret i32

// multi_ghost: ghost blocks stripped, only real code remains
// LLVM: define {{.*}} @_Z11multi_ghosti(i32 {{.*}} %x)
// LLVM: ret i32

// ghost_with_vars: local 'tmp' declared inside ghost should not appear
// LLVM: define {{.*}} @_Z15ghost_with_varsi(i32 {{.*}} %x)
// LLVM-NOT: %tmp
// LLVM: ret i32
