// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --implicit-check-not=plain
//
// An assertion or ghost block is an obligation even in a function without a
// contract clause. Only a function that states nothing is left alone.

void asserts_false()
{
  cppverify::check(false);
}

void ghost_false()
{
  cppverify::ghost { cppverify::check(false); }
}

int asserts_argument(int n)
{
  cppverify::check(n > 0);
  return n;
}

int loop_invariant(int n)
{
  int i = 0;
  while (i < 10)
    cppverify::invariant(0 <= i && i <= 10)
    cppverify::decreases(10 - i)
  {
    i = i + 1;
  }
  cppverify::check(i == 10);
  return i;
}

int plain(int n)
{
  return n + 1;
}

// CHECK-DAG: verification failed: asserts_false [{{.*}}::assertion@
// CHECK-DAG: verification failed: ghost_false [{{.*}}::assertion@
// CHECK-DAG: verification failed: asserts_argument [{{.*}}::assertion@{{.*}}n [ssa=n_0] [type=i32] = {{-?[0-9]+}}
// CHECK-DAG: Verified: loop_invariant
