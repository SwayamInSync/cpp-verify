// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify --check-ub %s -- 2>&1 | FileCheck %s --check-prefixes=CHECK,DECIDED
// RUN: not %cpp-verify --check-ub --int-encoding=bitvector --timeout=5000 %s -- 2>&1 | FileCheck %s --check-prefixes=CHECK,BV
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=1 %s -- 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=2 %s -- 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=3 %s -- 2>&1 | FileCheck %s --check-prefix=VC
// RUN: not %cpp-verify --no-check-ub %s -- 2>&1 | FileCheck %s --check-prefix=NOUB

// Under --check-ub the non-aliasing default separates whole valid(p, n)
// extents; callers prove it, and `aliases` pairs may still overlap.

cppverify::spec bool valid(const int *p, int n) { return true; }
cppverify::spec bool valid(int *p, int n) { return true; }

void copy(const int *a, int *out, int n)
  cppverify::pre(n >= 0 && valid(a, n) && valid(out, n))
  cppverify::modifies(*out)
  cppverify::post(cppverify::forall(i, 0, n, out[i] == a[i]))
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::invariant(cppverify::forall(j, 0, i, out[j] == a[j]))
    cppverify::decreases(n - i)
  {
    out[i] = a[i];
    i = i + 1;
  }
}
// DECIDED-DAG: Verified: copy
// BV-DAG: {{Verified|Unresolved}}: copy
// Without extents only single elements are separated, so a write to out[i]
// may overwrite a[j] and the postcondition is genuinely false.
// NOUB-DAG: verification failed: copy

// The widened clause scales each extent by sizeof(int).
// VCR-LABEL: fn copy
// VCR:      {{^ +\*$}}
// VCR-NEXT: cast
// VCR-NEXT: n
// VCR-NEXT: 4
// VCR-NEXT: out
// VCR-NEXT: <=
// VCR-NEXT: +
// VCR-NEXT: out
// VCR-NEXT: *
// VCR-NEXT: cast
// VCR-NEXT: n
// VCR-NEXT: 4
// VCR-NEXT: a
// VCR-NEXT: post

void wrong_copy(const int *a, int *out, int n)
  cppverify::pre(n >= 0 && valid(a, n) && valid(out, n))
  cppverify::modifies(*out)
  cppverify::post(cppverify::forall(i, 0, n, out[i] == a[i]))
{
  int i = 0;
  while (i < n)
    cppverify::invariant(0 <= i && i <= n)
    cppverify::invariant(cppverify::forall(j, 0, i, out[j] == a[j]))
    cppverify::decreases(n - i)
  {
    out[i] = a[n - 1 - i];
    i = i + 1;
  }
}
// DECIDED-DAG: verification failed: wrong_copy [{{.*}}::invariant-preserved@
// BV-DAG: {{verification failed|Unresolved}}: wrong_copy

// The separation must not make the preconditions contradictory.
void separation_is_satisfiable(const int *a, int *out, int n)
  cppverify::pre(n > 1 && valid(a, n) && valid(out, n))
  cppverify::post(false)
{
}
// CHECK-DAG: verification failed: separation_is_satisfiable

// A scalar pointer is separated from a whole extent as well.
void extent_and_scalar(int *buffer, int *count, int n)
  cppverify::pre(n >= 0 && valid(buffer, n) && count != nullptr)
  cppverify::modifies(*count)
  cppverify::post(cppverify::forall(i, 0, n, buffer[i] == cppverify::old(buffer[i])))
{
  *count = n;
}
// CHECK-DAG: Verified: extent_and_scalar

// Call sites prove the separation. The callees do not write, so the callers
// need no range frame for a sub-slice.
int inspect(int *out, const int *a, int n)
  cppverify::pre(n >= 0 && valid(out, n) && valid(a, n))
{
  return 0;
}

int shift_left(int *dst, int *src, int n)
  cppverify::aliases(dst, src)
  cppverify::pre(n >= 0 && valid(dst, n) && valid(src, n))
{
  return 0;
}

int disjoint_caller(int *buffer)
  cppverify::pre(valid(buffer, 8))
{
  return inspect(buffer + 4, buffer, 4);
}
// CHECK-DAG: Verified: disjoint_caller

int overlapping_caller(int *buffer)
  cppverify::pre(valid(buffer, 8))
{
  return inspect(buffer + 2, buffer, 4);
}
// CHECK-DAG: verification failed: overlapping_caller [{{.*}}::aliasing@

int empty_caller(int *buffer)
  cppverify::pre(valid(buffer, 8))
{
  return inspect(buffer + 2, buffer, 0);
}
// CHECK-DAG: Verified: empty_caller

int aliasing_caller(int *buffer)
  cppverify::pre(valid(buffer, 8))
{
  return shift_left(buffer, buffer + 2, 4);
}
// CHECK-DAG: Verified: aliasing_caller

// The callee's clauses are asserted at the call under their own kinds: the
// explicit precondition, element separation, each extent's validity, and
// extent separation. A parameter with a declared extent has no single-object
// validity of its own.
// PASSIVE-LABEL: passive disjoint_caller
// PASSIVE: assert precondition
// PASSIVE: assert aliasing
// PASSIVE: assert pointer-validity
// PASSIVE: assert pointer-validity
// PASSIVE: assert aliasing
// PASSIVE: assert missing-return
// PASSIVE-LABEL: passive overlapping_caller

// VC-LABEL: vc overlapping_caller
// VC: obligation {{.*}} aliasing
// VC: obligation {{.*}} aliasing
