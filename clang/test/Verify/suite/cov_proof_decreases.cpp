// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

cppverify::spec int id_spec(int n) { return n; }

cppverify::proof void lemma_id(int n)
  cppverify::pre(n >= 0 && n <= 10)
  cppverify::post(id_spec(n) == n)
  cppverify::decreases(n)
{
  cppverify::ghost { cppverify::reveal(id_spec); }
}

int walk(int n)
  cppverify::pre(n >= 0 && n <= 3)
  cppverify::post(cppverify::result >= 0)
  cppverify::decreases(n)
{
  int i = 0;
  while (i < n)
    cppverify::invariant(i >= 0)
    cppverify::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}

// VERIFY-DAG: Verified: lemma_id
// VERIFY-DAG: Verified: walk