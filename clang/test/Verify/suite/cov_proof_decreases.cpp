// RUN: %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY

spec int id_spec(int n) { return n; }

proof void lemma_id(int n)
  pre(n >= 0 && n <= 10)
  post(id_spec(n) == n)
  decreases(n)
{
  ghost { reveal(id_spec); }
}

int walk(int n)
  pre(n >= 0 && n <= 3)
  post(result >= 0)
  decreases(n)
{
  int i = 0;
  while (i < n)
    invariant(i >= 0)
    decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}

// VERIFY-DAG: verified: lemma_id
// VERIFY-DAG: verified: walk