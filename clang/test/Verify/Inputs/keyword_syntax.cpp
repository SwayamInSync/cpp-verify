// pre(x) and contract_assert in comments and "post(" in strings stay.
spec int sq(int x) recommends(x >= 0) { return x * x; }

int max_index(const int *a, int n)
  pre(n > 0 && cppverify::valid(a, n))
  post(0 <= result && result < n)
  post(forall(k, 0, n, a[k] <= a[result]))
{
  int best = 0;
  for (int i = 1; i < n; ++i)
    invariant(1 <= i && i <= n && 0 <= best && best < i)
    invariant(forall(k, 0, i, a[k] <= a[best]))
    decreases(n - i)
  {
    if (a[i] > a[best])
      best = i;
  }
  contract_assert(best < n);
  ghost { contract_assert(sq(best) >= 0); }
  return best;
}

const char *label() { return "post("; }

void inc(int *p) pre(p != nullptr && *p < 100) modifies(*p) post(*p == old(*p) + 1) { *p += 1; }
