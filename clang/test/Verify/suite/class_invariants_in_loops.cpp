// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 %s -- -DGHOST_ADDRESS 2>&1 | FileCheck %s --check-prefix=GHOST
//
// A loop outside a class keeps the class invariants of the objects it
// reaches: the local objects alive at it and those its function's reference
// and pointer parameters address. Only the class's members change what an
// invariant states, and a public one keeps it; each invariant is still
// checked at the loop's entry and kept by its iterations, like the user's.
// A member function's own loops get none of its class's: it may break the
// invariant between calls.
//
// No proof here holds only because no execution reaches its end.
// CHECK-NOT: vacuous

namespace cv = cppverify;

class Meter {
public:
  Meter() cv::post(reading(this) == 0) : total(0), last(0) {}

  void add(int d)
    cv::pre(0 <= d && d <= 10 && reading(this) <= 1000)
    cv::post(reading(this) == cv::old(reading(this)) + d)
  {
    last = d;
    total = total + d;
  }

  // Counts the reading up again from 0: while its loop runs, last may
  // exceed total, and only the end restores the invariant.
  void recount(int n)
    cv::pre(0 <= n && n <= 10)
    cv::post(reading(this) == n)
  {
    total = 0;
    int i = 0;
    while (i < n)
      cv::invariant(0 <= i && i <= n && total == i && last == cv::old(last))
      cv::decreases(n - i)
    {
      total = total + 1;
      i = i + 1;
    }
    last = 0;
  }

  friend cv::spec int reading(const Meter *m);

private:
  int total;
  int last;

public:
  cv::type_invariant(0 <= last && last <= total);
};

cv::spec int reading(const Meter *m) { return m->total; }

// The loop keeps the meter's invariant without saying so.
int count_to(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(cv::result == n)
{
  Meter m;
  int i = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n && reading(&m) == i)
    cv::decreases(n - i)
  {
    m.add(1);
    i = i + 1;
  }
  cv::check(reading(&m) == n);
  return i;
}

// So does a loop over an object a reference addresses.
void fill(Meter &m, int n)
  cv::pre(0 <= n && n <= 100 && reading(&m) <= 100)
  cv::post(reading(&m) == cv::old(reading(&m)) + n)
  cv::modifies(m)
{
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && reading(&m) == cv::old(reading(&m)) + i)
    cv::decreases(n - i)
  {
    m.add(1);
  }
}

// And a do loop over one a pointer addresses, which may be null.
void drain(Meter *m, int n)
  cv::pre(m != nullptr && 1 <= n && n <= 100 && reading(m) <= 100)
  cv::post(reading(m) == cv::old(reading(m)) + n)
  cv::modifies(*m)
{
  int i = 0;
  do {
    m->add(1);
    i = i + 1;
  } while (i < n)
    cv::invariant(1 <= i && i <= n && reading(m) == cv::old(reading(m)) + i)
    cv::decreases(n - i);
}
// A pointer that may be null addresses no object whose invariant holds.
int idle(const Meter *m, int n)
  cv::pre(0 <= n && n <= 10)
  cv::post(cv::result == n)
{
  int i = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    i = i + 1;
  }
  return i;
}

#ifdef GHOST_ADDRESS
// Ghost code could keep the address of a local: it is still an error.
int kept()
  cv::post(cv::result == 0)
{
  Meter m;
  cv::ghost { const Meter *q = &m; }
  return 0;
}
// GHOST: class_invariants_in_loops.cpp:[[@LINE-3]]:32: error: kept: raw address-of is unsupported until lexical lifetime and escape effects are modeled
#endif

// CHECK-DAG: Verified: idle [backend=z3]
// CHECK-DAG: Verified: Meter::recount [backend=z3]
// CHECK-DAG: Verified: count_to [backend=z3]
// CHECK-DAG: Verified: fill [backend=z3]
// CHECK-DAG: Verified: drain [backend=z3]

// A friend may break an invariant, and a loop that does fails it: the
// invariant is checked, not assumed.
class Gauge {
  int lo;
  int hi;
  friend int spread(int n);

public:
  Gauge() cv::post(lo == 0 && hi == 5) : lo(0), hi(5) {}

  cv::type_invariant(lo <= hi);
};

int spread(int n)
  cv::pre(0 <= n && n <= 10)
  cv::post(cv::result >= 0)
{
  Gauge g;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && g.lo == i && g.hi == 5)
    cv::decreases(n - i)
  {
    g.lo = g.lo + 1;
  }
  return g.hi - g.lo;
}
// CHECK-DAG: class_invariants_in_loops.cpp:[[@LINE-16]]:25: error: verification failed: spread [invariant-preserved] [backend=z3] [reason=counterexample]
