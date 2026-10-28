// RUN: %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: not %cpp-verify --jobs=1 %s -- -DFORGET_WRAP 2>&1 | FileCheck %s --check-prefix=BUG
//
// The ring buffer case study (website/source/case-studies/ring-buffer.rst):
// a class template whose contract states it is a FIFO queue, through a
// view of its elements, and clients that rely on that contract alone.
//
// No proof here holds only because no execution reaches its end.
// CHECK-NOT: vacuous

#include <cassert>

namespace cv = cppverify;

template <int N> class Ring;
template <int N> cv::spec int size(const Ring<N> *r);
template <int N> cv::spec int at(const Ring<N> *r, int i);

// A queue of at most N ints in a fixed array, as embedded code keeps one:
// its elements, oldest first, are buf[head], buf[head + 1], ..., wrapping
// around at N.
template <int N>
class Ring {
public:
  Ring()
    cv::post(size(this) == 0)
    : head(0), count(0)
  {
    for (int i = 0; i < N; i = i + 1)
      cv::invariant(0 <= i && i <= N && head == 0 && count == 0)
      cv::invariant(cv::forall(k, 0, i, buf[k] == 0))
      cv::decreases(N - i)
    {
      buf[i] = 0;
    }
  }

  bool full() const
    cv::post(cv::result == (size(this) == N))
  {
    return count == N;
  }

  // Appends v after the newest element.
  void push(int v)
    cv::pre(size(this) < N)
    cv::post(size(this) == cv::old(size(this)) + 1)
    cv::post(at(this, size(this) - 1) == v)
    cv::post(cv::forall(k, 0, cv::old(size(this)),
                        at(this, k) == cv::old(at(this, k))))
  {
    assert(count < N);
    buf[(head + count) % N] = v;
    count = count + 1;
  }

  // Removes the oldest element and returns it.
  int pop()
    cv::pre(size(this) > 0)
    cv::post(size(this) == cv::old(size(this)) - 1)
    cv::post(cv::result == cv::old(at(this, 0)))
    cv::post(cv::forall(k, 0, size(this),
                        at(this, k) == cv::old(at(this, k + 1))))
  {
    int v = buf[head];
#ifdef FORGET_WRAP
    head = head + 1;
#else
    head = (head + 1) % N;
#endif
    count = count - 1;
    return v;
  }

private:
  int buf[N];
  int head;
  int count;

  template <int M> friend cv::spec int size(const Ring<M> *r);
  template <int M> friend cv::spec int at(const Ring<M> *r, int i);

public:
  cv::type_invariant(0 <= head && head < N && 0 <= count && count <= N);
};

// How many elements r holds.
template <int N> cv::spec int size(const Ring<N> *r) { return r->count; }

// The element i places after the oldest.
template <int N> cv::spec int at(const Ring<N> *r, int i)
{
  return r->buf[(r->head + i) % N];
}

// The samples come out in the order they went in.
int first_two()
  cv::post(cv::result == 12)
{
  cv::hide(at<4>);
  Ring<4> r;
  int samples[3] = {1, 2, 3};
  for (int s : samples)
    cv::invariant(size(&r) == cv::index)
    cv::invariant(cv::forall(k, 0, cv::index, at(&r, k) == samples[k]))
    r.push(s);
  if (!r.full())
    r.push(4);
  int a = r.pop();
  int b = r.pop();
  return 10 * a + b;
}

enum class Command { Push, Pop, Skip };

// Applies one command to r: a push of v, a pop, which returns the oldest
// element, or nothing.
int apply(Ring<4> &r, Command c, int v)
  cv::pre(c != Command::Push || size(&r) < 4)
  cv::pre(c != Command::Pop || size(&r) > 0)
  cv::post(c != Command::Pop || cv::result == cv::old(at(&r, 0)))
  cv::post(c != Command::Skip || size(&r) == cv::old(size(&r)))
  cv::modifies(r)
{
  switch (c) {
  case Command::Push:
    r.push(v);
    return 0;
  case Command::Pop:
    return r.pop();
  case Command::Skip:
    break;
  }
  return 0;
}

// CHECK-DAG: Verified: Ring<4>::Ring [backend=z3]
// CHECK-DAG: Verified: Ring<4>::full [backend=z3]
// CHECK-DAG: Verified: Ring<4>::push [backend=z3]
// CHECK-DAG: Verified: Ring<4>::pop [backend=z3]
// CHECK-DAG: Verified: first_two [backend=z3]
// CHECK-DAG: Verified: apply [backend=z3]
// CHECK: Summary: 6 verified

// Without the wraparound, pop moves head past the array: the class
// invariant fails at its exit, and the path shows the store that breaks it.
// BUG: ring_buffer.cpp:{{[0-9]+}}:58: error: verification failed: Ring<4>::pop [type-invariant] [backend=z3] [reason=counterexample]
// BUG: note: counterexample: this = {{[0-9]+}}
// BUG: note: stores 4 at address {{[0-9]+}}
// BUG-NEXT: {{.*}}head = head + 1;
// BUG: Unresolved: first_two [backend=z3] [reason=callee.contract] (relies on the contract of Ring<4>::pop, which is not established)
