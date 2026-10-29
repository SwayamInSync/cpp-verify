// RUN: not %cpp-verify --jobs=1 %s -- > %t 2>&1
// RUN: FileCheck %s < %t
// RUN: FileCheck %s --check-prefix=SOUND < %t
// RUN: %cpp-verify --lower-only --dump-ir=1 --function=twice_once %s -- 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: not %cpp-verify --jobs=1 %s -- -DORDER 2>&1 | FileCheck %s --check-prefix=ORDER
// RUN: not %cpp-verify --jobs=1 --function=old_index --function=new_index %s -- -std=c++14 2>&1 | FileCheck %s --check-prefix=CXX14
//
// An increment, a decrement, an assignment, or a comma expression may stand
// where its value is used: its write runs where C++ evaluates it, and the
// value is read there, the old one for a postfix operator. C++ leaves the
// order of unsequenced operands open, so a write that another operand may
// read is an error.
//
// SOUND-NOT: vacuous

namespace cv = cppverify;

int post_inc(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x)
{
  int y = x;
  int z = y++;
  cv::check(y == x + 1);
  return z;
}
// CHECK-DAG: Verified: post_inc

int pre_dec(int x)
  cv::pre(x > -100)
  cv::post(cv::result == x - 1)
{
  int y = x;
  return --y;
}
// CHECK-DAG: Verified: pre_dec

int chain()
  cv::post(cv::result == 0)
{
  int a, b;
  a = b = 0;
  return a + b;
}
// CHECK-DAG: Verified: chain

int compound_value(int x)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == 2 * x + 3)
{
  int y = x;
  int z = (y += 3) + x;
  cv::check(y == x + 3);
  return z;
}
// CHECK-DAG: Verified: compound_value

int first_nonzero(const int *p, int n)
  cv::pre(cv::valid(p, n) && n >= 1)
  cv::post(cv::result == p[0] || (p[0] == 0 && cv::result == -1))
{
  int c;
  if ((c = p[0]) != 0)
    return c;
  return -1;
}
// CHECK-DAG: Verified: first_nonzero

int sum(const int *a, int n)
  cv::pre(cv::valid(a, n) && 0 <= n && n <= 100)
  cv::pre(cv::forall(k, 0, n, 0 <= a[k] && a[k] <= 100))
  cv::post(0 <= cv::result && cv::result <= 100 * n)
{
  int s = 0;
  int i = 0;
  while (i < n)
    cv::invariant(0 <= i && i <= n && 0 <= s && s <= 100 * i)
    cv::decreases(n - i)
  {
    s = s + a[i++];
  }
  return s;
}
// CHECK-DAG: Verified: sum

void copy(int *dst, const int *src, int n)
  cv::pre(cv::valid(dst, n) && cv::valid(src, n) && 0 <= n && n < 1000)
  cv::modifies(dst[0 : n])
  cv::post(cv::forall(k, 0, n, dst[k] == src[k]))
{
  int *d = dst;
  const int *s = src;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && d == dst + i && s == src + i)
    cv::invariant(cv::forall(k, 0, i, dst[k] == src[k]))
    cv::decreases(n - i)
  {
    *d++ = *s++;
  }
}
// CHECK-DAG: Verified: copy

int countdown(int k)
  cv::pre(0 <= k && k < 100)
  cv::post(cv::result == 0)
{
  while (k-- > 0)
    cv::invariant(0 <= k && k < 100)
    cv::decreases(k)
  {
  }
  return k + 1;
}
// CHECK-DAG: Verified: countdown

int comma_value(int i, int j)
  cv::pre(0 <= i && i < 100 && 0 <= j && j < 100)
  cv::post(cv::result == i + j + 1)
{
  int a = i;
  int b = j;
  for (int k = 0; k < 1; k++, a++, b--)
    cv::invariant(0 <= k && k <= 1 && a == i + k && b == j - k)
    cv::decreases(1 - k)
  {
  }
  return (a++, a + b);
}
// CHECK-DAG: Verified: comma_value

int old_of_memory(int *p)
  cv::pre(p != nullptr && *p < 1000)
  cv::modifies(*p)
  cv::post(cv::result == cv::old(*p) && *p == cv::old(*p) + 1)
{
  return (*p)++;
}
// CHECK-DAG: Verified: old_of_memory

// The target of a compound assignment is read and written once: its increment
// runs once.
int twice_once(int *a, int i)
  cv::pre(cv::valid(a, 4) && 0 <= i && i < 4 && a[i] < 1000)
  cv::modifies(a[0 : 4])
  cv::post(a[i] == cv::old(a[i]) + 1 && cv::result == i + 1)
{
  a[i++] += 1;
  return i;
}
// CHECK-DAG: Verified: twice_once
// VCR-LABEL: fn twice_once
// VCR:      assign __value_[[ONE:[0-9]+]]
// VCR-NEXT:   1
// VCR-NEXT: assign __value_[[K:[0-9]+]]
// VCR-NEXT:   i
// VCR-NEXT: assign i
// VCR-NOT:  assign i
// VCR:      store
// VCR-NEXT:   +
// VCR-NEXT:     a
// VCR-NEXT:     *
// VCR-NEXT:       cast
// VCR-NEXT:         __value_[[K]]
// VCR:          load
// VCR:                __value_[[K]]
// VCR:          __value_[[ONE]]
// VCR-NEXT: return

int nested_once(int *a, int i)
  cv::pre(cv::valid(a, 4) && 0 <= i && i < 4 && a[i] < 1000)
  cv::modifies(a[0 : 4])
  cv::post(cv::result == cv::old(a[i]) && a[i] == cv::old(a[i]) + 1)
{
  int k = i;
  int v = a[k++]++;
  cv::check(k == i + 1);
  return v;
}
// CHECK-DAG: Verified: nested_once

// A comma in such a target runs its first operand once.
int comma_target(int *a, int i)
  cv::pre(cv::valid(a, 4) && 0 <= i && i < 3 && a[i + 1] < 1000)
  cv::modifies(a[0 : 4])
  cv::post(a[i + 1] == cv::old(a[i + 1]) + 1 && cv::result == i + 1)
{
  int k = i;
  a[(k++, k)] += 1;
  return k;
}
// CHECK-DAG: Verified: comma_target

// The value is read before the target is located (C++17).
void old_index(int *a, int i)
  cv::pre(cv::valid(a, 4) && 0 <= i && i < 3)
  cv::modifies(a[0 : 4])
  cv::post(a[i] == i)
{
  int k = i;
  a[k++] = k;
}
// CHECK-DAG: Verified: old_index
// CXX14-DAG: error: old_index: before C++17 the order of an assignment's operands is open, and a call or a write in one may change what the other reads

// The target is located after the value's write.
void new_index(int *a, int i)
  cv::pre(cv::valid(a, 4) && 0 <= i && i < 3)
  cv::modifies(a[0 : 4])
  cv::post(a[i + 1] == i)
{
  int k = i;
  a[k] = k++;
}
// CHECK-DAG: Verified: new_index
// CXX14-DAG: error: new_index: before C++17 the order of an assignment's operands is open

// A write on one path of a ?: or && runs on that path only.
int on_path(int x, bool c)
  cv::pre(0 <= x && x < 100)
  cv::post(cv::result == (c ? x + 1 : x))
{
  int y = x;
  int v = c ? y++ : 0;
  int w = (c && (v = 1)) ? 0 : 0;
  return y + w;
}
// CHECK-DAG: Verified: on_path

int past_end(const int *a, int n)
  cv::pre(cv::valid(a, n) && n == 1)
  cv::post(true)
{
  int i = 0;
  int v = a[i++];
  cv::check(v == a[0]);
  return a[i++];
}
// CHECK-DAG: side_effect_values.cpp:[[@LINE-2]]:10: error: verification failed: past_end [bounds]

int wrong_old(int x)
  cv::pre(x < 100)
  cv::post(cv::result == x + 1)
{
  int y = x;
  return y++;
}
// CHECK-DAG: side_effect_values.cpp:[[@LINE-5]]:23: error: verification failed: wrong_old [postcondition]

#ifdef ORDER
int unsequenced(int i)
  cv::pre(0 <= i && i < 100)
  cv::post(true)
{
  return i++ + i;
}
// ORDER-DAG: error: unsequenced: C++ leaves the order of these operands open, and a call or a write in one may change what the other reads

int read_twice(int i, int j)
  cv::pre(0 <= i && i < 100)
  cv::post(cv::result == j)
{
  return j;
}

int arguments(int i)
  cv::pre(0 <= i && i < 99)
  cv::post(true)
{
  return read_twice(i++, i);
}
// ORDER-DAG: error: arguments: C++ leaves the order of these call arguments open, and a call or a write in one may change what another reads

struct Buf {
  int *data;
};

int index_write(Buf *b)
  cv::pre(b != nullptr && cv::valid(b->data, 4))
  cv::modifies(b->data[0 : 4])
  cv::post(true)
{
  return b->data[b->data[0]++];
}
// ORDER-DAG: error: index_write: C++ leaves the order of these operands open

struct Pair {
  int f;
  int g;
};

int field_read(Pair s)
  cv::pre(0 <= s.f && s.f < 100)
  cv::post(true)
{
  return s.f++ + s.f;
}
// ORDER-DAG: error: field_read: C++ leaves the order of these operands open

struct Counter {
  int n;

  int bump()
    cv::pre(0 <= n && n < 100)
    cv::modifies(n)
    cv::post(true)
  {
    return n++ + n;
  }
};
// ORDER-DAG: error: Counter::bump: C++ leaves the order of these operands open

int dynamic_assign()
  cv::post(true)
{
  int *q = new int(1);
  int *p = nullptr;
  if ((p = q) != nullptr)
    delete q;
  return 0;
}
// ORDER-DAG: error: dynamic_assign: the value of an assignment, an increment, or a decrement of a pointer to dynamic storage is unsupported
#endif
