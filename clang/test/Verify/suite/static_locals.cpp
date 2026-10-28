// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
//
// A static local with a constant initializer is an object at a fixed address
// that only its function names: its value at entry is whatever earlier calls
// left, the function writes it without naming it in a frame, and a call of
// any function that may reach the owner changes it.

namespace cv = cppverify;

int next_id()
  cv::post(cv::result >= 1 && cv::result <= 1000)
{
  static int last = 0;
  if (last < 0 || last >= 1000)
    last = 0;
  last = last + 1;
  return last;
}
// CHECK-DAG: Verified: next_id

// Its value at entry is not its initializer.
int first_id()
  cv::post(cv::result == 1)
{
  static int last = 0;
  last = last + 1;
  return last;
}
// CHECK-DAG: error: verification failed: first_id

// Callers state nothing about it.
int two_ids()
  cv::post(cv::result >= 2 && cv::result <= 2000)
{
  int a = next_id();
  int b = next_id();
  return a + b;
}
// CHECK-DAG: Verified: two_ids

// Records and arrays, through places.
struct Stats {
  int calls;
  int last;
};

int remember(int v)
  cv::pre(0 <= v && v <= 100)
  cv::post(cv::result == v)
{
  static Stats stats = {0, 0};
  static int seen[4] = {0, 0, 0, 0};
  if (stats.calls < 0 || stats.calls >= 1000000)
    stats.calls = 0;
  stats.calls = stats.calls + 1;
  stats.last = v;
  seen[stats.calls % 4] = v;
  return stats.last;
}
// CHECK-DAG: Verified: remember

// Within one call it keeps its value: nothing else names it.
int keeps(int v)
  cv::post(cv::result == v)
{
  static int saved = 0;
  saved = v;
  int other = next_id();
  return saved;
}
// CHECK-DAG: Verified: keeps

// A call that may reach the owner changes it, through other functions too.
void pass_on(int n)
  cv::decreases(n, 1)
  cv::post(true);

int owner(int n)
  cv::pre(n >= 0)
  cv::decreases(n, 0)
  cv::post(cv::result == 5)
{
  static int state = 0;
  state = 5;
  if (n > 0)
    pass_on(n - 1);
  return state;
}
// CHECK-DAG: error: verification failed: owner [postcondition]

void pass_on(int n)
{
  if (n > 0)
    owner(n - 1);
}
// CHECK-DAG: Unresolved: pass_on {{.*}}[reason=callee.contract]

// And a direct recursive call.
int recursive(int n)
  cv::pre(n >= 0)
  cv::decreases(n)
  cv::post(cv::result == 7)
{
  static int mark = 0;
  mark = 7;
  if (n > 0)
    recursive(n - 1);
  return mark;
}
// CHECK-DAG: error: verification failed: recursive [postcondition]

// A record changes as a whole.
int recursive_record(int n)
  cv::pre(n >= 0)
  cv::decreases(n)
  cv::post(cv::result == 3)
{
  static Stats marks = {0, 0};
  marks.last = 3;
  if (n > 0)
    recursive_record(n - 1);
  return marks.last;
}
// CHECK-DAG: error: verification failed: recursive_record [postcondition]

// A loop that calls back into the owner changes it at the loop's head too.
void call_back(int n)
  cv::decreases(n, 1)
  cv::post(true);

int looped(int n)
  cv::pre(n >= 0)
  cv::decreases(n, 0)
  cv::post(cv::result == 1)
{
  static int flag = 0;
  flag = 1;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n)
    cv::decreases(n - i)
  {
    call_back(n - 1);
  }
  return flag;
}
// CHECK-DAG: error: verification failed: looped [postcondition]

void call_back(int n)
{
  if (n > 0)
    looped(n - 1);
}

// cppverify::old of a static local is its value at entry.
int add_up(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(true)
{
  static int sum = 0;
  if (sum < 0 || sum > 1000000)
    sum = 0;
  cv::ghost int start = sum;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && sum == start + i)
    cv::invariant(start == cv::old(sum) || cv::old(sum) < 0 || cv::old(sum) > 1000000)
    cv::decreases(n - i)
  {
    sum = sum + 1;
  }
  return sum;
}
// CHECK-DAG: Verified: add_up

// The static local of a helper without a contract is the state of the
// function its body runs in, and of that function's callers.
int tick()
{
  static int ticks = 0;
  if (ticks < 0 || ticks >= 1000)
    ticks = 0;
  ticks = ticks + 1;
  return ticks;
}

int ticked()
  cv::post(cv::result >= 1 && cv::result <= 1000)
{
  return tick();
}
// CHECK-DAG: Verified: ticked

// In a loop of its function, an invariant may name it, and cppverify::old
// is its value at entry.
int count_up(int n)
  cv::pre(0 <= n && n <= 100)
  cv::post(true)
{
  static int total = 0;
  total = 0;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && total == i)
    cv::decreases(n - i)
  {
    total = total + 1;
  }
  cv::check(total == n);
  return total;
}
// CHECK-DAG: Verified: count_up

// Unsupported, located: an initializer that runs code, and pointers that
// would let the state escape.
int dynamic(int x)
  cv::post(true)
{
  static int first = x;
  return first;
}
// CHECK-DAG: error: dynamic: the static local first is initialized by running code at its first pass, which is not modeled; initialize it with a constant

int *leak()
  cv::post(true)
{
  static int value = 0;
  return &value;
}
// CHECK-DAG: error: leak: a pointer to the static local value is unsupported: its function's state would escape

int sum4(const int *p)
  cv::pre(cv::valid(p, 4))
  cv::post(true)
{
  return 0;
}

int pass_buffer()
  cv::post(true)
{
  static int buffer[4] = {0, 0, 0, 0};
  return sum4(buffer);
}
// CHECK-DAG: error: pass_buffer: a pointer into the static local 'buffer' is unsupported: its function's state would escape
