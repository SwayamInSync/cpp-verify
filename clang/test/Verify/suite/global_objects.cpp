// RUN: not %cpp-verify --jobs=1 %s -- 2>&1 | FileCheck %s
// RUN: %cpp-verify --lower-only --dump-ir=1 --function=set_mode %s -- | FileCheck %s --check-prefix=L1
// RUN: %cpp-verify --lower-only --dump-ir=1 --function=read_entry %s -- | FileCheck %s --check-prefix=ELEM
//
// A mutable global record or array is one object at its fixed address:
// its fields and elements are cells, read and written through places, with
// every index bounded by its array and every write within the function's
// modifies clause.

namespace cv = cppverify;

struct Config {
  int mode;
  int limit;
  int table[4];
};

Config config;
int history[8];
int count;

void set_mode(int m)
  cv::modifies(config.mode)
  cv::post(config.mode == m && config.limit == cv::old(config.limit))
{
  config.mode = m;
}
// CHECK-DAG: Verified: set_mode
// The field's cell: the object's address in the global region plus the
// field's offset.
// L1:      store
// L1-NEXT:   +
// L1-NEXT:     18446744069414584320
// L1-NEXT:     0
// L1-NEXT:   m

void set_mode_unframed(int m)
  cv::modifies(config.limit)
{
  config.mode = m;
}
// CHECK-DAG: error: verification failed: set_mode_unframed [frame]

int read_entry(int i)
  cv::pre(0 <= i && i < 4)
  cv::post(cv::result == config.table[i])
{
  return config.table[i];
}
// CHECK-DAG: Verified: read_entry
// An element is a place in the object, its index bounded by its array.
// ELEM:      load
// ELEM-NEXT:   +
// ELEM-NEXT:     +
// ELEM-NEXT:       18446744069414584320
// ELEM-NEXT:       8
// ELEM:      access_condition
// ELEM-NEXT:   &&
// ELEM-NEXT:     >=
// ELEM-NEXT:       i
// ELEM-NEXT:       0
// ELEM-NEXT:     <
// ELEM-NEXT:       i
// ELEM-NEXT:       4

int read_past(int i)
  cv::pre(0 <= i && i <= 4)
{
  return config.table[i];
}
// CHECK-DAG: error: verification failed: read_past [bounds]

void clear_history()
  cv::modifies(history[0 : 8])
  cv::post(cv::forall(k, 0, 8, history[k] == 0))
{
  for (int i = 0; i < 8; i = i + 1)
    cv::invariant(0 <= i && i <= 8)
    cv::invariant(cv::forall(k, 0, i, history[k] == 0))
    cv::modifies(history[0 : 8])
    cv::decreases(8 - i)
  {
    history[i] = 0;
  }
}
// CHECK-DAG: Verified: clear_history

// A callee that writes one field keeps every other cell of the object.
int keeps_limit()
  cv::modifies(config.mode)
  cv::post(cv::result == cv::old(config.limit))
{
  set_mode(3);
  return config.limit;
}
// CHECK-DAG: Verified: keeps_limit

// The whole object as a footprint.
void reset_config()
  cv::modifies(config)
  cv::post(config.mode == 0 && config.table[3] == 0)
{
  config.mode = 0;
  config.limit = 0;
  config.table[3] = 0;
}
// CHECK-DAG: Verified: reset_config

// A pointer into a global array is bounded by it.
int sum(const int *p, int n)
  cv::pre(cv::valid(p, n) && 0 <= n && n <= 8)
  cv::pre(cv::forall(k, 0, n, 0 <= p[k] && p[k] <= 100))
  cv::post(cv::result >= 0)
{
  int s = 0;
  for (int i = 0; i < n; i = i + 1)
    cv::invariant(0 <= i && i <= n && 0 <= s && s <= 100 * i)
    cv::decreases(n - i)
  {
    s = s + p[i];
  }
  return s;
}

int history_sum()
  cv::pre(cv::forall(k, 0, 8, 0 <= history[k] && history[k] <= 100))
  cv::post(cv::result >= 0)
{
  return sum(history, 8);
}
// CHECK-DAG: Verified: history_sum

int history_sum_past()
  cv::pre(cv::forall(k, 0, 8, 0 <= history[k] && history[k] <= 100))
{
  return sum(history + 1, 8);
}
// CHECK-DAG: error: verification failed: history_sum_past

int through_pointer(int i)
  cv::pre(0 <= i && i < 8)
  cv::post(cv::result == history[i])
{
  int *p = history;
  return p[i];
}
// CHECK-DAG: Verified: through_pointer

int through_pointer_past()
  cv::post(true)
{
  int *p = history;
  return p[8];
}
// CHECK-DAG: error: verification failed: through_pointer_past [bounds]

// A scalar global next to the objects is still its own cell.
void bump_count()
  cv::pre(count < 100)
  cv::modifies(count)
  cv::post(count == cv::old(count) + 1 && config.mode == cv::old(config.mode))
{
  count = count + 1;
}
// CHECK-DAG: Verified: bump_count

// A pointer to a field, given to a callee that writes through it: the
// caller's frame must cover the field, and the other cells keep their values.
void put(int *p, int v)
  cv::pre(p != nullptr)
  cv::modifies(*p)
  cv::post(*p == v)
{
  *p = v;
}

void set_limit(int v)
  cv::modifies(config.limit)
  cv::post(config.limit == v && config.mode == cv::old(config.mode))
{
  put(&config.limit, v);
}
// CHECK-DAG: Verified: set_limit

void set_limit_unframed(int v)
  cv::modifies(config.mode)
{
  put(&config.limit, v);
}
// CHECK-DAG: error: verification failed: set_limit_unframed [frame]

// Records in arrays, and arrays of arrays.
struct Slot {
  int key;
  int value;
};
Slot slots[3];
int grid[3][3];

int find_key(int k)
  cv::post(-1 <= cv::result && cv::result < 3)
  cv::post(cv::result == -1 || slots[cv::result].key == k)
{
  for (int i = 0; i < 3; i = i + 1)
    cv::invariant(0 <= i && i <= 3)
    cv::decreases(3 - i)
  {
    if (slots[i].key == k)
      return i;
  }
  return -1;
}
// CHECK-DAG: Verified: find_key

void set_diagonal()
  cv::modifies(grid)
  cv::post(grid[0][0] == 1 && grid[1][1] == 1 && grid[2][2] == 1)
{
  grid[0][0] = 1;
  grid[1][1] = 1;
  grid[2][2] = 1;
}
// CHECK-DAG: Verified: set_diagonal

int grid_row_past(int j)
  cv::pre(0 <= j && j <= 3)
{
  return grid[1][j];
}
// CHECK-DAG: error: verification failed: grid_row_past [bounds]

// A global may hold a pointer it is given; a pointer to storage whose
// lifetime the verifier tracks may not leave it.
struct Holder {
  int *p;
};
Holder holder;

void keep(int *q)
  cv::modifies(holder.p)
  cv::post(holder.p == q)
{
  holder.p = q;
}
// CHECK-DAG: Verified: keep

void keep_dynamic()
  cv::modifies(holder.p)
{
  int *q = new int(1);
  holder.p = q;
}
// CHECK-DAG: error: keep_dynamic: copying a dynamic-storage pointer is unsupported

// Specs and ghost code do not touch global objects.
cv::spec int mode_spec() { return config.mode; }
// CHECK-DAG: error: mode_spec: a spec function cannot read the mutable global config; pass its value as a parameter

void ghost_store()
  cv::post(true)
{
  cv::ghost {
    history[0] = 1;
  }
}
// CHECK-DAG: error: ghost_store: ghost code cannot modify executable state

// Unsupported, located: a whole-object read.
struct Pair {
  int a;
  int b;
};
Pair pair;

int first_of(Pair p)
  cv::post(cv::result == p.a)
{
  return p.a;
}

int copy_pair()
  cv::post(true)
{
  return first_of(pair);
}
// CHECK-DAG: error: copy_pair: the global pair read as a whole record or array is unsupported; read its fields or elements

struct Positive {
  int v;
  cv::type_invariant(v > 0);
};
Positive positive;

int read_positive()
  cv::post(true)
{
  return positive.v;
}
// CHECK-DAG: error: read_positive: the global positive holds a class with an invariant, which a global object does not maintain
