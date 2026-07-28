// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: not %cpp-verify %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --lower-only %s 2>&1 | FileCheck %s --check-prefix=VERIFY
// RUN: not %cpp-verify --backend=bmc --unroll=2 %s 2>&1 | FileCheck %s --check-prefix=VERIFY

// Every promoted-object form outside this slice must be rejected explicitly:
// nothing is silently truncated, degraded to a scalar, or left with a second
// (flattened) representation.

struct Pair {
  int first;
  int second;
};

struct Inner {
  int lo;
  int hi;
};

struct Outer {
  Inner inner;
  int tag;
};

struct PointerBox {
  int tag;
  int *pointer;
};

void set_scalar(int &target, int value)
  modifies(target)
  post(target == value)
{
  target = value;
}

// The byte-granular allocation metadata is emitted per target byte, so an
// oversized automatic object is rejected rather than truncated.
int oversized_array()
  post(result == 1)
{
  int big[100];
  big[0] = 1;
  return big[0];
}

struct Wide {
  int values[80];
};

int oversized_record()
  post(result == 1)
{
  Wide wide;
  int &alias = wide.values[0];
  alias = 1;
  return wide.values[0];
}

int loop_local_array()
  post(result == 1)
{
  int iteration = 0;
  while (iteration < 1)
    invariant(iteration >= 0 && iteration <= 1)
    decreases(1 - iteration)
  {
    int a[2] = {1, 2};
    set_scalar(a[0], 1);
    ++iteration;
  }
  return iteration;
}

int loop_local_addressable_record()
  post(result == 1)
{
  int iteration = 0;
  while (iteration < 1)
    invariant(iteration >= 0 && iteration <= 1)
    decreases(1 - iteration)
  {
    Pair value{1, 2};
    set_scalar(value.first, 1);
    ++iteration;
  }
  return iteration;
}

// A constant index outside the declared extent is rejected outright; the
// one-past address is never formed.
int constant_out_of_bounds()
  post(result == 1)
{
  int a[4] = {1, 2, 3, 4};
  int &alias = a[4];
  return alias;
}

int wide_constant_out_of_bounds()
  post(result == 1)
{
  int a[1] = {1};
  return a[((unsigned __int128)1) << 100];
}

int string_literal_array()
  post(result == 1)
{
  char text[4] = "abc";
  char &alias = text[0];
  return alias;
}

int unsupported_copy_source(Pair *source)
  pre(source != nullptr)
  post(result == 1)
{
  Pair value = *source;
  int &alias = value.first;
  return alias;
}

int *return_local_address()
  post(result != nullptr)
{
  int value = 7;
  return &value;
}

int *return_local_array()
  post(result != nullptr)
{
  int values[2] = {1, 2};
  return values;
}

int dereference_escaped_local()
  post(result == 7)
{
  return *return_local_address();
}

int raw_pointer_into_local_array()
  post(result == 5)
{
  int values[4] = {1, 2, 3, 4};
  int *pointer = &values[1];
  *pointer = 5;
  return values[1];
}

int whole_object_pointer_argument()
  post(result == 1)
{
  Pair value{1, 2};
  int &alias = value.first;
  return (&value)->first;
}

int provenance_pointer_field()
  post(result == 9)
{
  int *owner = new int(7);
  PointerBox box{0, owner};
  int &promote = box.tag;
  promote = 1;
  delete owner;
  int *replacement = new int(9);
  if (box.pointer == replacement)
    return *box.pointer;
  int observed = *replacement;
  delete replacement;
  return observed;
}

// A non-promoted record keeps its flattened SSA form, which only exists for
// records made purely of scalar fields.
int flattened_nested_record()
  post(result == 1)
{
  Outer o{{1, 2}, 3};
  return o.inner.lo;
}

// VERIFY-DAG: error: oversized_array: automatic object exceeds the 256-byte byte-addressed object limit: big
// VERIFY-DAG: error: oversized_record: automatic object exceeds the 256-byte byte-addressed object limit: wide
// VERIFY-DAG: error: loop_local_array: addressable local declarations inside loops are unsupported
// VERIFY-DAG: error: loop_local_addressable_record: addressable local declarations inside loops are unsupported
// VERIFY-DAG: error: constant_out_of_bounds: fixed-array index is out of bounds
// VERIFY-DAG: error: wide_constant_out_of_bounds: fixed-array index is out of bounds
// VERIFY-DAG: error: string_literal_array: unsupported aggregate initializer for an automatic object
// VERIFY-DAG: error: unsupported_copy_source: unsupported aggregate initializer for an automatic object
// VERIFY-DAG: error: return_local_address: raw address-of is unsupported until lexical lifetime and escape effects are modeled
// VERIFY-DAG: error: return_local_array: array-to-pointer decay of automatic storage is unsupported until lexical lifetime and escape effects are modeled
// VERIFY-DAG: error: dereference_escaped_local: executable call is unsupported in this expression context: return_local_address
// VERIFY-DAG: error: raw_pointer_into_local_array: raw address-of is unsupported until lexical lifetime and escape effects are modeled
// VERIFY-DAG: error: whole_object_pointer_argument: raw address-of is unsupported until lexical lifetime and escape effects are modeled
// VERIFY-DAG: error: provenance_pointer_field: storing a provenance-bearing pointer in an automatic object is unsupported
// VERIFY-DAG: error: flattened_nested_record: unsupported aggregate local variable: o
// VERIFY-NOT: Verified: oversized_array
// VERIFY-NOT: Verified: constant_out_of_bounds
// VERIFY-NOT: Verified: wide_constant_out_of_bounds
// VERIFY-NOT: Verified: return_local_address
// VERIFY-NOT: Verified: return_local_array
// VERIFY-NOT: Verified: dereference_escaped_local
// VERIFY-NOT: Lowered: oversized_array
