// RUN: %clang -std=c++17 -fverify-contracts -fsyntax-only %s
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=1 %s 2>&1 | FileCheck %s --check-prefix=VCR
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=2 %s 2>&1 | FileCheck %s --check-prefix=PASSIVE
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=3 %s 2>&1 | FileCheck %s --check-prefix=VC
// RUN: %cpp-verify --check-ub --lower-only --dump-ir=4 %s 2>&1 | FileCheck %s --check-prefix=Z3

spec bool valid(int *p, int count) { return true; }

int read_one(int *p, int count)
  pre(valid(p, count) && count >= 1)
  post(result == p[0])
{
  return p[0];
}

int slice_call_ir(int *p, int count, int offset, int length)
  pre(valid(p, count) && count >= 0 && count <= 1000 && offset >= 0 &&
      offset <= count && length >= 1 && length <= count - offset)
  post(result == p[offset])
{
  return read_one(p + offset, length);
}

long slice_difference_ir(int *p, int count, int left, int right)
  pre(valid(p, count) && p != nullptr && count >= 0 && count <= 1000 &&
      left >= 0 && left <= count && right >= 0 && right <= count)
  post(result == left - right)
{
  return (p + left) - (p + right);
}

// VCR-LABEL: fn slice_call_ir
// VCR: valid_extent p stride 4
// VCR-NEXT: count
// VCR: call read_one
// VCR-NEXT: +
// VCR-NEXT: p
// VCR-NEXT: *
// VCR-NEXT: cast
// VCR-NEXT: offset
// VCR-NEXT: 4
// VCR-NEXT: length
// VCR-LABEL: fn slice_difference_ir
// VCR: valid_extent p stride 4
// VCR-NEXT: count
// VCR: return
// VCR-NEXT: cast
// VCR-NEXT: /
// VCR-NEXT: -
// VCR-NEXT: +
// VCR-NEXT: p
// VCR-NEXT: *
// VCR-NEXT: cast
// VCR-NEXT: left

// PASSIVE-LABEL: passive slice_call_ir
// PASSIVE: assert
// PASSIVE: false
// PASSIVE: >=
// PASSIVE-NEXT: offset_0
// PASSIVE-NEXT: 0
// PASSIVE-NEXT: <=
// PASSIVE-NEXT: offset_0
// PASSIVE-NEXT: count_0
// PASSIVE-NEXT: >=
// PASSIVE-NEXT: length_0
// PASSIVE-NEXT: 0
// PASSIVE-NEXT: <=
// PASSIVE-NEXT: length_0
// PASSIVE-NEXT: -
// PASSIVE-NEXT: count_0
// PASSIVE-NEXT: offset_0
// PASSIVE: assume
// PASSIVE: __return_call_1_1
// PASSIVE: load
// PASSIVE-LABEL: passive slice_difference_ir
// PASSIVE: assert
// PASSIVE: <=
// PASSIVE-NEXT: left_0
// PASSIVE-NEXT: count_0
// PASSIVE: __result_1
// PASSIVE: cast
// PASSIVE-NEXT: left_0
// PASSIVE: cast
// PASSIVE-NEXT: right_0
// PASSIVE-NOT: /

// VC-LABEL: vc slice_call_ir
// VC: features mathematical-integers, bit-vectors, pointers, heap-arrays
// VC: 1000 : bitvector32
// VC-NEXT: >= : bool
// VC-NEXT: offset_0 : bitvector32
// VC-NEXT: 0 : bitvector32
// VC-NEXT: <= : bool
// VC-NEXT: offset_0 : bitvector32
// VC-NEXT: count_0 : bitvector32
// VC-NEXT: >= : bool
// VC-NEXT: length_0 : bitvector32
// VC-NEXT: 1 : bitvector32
// VC-NEXT: <= : bool
// VC-NEXT: length_0 : bitvector32
// VC-NEXT: - : bitvector32
// VC-NEXT: count_0 : bitvector32
// VC-NEXT: offset_0 : bitvector32
// VC: bv_to_int
// VC: obligations
// VC-LABEL: vc slice_difference_ir
// VC: bitvector64
// VC: obligations
// VC: __result_1 : bitvector64
// VC-NEXT: - : bitvector64
// VC-NEXT: bv_resize : bitvector64
// VC-NEXT: left_0 : bitvector32
// VC-NEXT: bv_resize : bitvector64
// VC-NEXT: right_0 : bitvector32
// VC-NOT: / :

// Z3: (bvsge offset_0 #x00000000)
// Z3-NEXT: (bvsle offset_0 count_0)
// Z3: (bvsge length_0 #x00000000)
// Z3-NEXT: (bvsle length_0 (bvsub count_0 offset_0))
// Z3: sign_extend
// Z3: bvsub
// Z3: Lowered: slice_call_ir
// Z3: Lowered: slice_difference_ir
