/*===---- cppverify.h - CppVerify specification collections ----------------===
 *
 * Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
 * See https://llvm.org/LICENSE.txt for license information.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 *===-----------------------------------------------------------------------===
 */

/* Verification-only declarations: the valid extent marker and collections
 * of mathematical integers, for contracts, ghost code, and spec and proof
 * functions. They have no runtime representation; executable code cannot
 * use them. Elements, keys, values, indices, lengths, and counts are
 * mathematical: no operation wraps.
 *
 * valid(p, n) in a precondition declares that p points to n objects of its
 * type, p[0] to p[n - 1]: every access through p must then stay in them, and
 * p + i must stay in [0, n]. It must be a top-level && clause of a pre.
 *
 * Every operation is total. A sequence index outside [0, len()) reads 0, and
 * an update there leaves the sequence unchanged; subrange(lo, hi) clamps
 * both bounds into [0, len()). A key outside a map's domain maps to 0.
 * Collections are equal when they have the same elements (sequences in the
 * same order, multisets with the same multiplicities, maps with the same
 * domain and values). */

#ifndef __CPPVERIFY_H
#define __CPPVERIFY_H

#if defined(__cplusplus)

namespace cppverify {

/// p points to n objects: p[0] to p[n - 1].
template <class T> bool valid(const T *p, long long n);

/// A finite sequence.
struct seq {
  long long len() const;
  long long operator[](long long index) const;
  /// This sequence with value appended.
  seq push(long long value) const;
  /// This sequence with the element at index replaced by value.
  seq update(long long index, long long value) const;
  /// The elements at [lo, hi).
  seq subrange(long long lo, long long hi) const;
  /// This sequence followed by other.
  seq operator+(seq other) const;
  bool contains(long long value) const;
  bool operator==(seq other) const;
  bool operator!=(seq other) const;
};
seq seq_empty();
/// The sequence of one element.
seq seq_of(long long value);

/// A finite set.
struct set {
  set insert(long long value) const;
  set remove(long long value) const;
  bool contains(long long value) const;
  set unite(set other) const;
  set intersect(set other) const;
  set difference(set other) const;
  bool subset_of(set other) const;
  bool operator==(set other) const;
  bool operator!=(set other) const;
};
set set_empty();

/// A finite multiset.
struct multiset {
  /// One more occurrence of value.
  multiset insert(long long value) const;
  /// One fewer occurrence of value, if it has any.
  multiset remove(long long value) const;
  long long count(long long value) const;
  bool operator==(multiset other) const;
  bool operator!=(multiset other) const;
};
multiset multiset_empty();

/// A finite map.
struct map {
  map insert(long long key, long long value) const;
  map remove(long long key) const;
  bool contains(long long key) const;
  long long operator[](long long key) const;
  bool operator==(map other) const;
  bool operator!=(map other) const;
};
map map_empty();

} // namespace cppverify

#endif /* __cplusplus */

#endif /* __CPPVERIFY_H */
