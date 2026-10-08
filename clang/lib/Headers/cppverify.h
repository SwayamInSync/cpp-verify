/*===---- cppverify.h - CppVerify constructs and collections ---------------===
 *
 * Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
 * See https://llvm.org/LICENSE.txt for license information.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 *===-----------------------------------------------------------------------===
 */

/* The namespace cppverify. With -fverify-contracts every C++ translation unit
 * includes this header implicitly.
 *
 * Contract constructs are compiler syntax written qualified,
 * cppverify::pre(...) or through an alias (namespace cv = cppverify;). The
 * declarations below document them for editors; any other use of one is an
 * error.
 *
 * Verification-only declarations: the valid extent marker and collections
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

/// Precondition, after a function's parameter list:
/// `int f(int x) cppverify::pre(x > 0)`. Every caller must establish it, and
/// the body may assume it.
void pre(bool condition) = delete;

/// Postcondition, after a function's parameter list. The body establishes it
/// at every return and callers may assume it; cppverify::result is the
/// return value and cppverify::old(e) the value of e at entry.
void post(bool condition) = delete;

/// The memory a function or loop may write: cells (`*p`, `p->f`, `p[i]`, a
/// reference), ranges `p[lo : n]`, and objects `*p`. Everything else keeps
/// its value.
void modifies(...) = delete;

/// Lets two pointer or reference parameters address the same object;
/// otherwise mutable ones are assumed not to.
void aliases(...) = delete;

/// Soft precondition of a spec function: not checked at calls, but reported
/// as a warning when a caller fails to verify.
void recommends(bool condition) = delete;

/// The cells p[0] to p[n - 1] a spec function's value depends on, checked
/// against its body.
void reads(...) = delete;

/// The domain on which a spec function's body defines it; elsewhere its
/// value is unspecified.
void when(bool condition) = delete;

/// Termination measure of a recursive function or a loop: a tuple, ordered
/// lexicographically, that every recursive call or iteration lowers.
/// cppverify::decreases(*) lets an executable function or loop diverge.
void decreases(...) = delete;

/// Starts a case of the contract, `cppverify::behavior(name, assumes)`: the
/// pre and post clauses after it apply where assumes holds.
void behavior(...) = delete;

/// Loop invariant, between a loop's head and its body: it holds on entry and
/// after every iteration.
void invariant(bool condition) = delete;

/// Class invariant, in a class body after the fields it names: it holds for
/// every object of the class.
void type_invariant(bool condition) = delete;

/// Proof obligation at this point, assumed afterwards:
/// `cppverify::check(e);`, or with a local proof
/// `cppverify::check(e) by { ... }`.
void check(bool condition) = delete;

/// Unfolds the recursive spec function f up to n levels in this function:
/// `cppverify::reveal_with_fuel(f, n);`.
void reveal_with_fuel(...) = delete;

/// Withholds the definition of spec function f from the proofs in this
/// function.
void hide(...) = delete;

/// Gives the proofs in this function the definition of spec function f.
void reveal(...) = delete;

/// Universal quantifier: `cppverify::forall(k, lo, hi, body)` over
/// lo <= k < hi, or `cppverify::forall(k, body)` over all integers; k is a
/// fresh mathematical integer.
bool forall(...) = delete;

/// Existential quantifier: `cppverify::exists(k, lo, hi, body)` over
/// lo <= k < hi, or `cppverify::exists(k, body)` over all integers.
bool exists(...) = delete;

/// Some integer for which the body holds, an unspecified one if none does:
/// `cppverify::choose(k, body)` or `cppverify::choose(k, lo, hi, body)`.
long long choose(...) = delete;

/// The value of an expression at function entry, in postconditions and loop
/// invariants: `cppverify::old(*p)`.
void old(...) = delete;

/// Marks a term of a quantifier body as the pattern that instantiates the
/// quantifier: `cppverify::forall(k, cppverify::trigger(a[k]) > 0)`.
void trigger(...) = delete;

enum __construct {
  /// The return value, in postconditions.
  result __attribute__((unavailable("cppverify::result is the return value "
                                    "in a postcondition"))),
  /// After a spec function returning bool: the least predicate its body
  /// defines, true exactly where a finite derivation shows it.
  inductive __attribute__((unavailable("cppverify::inductive follows a spec "
                                       "function's parameter list"))),
  /// After the behaviors: every input the preconditions admit is in some
  /// behavior (or in one of those named in parentheses).
  complete_behaviors __attribute__((unavailable(
      "cppverify::complete_behaviors follows a function's behaviors"))),
  /// After the behaviors: no input is in two of them (or of those named).
  disjoint_behaviors __attribute__((unavailable(
      "cppverify::disjoint_behaviors follows a function's behaviors"))),
  /// Declares a spec function, a mathematical definition for contracts and
  /// proofs that is never compiled: `cppverify::spec int sq(int x)`.
  spec __attribute__((unavailable("cppverify::spec starts a declaration"))),
  /// Declares a proof function, a lemma proved from its body that is never
  /// compiled: `cppverify::proof void lemma(int n)`.
  proof __attribute__((unavailable("cppverify::proof starts a declaration"))),
  /// Ghost code, for proofs only and never compiled: a block
  /// `cppverify::ghost { ... }` or a variable `cppverify::ghost T x = e;`.
  ghost __attribute__((unavailable("cppverify::ghost starts a statement"))),
  /// A chain of proved steps: `cppverify::calc { e0; == { proof } e1; }`.
  calc __attribute__((unavailable("cppverify::calc starts a statement"))),
};

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
  /// The elements in reverse order.
  seq reverse() const;
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

/// A set of integers, possibly infinite.
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

/// A multiset of integers.
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

/// A map from integers to integers.
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
