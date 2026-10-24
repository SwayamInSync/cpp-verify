// Sequences, sets, multisets, and maps in a Lean project, for
// lean_collections.test.
using cppverify::map;
using cppverify::multiset;
using cppverify::seq;
using cppverify::set;

cppverify::spec int total(seq s)
  cppverify::decreases(s.len())
{
  return s.len() <= 0 ? 0 : total(s.subrange(0, s.len() - 1)) + s[s.len() - 1];
}

cppverify::proof void sequences(seq s, int x)
{
  cppverify::check(s.push(x).len() == s.len() + 1);
  cppverify::check(s.push(x)[s.len()] == x);
  cppverify::check((s + cppverify::seq_of(x)).contains(x));
  cppverify::check(s.subrange(0, s.len()) == s);
}

cppverify::proof void sets(set a, int x, int y)
  cppverify::pre(x != y)
{
  cppverify::check(a.insert(x).remove(y).contains(x));
  cppverify::check(a.subset_of(a.unite(cppverify::set_empty().insert(y))));
}

cppverify::proof void multisets(multiset m, int x)
{
  cppverify::check(m.insert(x).count(x) == m.count(x) + 1);
  cppverify::check(m.insert(x).remove(x) == m);
}

cppverify::proof void maps(map m, int k, int v)
{
  cppverify::check(m.insert(k, v)[k] == v);
  cppverify::check(!m.remove(k).contains(k));
}

cppverify::proof void total_push(seq s, int x)
  cppverify::post(total(s.push(x)) == total(s) + x)
{
}

cppverify::proof void wrong(set a, int x)
{
  cppverify::check(a.remove(x).contains(x) == a.contains(x));
}

cppverify::spec int members(set a, int n)
  cppverify::decreases(n)
{
  return n <= 0 ? 0 : members(a, n - 1) + (a.contains(n) ? 1 : 0);
}

cppverify::proof void no_members(set a)
  cppverify::post(members(a, 0) == 0)
{
}
