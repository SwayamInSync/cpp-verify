// Under a small resource limit Z3 proves only the trivial return check.
proof void bump(int x)
  pre(0 <= x && x <= 100)
  post(x + 1 > x)
{
}
