// RUN: %clang_cc1 -std=c++17 -fverify-contracts -fsyntax-only %s
//
// libc++ uses names like std::codecvt::result. old/result must stay lexer
// identifiers; this test embeds the same pattern without needing <iostream>.

namespace std_like {
struct codecvt_base {
  enum result { ok, partial, error, noconv };
};
struct codecvt : codecvt_base {
  result do_in() { return ok; }
};
} // namespace std_like

int abs_val(int x)
  pre(true)
  post(result >= 0)
{
  return x < 0 ? -x : x;
}