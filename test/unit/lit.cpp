#include "lit.hpp"
#include "test.hpp"

using namespace miniqu;

int main () {
  const Lit p = mk_lit (5, false), n = mk_lit (5, true);
  CHECK_EQ (var (p), 5u);
  CHECK_EQ (var (n), 5u);
  CHECK (!sign (p) && sign (n));
  CHECK (~p == n && ~n == p);
  CHECK_EQ (index (p), 10u);
  CHECK_EQ (index (n), 11u);
  CHECK (p < n && mk_lit (4, true) < p);
  CHECK (p != n);
  CHECK (lit_undef != p && lit_undef != n);
  CHECK (primary (Kind::Clause) == Quant::Exists);
  CHECK (primary (Kind::Cube) == Quant::Forall);
  CHECK (other (Kind::Clause) == Kind::Cube);
  CHECK (other (other (Kind::Cube)) == Kind::Cube);
  CHECK (Ref::none == static_cast<Ref> (UINT32_MAX));
  return test_result ();
}
