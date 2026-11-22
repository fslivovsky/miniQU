#include "constraint.hpp"
#include "test.hpp"

#include <vector>

using namespace miniqu;

static std::vector<Lit> lits_of (std::initializer_list<int> dimacs) {
  std::vector<Lit> result;
  for (int d : dimacs)
    result.push_back (mk_lit ((Var) (d < 0 ? -d : d) - 1, d < 0));
  return result;
}

int main () {
  static_assert (sizeof (Constraint) == 16);
  static_assert (Constraint::words (3) == 7);

  Arena arena (16);
  const std::vector<Lit> ls = lits_of ({1, -2, 3});
  const uint64_t big = 0x123456789abcdef0ull;
  const Ref r = alloc_constraint (arena, ls, Kind::Cube, true, big);
  CHECK_EQ (arena.size (), 7u);

  Constraint &c = deref (arena, r);
  CHECK_EQ (c.size (), 3u);
  CHECK (c.kind () == Kind::Cube);
  CHECK (c.redundant ());
  CHECK (!c.garbage ());
  CHECK (!c.moved ());
  CHECK (!c.reason ());
  CHECK_EQ (c.glue (), 0u);
  CHECK_EQ (c.id (), big);
  CHECK_EQ (c.lits ().size (), 3u);
  for (uint32_t i = 0; i < 3; i++)
    CHECK (c[i] == ls[i]);
  CHECK_EQ (c.end () - c.begin (), 3);

  // Every flag is independent of the others and of the glue.
  c.set_glue (77);
  c.set_garbage (true);
  c.set_reason (true);
  CHECK (c.garbage () && c.reason () && c.redundant ());
  CHECK (c.kind () == Kind::Cube);
  CHECK_EQ (c.glue (), 77u);
  c.set_garbage (false);
  c.set_redundant (false);
  CHECK (!c.garbage () && c.reason () && !c.redundant ());
  CHECK_EQ (c.glue (), 77u);

  // Glue saturates at 2^20 - 1.
  c.set_glue (1u << 20);
  CHECK_EQ (c.glue (), (1u << 20) - 1);
  c.set_glue (UINT32_MAX);
  CHECK_EQ (c.glue (), (1u << 20) - 1);
  CHECK (c.reason () && c.kind () == Kind::Cube);
  c.set_glue (0);
  CHECK_EQ (c.glue (), 0u);

  // Ids use both words.
  const Ref r2 = alloc_constraint (arena, lits_of ({-4}), Kind::Clause,
                                   false, UINT64_MAX);
  CHECK_EQ (deref (arena, r2).id (), UINT64_MAX);
  CHECK (deref (arena, r2).kind () == Kind::Clause);
  CHECK_EQ (deref (arena, r).id (), big);

  // Shrinking reports the freed words.
  CHECK_EQ (deref (arena, r).shrink (2), 1u);
  CHECK_EQ (deref (arena, r).size (), 2u);

  // Relocation into a second arena through forwarding.
  Arena to (16);
  const Ref copy =
      alloc_constraint (to, deref (arena, r).lits (), Kind::Cube, true,
                        deref (arena, r).id ());
  deref (arena, r).forward (copy);
  CHECK (deref (arena, r).moved ());
  CHECK (deref (arena, r).forwarded () == copy);
  CHECK_EQ (deref (to, copy).size (), 2u);
  CHECK (deref (to, copy)[0] == ls[0] && deref (to, copy)[1] == ls[1]);
  CHECK_EQ (deref (to, copy).id (), big);
  CHECK (!deref (to, copy).moved ());

  // Neighbours are untouched by the forwarding.
  CHECK (deref (arena, r2).lits ()[0] == lits_of ({-4})[0]);

  return test_result ();
}
