#include "watch.hpp"
#include "constraint.hpp"
#include "test.hpp"

#include <vector>

using namespace miniqu;

int main () {
  Arena arena (16);
  const Lit a = mk_lit (0), b = mk_lit (1), c = mk_lit (2);
  const Lit pair[2] = {a, b};
  std::vector<Ref> refs;
  for (uint64_t i = 0; i < 6; i++)
    refs.push_back (alloc_constraint (arena, pair, Kind::Clause, false, i));

  Watches watches;
  watches.init (3);
  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (Ref r : refs)
      watches (kind, c).push_back (Watch{r, a});
  CHECK (watches (Kind::Clause, ~c).empty ());
  CHECK_EQ (watches (Kind::Clause, c).size (), 6u);

  // Without smudging, lookup returns the list as it is.
  deref (arena, refs[1]).set_garbage (true);
  CHECK_EQ (watches.lookup (Kind::Clause, c, arena).size (), 6u);

  // Smudging (twice, harmlessly) makes lookup drop garbage entries, in one
  // kind only and keeping the order of the rest.
  watches.smudge (Kind::Clause, c);
  watches.smudge (Kind::Clause, c);
  const std::vector<Watch> &cleaned =
      watches.lookup (Kind::Clause, c, arena);
  CHECK_EQ (cleaned.size (), 5u);
  CHECK (cleaned[0].ref == refs[0] && cleaned[1].ref == refs[2]);
  CHECK (cleaned[0].blocker == a);
  CHECK_EQ (watches (Kind::Cube, c).size (), 6u);

  // clean_all handles every dirty list, also after an early lookup.
  deref (arena, refs[0]).set_garbage (true);
  deref (arena, refs[5]).set_garbage (true);
  watches.smudge (Kind::Clause, c);
  watches.smudge (Kind::Cube, c);
  watches.smudge (Kind::Cube, ~c);
  watches.clean_all (arena);
  CHECK_EQ (watches (Kind::Clause, c).size (), 3u);
  CHECK_EQ (watches (Kind::Cube, c).size (), 3u);
  for (const Watch &w : watches (Kind::Cube, c))
    CHECK (!deref (arena, w.ref).garbage ());

  // A list that was not smudged keeps its garbage, as documented.
  deref (arena, refs[2]).set_garbage (true);
  watches.clean_all (arena);
  CHECK_EQ (watches (Kind::Clause, c).size (), 3u);

  watches.clear_all ();
  CHECK (watches (Kind::Clause, c).empty ());
  CHECK (watches (Kind::Cube, c).empty ());
  // The dirty flags are gone too: a new entry is not cleaned unasked.
  watches (Kind::Clause, c).push_back (Watch{refs[1], a});
  CHECK_EQ (watches.lookup (Kind::Clause, c, arena).size (), 1u);

  return test_result ();
}
