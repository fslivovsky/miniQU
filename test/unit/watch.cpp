#include "watch.hpp"
#include "constraint.hpp"
#include "test.hpp"

#include <utility>
#include <vector>

using namespace miniqu;

static_assert (sizeof (WatchList) == 16);
static_assert (alignof (WatchList) == 8);
static_assert (std::is_nothrow_move_constructible_v<WatchList>);
static_assert (std::is_nothrow_move_assignable_v<WatchList>);
static_assert (!std::is_copy_constructible_v<WatchList>);

static Watch mk_watch (uint32_t i) {
  return Watch{static_cast<Ref> (i), mk_lit (i)};
}

static bool holds (const WatchList &list, std::vector<uint32_t> expected) {
  if (list.size () != expected.size ())
    return false;
  size_t k = 0;
  for (const Watch &w : list)
    if (w.ref != static_cast<Ref> (expected[k++]))
      return false;
  return true;
}

// Capacities from empty follow 'capacity + capacity / 2 + 2', as MiniSat.
static void test_growth () {
  WatchList list;
  CHECK (list.empty ());
  CHECK_EQ (list.capacity (), 0u);
  CHECK (list.begin () == list.end ());
  size_t expected = 0;
  for (uint32_t i = 0; i < 1000; i++) {
    if (list.size () == expected)
      expected += expected / 2 + 2;
    list.push (mk_watch (i));
    CHECK_EQ (list.capacity (), expected);
  }
  CHECK_EQ (list.size (), 1000u);
  WatchList small;
  std::vector<size_t> seen;
  for (uint32_t i = 0; i < 25; i++) {
    small.push (mk_watch (i));
    if (seen.empty () || seen.back () != small.capacity ())
      seen.push_back (small.capacity ());
  }
  CHECK ((seen == std::vector<size_t>{2, 5, 9, 15, 24, 38}));
  uint32_t i = 0;
  bool in_order = true;
  for (const Watch &w : list) {
    in_order &= w.ref == static_cast<Ref> (i) && w.blocker == mk_lit (i);
    i++;
  }
  CHECK (in_order);
}

static void test_erase_and_clear () {
  WatchList list;
  for (uint32_t i = 0; i < 6; i++)
    list.push (mk_watch (i));
  list.erase (list.begin () + 2); // single, keeps the order
  CHECK (holds (list, {0, 1, 3, 4, 5}));
  list.erase (list.end () - 1);
  CHECK (holds (list, {0, 1, 3, 4}));
  list.truncate (list.begin () + 3); // suffix
  CHECK (holds (list, {0, 1, 3}));
  list.truncate (list.end ());
  CHECK (holds (list, {0, 1, 3}));
  const size_t capacity = list.capacity ();
  list.clear ();
  CHECK (list.empty ());
  CHECK_EQ (list.capacity (), capacity);
  list.push (mk_watch (7));
  CHECK (holds (list, {7}));
}

// Under the sanitizers a leak or a double free fails the test.
static void test_move () {
  WatchList a;
  for (uint32_t i = 0; i < 3; i++)
    a.push (mk_watch (i));
  WatchList b (std::move (a));
  CHECK (a.empty () && a.capacity () == 0 && a.begin () == nullptr);
  CHECK (holds (b, {0, 1, 2}));
  WatchList c;
  c.push (mk_watch (9)); // freed by the assignment
  c = std::move (b);
  CHECK (b.empty () && b.capacity () == 0);
  CHECK (holds (c, {0, 1, 2}));
  WatchList &self = c;
  c = std::move (self);
  CHECK (holds (c, {0, 1, 2}));
  a.push (mk_watch (4)); // a moved-from list is usable
  CHECK (holds (a, {4}));
}

static void test_watches () {
  Arena arena (16);
  const Lit a = mk_lit (0), b = mk_lit (1), c = mk_lit (2);
  const Lit pair[2] = {a, b};
  std::vector<Ref> refs;
  for (uint64_t i = 0; i < 6; i++)
    refs.push_back (alloc_constraint (arena, pair, Kind::Clause, false, i));

  Watches watches;
  watches.resize (3);
  CHECK_EQ (watches.size (), 3u);
  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (Ref r : refs)
      watches (kind, c).push (Watch{r, a});
  CHECK (watches (Kind::Clause, ~c).empty ());
  CHECK_EQ (watches (Kind::Clause, c).size (), 6u);

  // Resizing moves the records and keeps the lists and the flags.
  watches.smudge (Kind::Cube, ~c);
  watches.resize (1000);
  CHECK_EQ (watches.size (), 1000u);
  CHECK_EQ (watches (Kind::Clause, c).size (), 6u);
  CHECK (watches (Kind::Cube, c).begin ()->ref == refs[0]);
  CHECK (watches.dirty (Kind::Cube, ~c));
  CHECK (!watches.dirty (Kind::Clause, ~c));
  CHECK (watches (Kind::Clause, mk_lit (999)).empty ());
  CHECK (!watches.dirty (Kind::Cube, mk_lit (999)));

  // Without smudging, lookup returns the list as it is.
  deref (arena, refs[1]).set_garbage (true);
  CHECK_EQ (watches.lookup (Kind::Clause, c, arena).size (), 6u);

  // Smudging (twice, harmlessly) makes lookup drop garbage entries, in one
  // kind only and keeping the order of the rest.
  watches.smudge (Kind::Clause, c);
  watches.smudge (Kind::Clause, c);
  CHECK (watches.dirty (Kind::Clause, c));
  CHECK (!watches.dirty (Kind::Cube, c));
  const WatchList &cleaned = watches.lookup (Kind::Clause, c, arena);
  CHECK (!watches.dirty (Kind::Clause, c));
  CHECK_EQ (cleaned.size (), 5u);
  CHECK (cleaned.begin ()[0].ref == refs[0] &&
         cleaned.begin ()[1].ref == refs[2]);
  CHECK (cleaned.begin ()[0].blocker == a);
  CHECK_EQ (watches (Kind::Cube, c).size (), 6u);

  // clean_all handles every dirty list, also after an early lookup.
  deref (arena, refs[0]).set_garbage (true);
  deref (arena, refs[5]).set_garbage (true);
  watches.smudge (Kind::Clause, c);
  watches.smudge (Kind::Cube, c);
  watches.clean_all (arena);
  for (Lit p : {c, ~c})
    for (Kind kind : {Kind::Clause, Kind::Cube})
      CHECK (!watches.dirty (kind, p));
  CHECK_EQ (watches (Kind::Clause, c).size (), 3u);
  CHECK_EQ (watches (Kind::Cube, c).size (), 3u);
  for (const Watch &w : watches (Kind::Cube, c))
    CHECK (!deref (arena, w.ref).garbage ());

  // A list that was not smudged keeps its garbage, as documented.
  deref (arena, refs[2]).set_garbage (true);
  watches.clean_all (arena);
  CHECK_EQ (watches (Kind::Clause, c).size (), 3u);

  // clean_every_list does not need the flags, and clears them.
  watches.smudge (Kind::Clause, a);
  watches.clean_every_list (arena);
  CHECK_EQ (watches (Kind::Clause, c).size (), 2u);
  CHECK_EQ (watches (Kind::Cube, c).size (), 2u);
  CHECK (!watches.dirty (Kind::Clause, a));

  watches.smudge (Kind::Cube, b);
  watches.clear_all ();
  CHECK (watches (Kind::Clause, c).empty ());
  CHECK (watches (Kind::Cube, c).empty ());
  CHECK (!watches.dirty (Kind::Cube, b));
  // The dirty flags are gone too: a new entry is not cleaned unasked.
  watches (Kind::Clause, c).push (Watch{refs[1], a});
  CHECK_EQ (watches.lookup (Kind::Clause, c, arena).size (), 1u);
  // And so is the list of dirty literals: clean_all does not clean it.
  watches.clean_all (arena);
  CHECK_EQ (watches (Kind::Clause, c).size (), 1u);
}

int main () {
  test_growth ();
  test_erase_and_clear ();
  test_move ();
  test_watches ();
  return test_result ();
}
