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

static bool same_lits (const Constraint &c, const std::vector<Lit> &ls) {
  return std::vector<Lit> (c.begin (), c.end ()) == ls;
}

// One header word; a glue word only if redundant, two id words only with
// an id.
static void test_words () {
  static_assert (sizeof (Constraint) == 4);
  static_assert (Constraint::words (3, false, false) == 4);
  static_assert (Constraint::words (3, true, false) == 5);
  static_assert (Constraint::words (3, false, true) == 6);
  static_assert (Constraint::words (3, true, true) == 7);

  Arena arena (16);
  const std::vector<Lit> ls = lits_of ({1, -2, 3});
  uint32_t expected = 0;
  for (bool redundant : {false, true})
    for (bool has_id : {false, true}) {
      const Ref r = alloc_constraint (arena, ls, Kind::Clause, redundant,
                                      has_id ? std::optional<uint64_t> (7)
                                             : std::nullopt);
      const Constraint &c = deref (arena, r);
      expected += Constraint::words (3, redundant, has_id);
      CHECK_EQ (arena.size (), expected);
      CHECK_EQ (c.words (), Constraint::words (3, redundant, has_id));
      CHECK_EQ (c.redundant (), redundant);
      CHECK_EQ (c.has_id (), has_id);
      CHECK_EQ (c.glue (), 0u);
      CHECK (same_lits (c, ls));
      if (has_id)
        CHECK_EQ (c.id (), 7u);
    }
}

// A redundant cube with id: flags, glue and id are independent, and glue
// and id survive shrinking.
static void test_redundant_with_id () {
  Arena arena (16);
  const std::vector<Lit> ls = lits_of ({1, -2, 3, -4});
  const uint64_t big = 0xfedcba9876543210ull;
  const Ref r = alloc_constraint (arena, ls, Kind::Cube, true, big);
  Constraint &c = deref (arena, r);
  CHECK_EQ (c.size (), 4u);
  CHECK (c.kind () == Kind::Cube);
  CHECK (c.redundant () && c.has_id ());
  CHECK (!c.garbage () && !c.moved () && !c.reason ());
  CHECK_EQ (c.glue (), 0u);
  CHECK_EQ (c.id (), big);
  CHECK_EQ (c.lits ().size (), 4u);
  CHECK_EQ (c.end () - c.begin (), 4);

  c.set_glue (77);
  c.set_garbage (true);
  c.set_reason (true);
  CHECK (c.garbage () && c.reason () && c.redundant () && c.has_id ());
  CHECK (c.kind () == Kind::Cube);
  CHECK_EQ (c.glue (), 77u);
  CHECK_EQ (c.id (), big);
  c.set_garbage (false);
  c.set_reason (false);

  // Glue saturates, and neither glue nor id disturbs the other.
  c.set_glue (Constraint::glue_max + 1);
  CHECK_EQ (c.glue (), Constraint::glue_max);
  c.set_glue (UINT32_MAX);
  CHECK_EQ (c.glue (), Constraint::glue_max);
  CHECK_EQ (c.id (), big);
  c.set_id (UINT64_MAX);
  CHECK_EQ (c.glue (), Constraint::glue_max);
  CHECK_EQ (c.id (), UINT64_MAX);
  c.set_glue (0);
  CHECK_EQ (c.id (), UINT64_MAX);
  c.set_id (big);
  c.set_glue (12);

  // Glue and used are independent; saturation of the glue does not spill
  // into used.
  CHECK_EQ (c.used (), 0u);
  c.set_used (2);
  CHECK_EQ (c.used (), 2u);
  CHECK_EQ (c.glue (), 12u);
  c.set_glue (UINT32_MAX);
  CHECK_EQ (c.glue (), Constraint::glue_max);
  CHECK_EQ (c.used (), 2u);
  c.set_glue (12);
  c.set_used (1);
  CHECK_EQ (c.glue (), 12u);
  CHECK_EQ (c.used (), 1u);
  c.set_used (2);
  CHECK_EQ (c.id (), big);

  // Shrinking moves glue, used and id behind the new last literal.
  CHECK_EQ (c.shrink (2), 2u);
  CHECK_EQ (c.size (), 2u);
  CHECK_EQ (c.words (), Constraint::words (2, true, true));
  CHECK (same_lits (c, lits_of ({1, -2})));
  CHECK_EQ (c.glue (), 12u);
  CHECK_EQ (c.used (), 2u);
  CHECK_EQ (c.id (), big);
  CHECK (c.redundant () && c.has_id () && c.kind () == Kind::Cube);
}

static void test_irredundant_without_id () {
  Arena arena (16);
  const std::vector<Lit> ls = lits_of ({2, 5, -6});
  const Ref r = alloc_constraint (arena, ls, Kind::Clause, false, {});
  Constraint &c = deref (arena, r);
  CHECK (!c.redundant () && !c.has_id ());
  CHECK_EQ (c.glue (), 0u);
  CHECK_EQ (c.used (), 0u);
  CHECK (!c.vivified ());
  CHECK_EQ (c.words (), 1u + 3u);
  CHECK_EQ (c.shrink (1), 2u);
  CHECK_EQ (c.words (), 2u);
  CHECK (same_lits (c, lits_of ({2})));
}

// The vivified bit of a learnt constraint: independent of glue, used and
// id, and kept by 'shrink' and by a word-by-word copy.
static void test_vivified () {
  Arena arena (16);
  const std::vector<Lit> ls = lits_of ({1, -2, 3, -4, 5});
  const Ref r = alloc_constraint (arena, ls, Kind::Clause, true, 99);
  Constraint &c = deref (arena, r);
  CHECK (!c.vivified ());
  c.set_glue (Constraint::glue_max);
  c.set_used (2);
  c.set_vivified (true);
  CHECK (c.vivified ());
  CHECK_EQ (c.glue (), Constraint::glue_max);
  CHECK_EQ (c.used (), 2u);
  CHECK_EQ (c.id (), 99u);
  c.set_glue (UINT32_MAX);
  c.set_used (0);
  c.set_glue (3);
  CHECK (c.vivified ());
  CHECK_EQ (c.glue (), 3u);
  CHECK_EQ (c.used (), 0u);
  CHECK_EQ (c.shrink (3), 2u);
  CHECK (c.vivified ());
  CHECK_EQ (c.glue (), 3u);
  CHECK_EQ (c.id (), 99u);
  Arena other (16);
  const Ref copy = copy_constraint (other, c);
  CHECK (deref (other, copy).vivified ());
  CHECK_EQ (deref (other, copy).glue (), 3u);
  c.set_vivified (false);
  CHECK (!c.vivified ());
  CHECK_EQ (c.glue (), 3u);
  CHECK_EQ (c.used (), 0u);
  CHECK_EQ (c.id (), 99u);
}

// The buffer of 'model.cpp': the id stays valid while the size goes down to
// zero and back up to the allocated size.
static void test_set_size () {
  Arena arena (16);
  const std::vector<Lit> ls = lits_of ({1, 2, 3, 4, 5});
  const uint64_t id = 0x123456789abull;
  const Ref r = alloc_constraint (arena, ls, Kind::Cube, false, id);
  const Ref after = alloc_constraint (arena, ls, Kind::Clause, false, 9);
  Constraint &c = deref (arena, r);
  for (uint32_t n : {3u, 0u, 1u, 5u, 4u}) {
    c.set_size (n);
    CHECK_EQ (c.size (), n);
    CHECK_EQ (c.id (), id);
    for (uint32_t i = 0; i < n; i++)
      c[i] = ls[4 - i];
    CHECK_EQ (c.id (), id);
  }
  c.set_size (5);
  c.set_id (id + 1);
  CHECK_EQ (c.id (), id + 1);
  // The neighbour is untouched.
  CHECK (same_lits (deref (arena, after), ls));
  CHECK_EQ (deref (arena, after).id (), 9u);
}

// Garbage collection copies verbatim and forwards the old constraint.
static void test_copy_and_forward () {
  Arena arena (16);
  const std::vector<Lit> ls = lits_of ({-1, 2, 3});
  const Ref r = alloc_constraint (arena, ls, Kind::Cube, true, 42);
  const Ref neighbour =
      alloc_constraint (arena, lits_of ({-4}), Kind::Clause, false, 43);
  deref (arena, r).set_glue (5);
  deref (arena, r).set_used (1);

  Arena to (16);
  const Ref filler = alloc_constraint (to, ls, Kind::Clause, false, {});
  const Ref copy = copy_constraint (to, deref (arena, r));
  CHECK (copy != filler);
  const Constraint &c = deref (to, copy);
  CHECK (c.kind () == Kind::Cube);
  CHECK (c.redundant () && c.has_id ());
  CHECK (!c.moved () && !c.garbage ());
  CHECK_EQ (c.size (), 3u);
  CHECK (same_lits (c, ls));
  CHECK_EQ (c.glue (), 5u);
  CHECK_EQ (c.used (), 1u);
  CHECK_EQ (c.id (), 42u);
  CHECK_EQ (to.size (), Constraint::words (3, false, false) +
                            Constraint::words (3, true, true));

  deref (arena, r).forward (copy);
  CHECK (deref (arena, r).moved ());
  CHECK (deref (arena, r).forwarded () == copy);
  // Neighbours are untouched by the forwarding.
  CHECK (same_lits (deref (arena, neighbour), lits_of ({-4})));
  CHECK_EQ (deref (arena, neighbour).id (), 43u);
}

int main () {
  test_words ();
  test_redundant_with_id ();
  test_irredundant_without_id ();
  test_vivified ();
  test_set_size ();
  test_copy_and_forward ();
  return test_result ();
}
