// Arena garbage collection ordered by access (ARCHITECTURE 5.3; MiniSat's
// 'relocAll' and 'garbageCollect').
//
// Deleting a constraint only marks it and counts its words as wasted
// ('mark_garbage').  Memory is reclaimed here by copying the live
// constraints into a fresh arena, in the order in which propagation will
// read them: constraint by constraint along the watch lists of the
// variables in index order.  The first walk over a watch list after a
// collection then touches consecutive memory.  Whatever the watches did not
// reach (reasons, unit constraints, constraints of the reference lists
// that no watch list holds) is copied after them.
//
// The collector runs only at safe points (after 'reduce'): no 'Ref' may be
// held in a local variable, a conflict in flight or an analysis buffer.
// Blockers are literals and stay valid.  A stale watch of mode 2
// (propagate_ldq.cpp) is relocated like any other: it refers to a live
// constraint, which is copied once and forwarded.  The buffer of
// 'model.cpp' is allocated afresh; its contents are dead between two
// initial cubes.
//
// Not a QBF technique: no side conditions, no proof steps (every deletion
// was logged when it was marked).

#include "contract.hpp"
#include "internal.hpp"

#include <cassert>

namespace miniqu {

bool Internal::collecting () const {
  // With 'gcfrac == 0' every safe point collects, even if nothing was
  // deleted, so that relocation runs on small instances.
  return opts.gcfrac == 0 || (uint64_t) arena.wasted () * 100 >
                                 (uint64_t) opts.gcfrac * arena.size ();
}

namespace {

// The constraints copied into 'to', in the order of their first reference.
class Relocator {
  Arena &from;
  Arena &to;
  int64_t copied = 0;

public:
  Relocator (Arena &f, Arena &t) : from (f), to (t) {}

  Ref operator() (Ref old) {
    Constraint &c = deref (from, old);
    if (c.moved ())
      return c.forwarded ();
    const Ref ref = copy_constraint (to, c);
    c.forward (ref);
    copied++;
    return ref;
  }

  int64_t count () const { return copied; }
};

} // namespace

void Internal::garbage_collect () {
  PROFILE_SCOPE (collect);
  assert (lone == lit_undef);
  stats.collections++;
  if (opts.mode == 2)
    watches.clean_every_list (arena);
  else
    watches.clean_all (arena);

  // Everything the arena holds that is not wasted, plus room to avoid a
  // reallocation of the new arena during the copy.
  Arena fresh (arena.size () - arena.wasted ());
  Relocator relocate (arena, fresh);

  // The point of the order: step 2 of ARCHITECTURE 5.3.
  const Var vars = prefix.size ();
  for (Var v = 0; v < vars; v++)
    for (bool negative : {false, true})
      for (Kind kind : {Kind::Clause, Kind::Cube})
        for (Watch &w : watches (kind, mk_lit (v, negative)))
          w.ref = relocate (w.ref);

  for (Lit l : trail) {
    Ref &r = vtab[var (l)].reason;
    if (r != Ref::none)
      r = relocate (r);
  }

  for (Kind kind : {Kind::Clause, Kind::Cube})
    for (auto *lists : {&irredundant, &redundant}) {
      std::vector<Ref> &list = (*lists)[index (kind)];
      size_t kept = 0;
      for (Ref ref : list)
        if (!deref (arena, ref).garbage ())
          list[kept++] = relocate (ref);
      list.resize (kept);
    }

  relocate_model_cube (fresh);
  stats.relocated += relocate.count ();
  LOG ("collected %u of %u words", arena.wasted (), arena.size ());
  fresh.move_to (arena);
  if (assertions_enabled || opts.check)
    check_invariants ();
}

} // namespace miniqu
