// Initial cubes from satisfying assignments (ARCHITECTURE 4.5; the old
// 'getInitialTerm').
//
// When every decision variable is assigned and propagation found no
// conflict, the assignment satisfies every irredundant clause.  A hitting
// set of them, one true literal per clause (preferring literals already
// taken, so that the cube stays small), is a cube that implies the
// irredundant clauses G.  After existential reduction (an existential
// literal right of every universal one can go) it is analysed like any
// satisfied cube; analysis then derives a cube with an asserting universal
// literal, or the empty cube (formula true).
//
// QBF side condition: the cube implies the *current* irredundant clauses,
// units included, and nothing more; that this is sound for QDIMACS rests on
// INV-SANDWICH (ARCHITECTURE 11.1).  'check_model_cube' verifies the
// hitting-set property in debug builds and with '--check', the one QDIMACS
// failure no proof checker sees.  For QCIR input INV-COMPLETE makes this
// code unreachable; 'stats.modelcubes' counts every visit so that a visit
// on QCIR input shows up (in M1 it is allowed without a proof, as in the
// old solver).
//
// The cube is written into a buffer constraint allocated once with room for
// every variable, so that it has a 'Ref' and analysis can start from it
// without storing it.  It is not derived, so no QLRUP step exists for it:
// the proof task makes it a fatal error with a QLRUP tracer, and tracers
// that accept it receive it through 'add_model_cube' (ARCHITECTURE 8.1).

#include "internal.hpp"

#include <algorithm>
#include <cassert>

namespace miniqu {

#ifdef NDEBUG
static constexpr bool assertions_enabled = false;
#else
static constexpr bool assertions_enabled = true;
#endif

void Internal::init_model_cube () {
  assert (model_cube == Ref::none);
  // A constraint has at least one literal; the contents do not matter.
  model.assign (std::max<size_t> (prefix.size (), 1), mk_lit (0));
  model_cube = alloc_constraint (arena, model, Kind::Cube, false, 0);
  model.clear ();
}

// Called while 'seen' marks the variables of the unreduced cube.
void Internal::check_model_cube () const {
  for (Ref ref : irredundant[index (Kind::Clause)]) {
    const Constraint &c = deref (arena, ref);
    if (c.garbage ())
      continue;
    if (std::none_of (c.begin (), c.end (), [this] (Lit l) {
          return seen[var (l)] && val (l) > 0;
        }))
      fatal ("internal error: initial cube misses clause %lu",
             (unsigned long) c.id ());
  }
}

Ref Internal::initial_cube () {
  stats.modelcubes++;
  assert (model.empty ());
  for (Ref ref : irredundant[index (Kind::Clause)]) {
    const Constraint &c = deref (arena, ref);
    if (c.garbage ())
      continue;
    Lit hit = lit_undef;
    for (Lit l : c)
      if (val (l) > 0) {
        if (seen[var (l)]) {
          hit = l;
          break;
        }
        if (hit == lit_undef)
          hit = l;
      }
    if (hit == lit_undef)
      fatal ("internal error: clause %lu not satisfied by a complete "
             "assignment",
             (unsigned long) c.id ());
    if (!seen[var (hit)]) {
      seen[var (hit)] = 1;
      model.push_back (hit);
    }
  }
  if (assertions_enabled || opts.check)
    check_model_cube ();
  for (Lit l : model)
    seen[var (l)] = 0;

  // The old solver bumps the variables that reduction removes.
  std::sort (model.begin (), model.end ());
  const size_t size = prefix.reduced_size (model, Kind::Cube);
  for (size_t i = size; i < model.size (); i++)
    bump_variable (var (model[i]));
  model.resize (size);

  Constraint &c = deref (arena, model_cube);
  std::copy (model.begin (), model.end (), c.begin ());
  c.set_size (static_cast<uint32_t> (size));
  model.clear ();
  LOG (model_cube, "initial");
  return model_cube;
}

} // namespace miniqu
