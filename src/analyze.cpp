// Q-resolution conflict analysis, mode 0 (ARCHITECTURE 4.7, 7.5; README.md
// "Conflict analysis"; the old 'analyzeQ').
//
// A conflict of kind K (a falsified clause or a satisfied cube; all its
// literals are assigned, mode 0 completes the conflict) is resolved with
// the reasons of its *primary* literals in reverse trail order.  A reason
// of a primary literal has the same kind K, since in mode 0 only primary
// literals are propagated.  Secondary literals cannot be resolved away;
// they disappear by reduction ('qreduce') only if every primary literal of
// the result is quantified further out.  The literals of a secondary
// variable assigned on or after the current pivot level are *blocked*:
// after backjumping they would be unassigned and would keep the learnt
// constraint from being unit.  Hence the asserting condition: a primary
// literal is asserting when it is the only primary literal of its level
// (that level above 0) and is left of ('<') every blocked secondary
// literal.  Once it is found, the primary literals right of the leftmost
// blocked literal are resolved away too, so that reduction removes every
// blocked literal; the others stay.
//
// A decision can be in the way only when decisions do not follow the
// prefix.  Without dependency learning it cannot be: a primary decision
// pivot p on level L was decided when every decision variable of the
// blocks before its own was assigned, on levels below L; a blocked
// variable b < p of the other quantifier lies in such an earlier block and
// has a level >= the pivot level >= L.  The argument needs b to be a
// decision variable: secondary variables of a clause (cube) are universal
// (existential) input variables of the encoding, except in initial cubes
// for QCIR input, which INV-COMPLETE makes unreachable (ARCHITECTURE 4.5).
// Dependency learning (M1-T08) turns this case into a learnt dependency.
//
// Root-level literals stay in the learnt constraint (porting note 5).  All
// comparisons of variables are index comparisons (INV-ORDER); 'no_var' is
// greater than every variable, so "no blocked variable" needs no case.
//
// Proof: the learnt constraint is one QLRUP step whose chain is the
// conflict id followed by the reason ids in resolution order ('chain',
// filled only when a proof is written), logged by 'learn'.

#include "internal.hpp"

#include <algorithm>
#include <cassert>

namespace miniqu {

void Internal::analyze (Ref conflict) {
  assert (opts.mode == 0 && !opts.legacyanalyze && !opts.dl);
  stats.conflicts++;
  const Kind kind = deref (arena, conflict).kind ();
  LOG (conflict, "analyzing");

  const size_t levels = (size_t) decision_level () + 1;
  if (level_count.size () < levels) {
    level_count.resize (levels, 0);
    level_blocked.resize (levels, no_var);
  }
  chain.clear ();

  int pivot_level = decision_level ();
  Var blocked = no_var;   // leftmost secondary variable at or above it
  Var asserting = no_var; // the asserting variable once found
  int remaining = 0;      // primary literals that may have to be resolved

  // Adds the literals of a constraint from position 'from' on.
  const auto add = [&] (Ref ref, uint32_t from) {
    const Constraint &c = deref (arena, ref);
    assert (c.kind () == kind);
    if (proof)
      chain.push_back (c.id ());
    for (uint32_t i = from; i < c.size (); i++) {
      const Lit l = c[i];
      const Var v = var (l);
      if (seen[v])
        continue;
      assert (val (l));
      seen[v] = 1;
      analyzed.push_back (l);
      bump_variable (v);
      const int lvl = level (v);
      if (prefix.is_primary (kind, v)) {
        level_count[(size_t) lvl]++;
        remaining += asserting == no_var || v > blocked;
      } else if (lvl >= pivot_level)
        blocked = std::min (blocked, v);
      else
        level_blocked[(size_t) lvl] =
            std::min (level_blocked[(size_t) lvl], v);
    }
  };

  add (conflict, 0);
  size_t i = trail.size ();
  while (remaining) {
    Var pivot;
    do {
      assert (i > 0);
      pivot = var (trail[--i]);
    } while (!seen[pivot] || !prefix.is_primary (kind, pivot) ||
             (asserting != no_var && pivot < blocked));

    if (asserting == no_var) {
      // Secondary literals on the levels the pivot level moves past are
      // now blocked as well.
      for (; pivot_level > level (pivot); pivot_level--)
        blocked =
            std::min (blocked, level_blocked[(size_t) pivot_level - 1]);
      if (pivot_level > 0 && level_count[(size_t) pivot_level] == 1 &&
          pivot < blocked) {
        asserting = pivot;
        LOG ("asserting variable %u, blocked from %u", pivot + 1,
             blocked + 1);
        remaining = 0;
        for (Lit l : analyzed) {
          const Var v = var (l);
          remaining +=
              seen[v] && prefix.is_primary (kind, v) && v > blocked;
        }
        continue;
      }
    }

    const Ref reason = vtab[pivot].reason;
    if (reason == Ref::none)
      fatal ("internal error: decision %u in the way of reducing %u "
             "without dependency learning",
             pivot + 1, blocked + 1);
    assert (var (deref (arena, reason)[0]) == pivot);
    seen[pivot] = 0;
    level_count[(size_t) level (pivot)]--;
    remaining--;
    add (reason, 1);
  }

  derived.clear ();
  for (Lit l : analyzed)
    if (seen[var (l)])
      derived.push_back (l);
  clear_analyzed ();
  learn (kind, asserting);
}

void Internal::clear_analyzed () {
  for (Lit l : analyzed) {
    const Var v = var (l);
    const size_t lvl = (size_t) level (v);
    seen[v] = 0;
    level_count[lvl] = 0;
    level_blocked[lvl] = no_var;
  }
  analyzed.clear ();
}

} // namespace miniqu
