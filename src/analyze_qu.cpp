// Level-by-level conflict analysis (ARCHITECTURE 4.7, 7.5; the old
// 'analyze'): QU-resolution in mode 1, and mode 0 with '--legacyanalyze'.
//
// The resolvent of kind K is kept as variables per quantifier block
// ('LevelAnalysis'), with a count of its literals per decision level, and
// reduced along the way: only blocks up to the rightmost one holding a
// primary variable are kept, and a secondary literal of a reason enters
// only if it is left of that block.  Literals of the highest level present
// ('max_level') are resolved in reverse trail order until one literal is
// left on it (in mode 0 a primary one), which is then asserting.  On that
// level a secondary literal that cannot be resolved (no reason, or a
// reason of the other kind) is *blocked*, and a primary decision left of
// the leftmost blocked literal is passed over; once the pivot search runs
// below the level, it resolves the primary literals right of the leftmost
// blocked one, so that reduction can remove it.  When the count of
// 'max_level' drops to zero, the search starts again from the top of the
// next level present.
//
// Pivots may be secondary (QU-resolution): in mode 1 propagation assigns
// secondary literals too, and such a literal with a reason of kind K is
// resolved like a primary one.  A primary pivot whose reason has the
// *other* kind (it was propagated as a secondary literal of that kind)
// cannot be resolved: the analysis restarts from that reason with the
// other kind (porting note 4; the old 'goto analyzeStart').  In the new
// round the pivot's literal is taken as it occurs in its reason, true
// rather than vanished, and the variable counts as having no reason, so
// that it is never resolved with the reason it starts from.  The old code
// clears the reason on the trail for this; here the round alone treats it
// so, which is the same: every later round only sees variables assigned
// before it, and every outcome either ends the search or backtracks below
// it (its level is the highest one of the new round).
//
// A primary decision as pivot can only occur with '--dl' (as in
// 'analyze.cpp'); it becomes the dependency of that decision on the
// leftmost blocked variable, which is left of it and on its level or
// above.
//
// Every variable that enters the resolvent is bumped.  Root-level literals
// are resolved only while no literal above the root is left, which then
// ends with the empty constraint.
//
// Proof: as in 'analyze.cpp', the chain is the id of the constraint the
// round started from, followed by the reason ids in resolution order; a
// kind switch starts a new chain, as the old 'premise_ids' did.  Literals
// that the reduction along the way removed may be needed again after a
// later resolution step extends the rightmost primary block; the step is
// then valid in the variant of the proof format that reduces after every
// resolution.

#include "internal.hpp"

#include <algorithm>
#include <cassert>

namespace miniqu {

namespace {

enum class Outcome { Learnt, Switch, Dependency };

// One round of the analysis, for one kind.
class LevelAnalyzer {
  Internal &s;
  std::vector<std::vector<Var>> &at;
  std::vector<int> &position;
  const Kind kind;
  const Quant quant; // of the primary literals
  const Var flipped; // started from its reason: taken as true
  const bool mode0 = s.opts.mode == 0;
  int rightmost = -1;     // depth of the rightmost primary block, or -1
  int max_level = 0;      // highest level with a literal
  size_t next = 0;        // the pivot search goes on below this position
  size_t level_start = 0; // where 'max_level' starts on the trail
  Var asserting = no_var; // mode 0: the single literal of 'max_level'

public:
  Var blocked = no_var; // leftmost blocked variable
  Var pivot = no_var;   // the switch or dependency variable

  LevelAnalyzer (Internal &internal, Kind k, Var f)
      : s (internal), at (internal.qu.at), position (internal.qu.position),
        kind (k), quant (primary (k)), flipped (f) {}

  Outcome run (Ref conflict);
  Var derive ();
  void clear ();

private:
  bool seen (Var v) const { return position[v] >= 0; }
  bool is_primary (Var v) const { return s.prefix.quant (v) == quant; }
  int depth (Var v) const { return (int) s.prefix.depth (v); }
  int &count (Var v) { return s.level_count[(size_t) s.level (v)]; }
  Ref reason (Var v) const {
    return v == flipped ? Ref::none : s.reason (v);
  }

  void add (Var v) {
    std::vector<Var> &list = at[(size_t) depth (v)];
    position[v] = (int) list.size ();
    list.push_back (v);
    count (v)++;
    s.bump_variable (v);
  }

  void remove (Var v) {
    std::vector<Var> &list = at[(size_t) depth (v)];
    const Var last = list.back ();
    list[(size_t) position[v]] = last;
    position[last] = position[v];
    list.pop_back ();
    position[v] = -1;
    count (v)--;
  }

  void start_level () {
    level_start = max_level ? s.control[(size_t) max_level - 1] : 0;
  }

  // The old 'getAssertingVar': the first variable on 'max_level'.
  Var first_on_max_level () const {
    for (int d = 0; d <= rightmost; d++)
      for (Var v : at[(size_t) d])
        if (s.level (v) == max_level)
          return v;
    return no_var;
  }

  void update_asserting () {
    asserting = s.level_count[(size_t) max_level] > 1
                    ? no_var
                    : first_on_max_level ();
  }

  bool resolving () const {
    if (rightmost < 0)
      return false;
    if (max_level == 0 || s.level_count[(size_t) max_level] > 1)
      return true;
    assert (!mode0 || asserting != no_var);
    return mode0 && !is_primary (asserting);
  }

  void start (Ref conflict);
  void resolve (Var v, Ref reason);
};

void LevelAnalyzer::start (Ref conflict) {
  const Constraint &c = deref (s.arena, conflict);
  if (s.proof)
    s.chain.push_back (c.id ());
  for (Lit l : c)
    if (is_primary (var (l)))
      rightmost = std::max (rightmost, depth (var (l)));
  for (Lit l : c)
    if (depth (var (l)) <= rightmost)
      add (var (l));
  max_level = s.decision_level ();
  while (max_level && !s.level_count[(size_t) max_level])
    max_level--;
  next = s.trail.size ();
  start_level ();
  if (mode0)
    update_asserting ();
}

Outcome LevelAnalyzer::run (Ref conflict) {
  start (conflict);
  while (resolving ()) {
    assert (next > 0);
    const Var v = var (s.trail[--next]);
    if (!seen (v))
      continue;
    const Ref r = reason (v);
    if (next >= level_start) {
      if (!is_primary (v) &&
          (r == Ref::none || deref (s.arena, r).kind () != kind)) {
        blocked = std::min (blocked, v);
        continue;
      }
      if (is_primary (v) && r == Ref::none && blocked != no_var &&
          v < blocked)
        continue;
    } else {
      assert (max_level > 0 && blocked != no_var);
      if (!is_primary (v) || v < blocked)
        continue;
    }
    if (r == Ref::none) {
      assert (blocked != no_var && blocked < v);
      pivot = v;
      return Outcome::Dependency;
    }
    if (deref (s.arena, r).kind () != kind) {
      pivot = v;
      return Outcome::Switch;
    }
    resolve (v, r);
  }
  return Outcome::Learnt;
}

void LevelAnalyzer::resolve (Var v, Ref ref) {
  const Constraint &c = deref (s.arena, ref);
  assert (var (c[0]) == v);
  if (s.proof)
    s.chain.push_back (c.id ());
  remove (v);
  if (mode0 && v == asserting)
    asserting = no_var;
  for (uint32_t i = 1; i < c.size (); i++) {
    const Var u = var (c[i]);
    if (is_primary (u) && !seen (u)) {
      add (u);
      rightmost = std::max (rightmost, depth (u));
    }
  }
  // Reduction: drop the blocks right of the rightmost primary one.
  while (rightmost >= 0 &&
         (s.prefix.blocks[(size_t) rightmost].quant != quant ||
          at[(size_t) rightmost].empty ())) {
    for (Var u : at[(size_t) rightmost]) {
      position[u] = -1;
      count (u)--;
    }
    at[(size_t) rightmost].clear ();
    rightmost--;
  }
  if (rightmost < 0)
    return;
  if (blocked != no_var && rightmost < depth (blocked))
    blocked = no_var;
  for (uint32_t i = 1; i < c.size (); i++) {
    const Var u = var (c[i]);
    if (!is_primary (u) && !seen (u) && depth (u) < rightmost)
      add (u);
  }
  if (!s.level_count[(size_t) max_level]) {
    while (max_level && !s.level_count[(size_t) max_level])
      max_level--;
    next = s.control[(size_t) max_level];
    start_level ();
    blocked = no_var;
  }
  if (mode0 && (asserting == no_var || rightmost < depth (asserting)))
    update_asserting ();
}

// Writes the resolvent to 'derived' and returns the asserting variable,
// the one on the highest level ('no_var' if the resolvent is empty).
Var LevelAnalyzer::derive () {
  s.derived.clear ();
  Var asserting_var = no_var;
  for (int d = 0; d <= rightmost; d++)
    for (Var v : at[(size_t) d]) {
      Lit l = mk_lit (v);
      if (s.kval (kind, l) > 0)
        l = ~l;
      if (v == flipped)
        l = ~l;
      s.derived.push_back (l);
      if (asserting_var == no_var || s.level (v) > s.level (asserting_var))
        asserting_var = v;
    }
  return asserting_var;
}

void LevelAnalyzer::clear () {
  for (int d = 0; d <= rightmost; d++) {
    for (Var v : at[(size_t) d]) {
      position[v] = -1;
      s.level_count[(size_t) s.level (v)] = 0;
    }
    at[(size_t) d].clear ();
  }
}

} // namespace

void Internal::analyze_qu (Ref conflict) {
  const size_t levels = (size_t) decision_level () + 1;
  if (level_count.size () < levels) {
    level_count.resize (levels, 0);
    level_blocked.resize (levels, no_var);
  }
  qu.at.resize (prefix.blocks.size ());
  qu.position.resize (prefix.size (), -1);

  Kind kind = deref (arena, conflict).kind ();
  Var flipped = no_var;
  LOG (conflict, "analyzing");
  for (;;) {
    chain.clear ();
    LevelAnalyzer round (*this, kind, flipped);
    switch (round.run (conflict)) {
    case Outcome::Learnt: {
      const Var asserting = round.derive ();
      round.clear ();
      learn (kind, asserting);
      return;
    }
    case Outcome::Dependency:
      if (!opts.dl)
        fatal ("internal error: decision %u in the way of reducing %u "
               "without dependency learning",
               round.pivot + 1, round.blocked + 1);
      round.clear ();
      learn_dependency (round.pivot, round.blocked);
      return;
    case Outcome::Switch:
      round.clear ();
      flipped = round.pivot;
      conflict = reason (flipped);
      kind = other (kind);
      LOG (conflict, "switching kind at %u, analyzing", flipped + 1);
      break;
    }
  }
}

} // namespace miniqu
