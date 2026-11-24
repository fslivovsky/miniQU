// Learnt-constraint minimisation, '--ccminmode' 1-3 (ARCHITECTURE 7.5;
// the old 'finishLearnt', 'litRedundant' and 'minimize').
//
// A literal l of a learnt constraint C of kind K (other than the asserting
// literal at position 0) is redundant if resolving C with the reason of l,
// and recursively with the reasons of the literals that introduces, yields
// a constraint without l whose other literals are already in C or are
// removed by reduction.  Only reasons of kind K qualify, and only primary
// literals can be resolved away; root-level literals forced by a unit of
// kind K are free (resolving with the unit removes them).
//
//   1 (basic): every literal of the reason of l is in C or free.
//   2 (deep):  the same, recursively; results are cached per variable in
//              'seen' (removable / failed).
//   3 (deep with reduction): a secondary literal introduced this way need
//              not be in C if it is right of every primary literal that
//              remains, since the final reduction removes it.  For each
//              literal the recursion computes a bound: 0 if it cannot be
//              removed, 'no_var' if it can without introducing a literal,
//              otherwise the leftmost secondary variable it introduces.
//              Sorted by bound, the literals to keep form a prefix (the
//              rightmost primary variable kept only grows).  A literal on
//              the asserting level is never removed, and the recursion is
//              cut at depth 1000 (as the old code).
//
// In mode 1 the asserting literal may be secondary; the analysis then
// leaves a primary literal right of it, and the reduction keeps it only as
// long as one stays.  If the mode would remove all of them, the
// constraint is not minimised at all (M2-T5: the old code kept the literal
// unreduced, the M1 port lost it in the reduction and failed).  This is
// decided before and independently of the proof.
//
// Soundness: the minimised constraint is C resolved with reasons of its
// own kind, then reduced; every literal such a reason brings in is
// vanished, so no complementary pair arises.  The old code never
// minimised long-distance resolvents; neither does this.
//
// Proof (M2.3): minimisation runs alike with and without a proof, and the
// step of the learnt constraint justifies it.  Once the literals to remove
// are known, 'extend_chain' appends to the chain of the analysis the
// reasons of every variable the minimisation resolves away, in reverse
// trail order: the removed literals (ccminmode 3: only the primary ones;
// a removed secondary literal is right of every primary literal kept and
// falls to the final reduction) and, transitively, every literal of their
// reasons that is neither in C nor, in ccminmode 3, secondary.  A root
// literal whose reason is a unit of kind K is one of them; its unit id is
// appended like any reason.  The set is found by a pass from the removed
// literals after the decision, never from the marks of the search alone:
// a literal that was explored but stays, or whose exploration failed, is
// still in the resolvent, and resolving with its reason would remove a
// literal of C.  Why this is one valid QLRUP step:
//
// - Every literal of the resolvent R of the analysis and of these reasons
//   is assigned and vanished, except each reason's propagated literal (and,
//   after a kind switch in 'analyze_qu', the literal the round started
//   from, which is the asserting literal, never removed, and later on the
//   trail than every literal minimisation meets).  So each appended reason
//   clashes with R on its propagated literal and nowhere else.
// - Reverse trail order: a reason contains only literals assigned before
//   its own, so the literals it brings in are resolved later, and a
//   variable once resolved is never brought back.  The final R is thus the
//   kept literals plus, in ccminmode 3, introduced secondary literals,
//   which are right of every primary literal kept ('bound'), so the
//   reduction at the end of the step removes them.
// - Mode 1 and '--legacyanalyze', where the analysis part may need the
//   variant of the format that reduces after every step: there R after the
//   analysis part is exactly the resolvent 'analyze_qu' kept.  Reduction
//   removes only secondary literals and kept literals are never pivots, so
//   every primary literal kept stays in R; a secondary pivot of mode 1
//   that an intermediate reduction removed only makes its reason clash
//   nowhere (R stays), and the literals only that reason would bring in
//   are never introduced.  The final literal set is again a subset of the
//   kept literals and of introduced secondary literals right of every
//   kept primary one, so the step holds in whichever variant the analysis
//   part holds in.  A literal the analysis reduced along the way that a
//   minimisation reason brings back is either resolved away (modes 1, 2)
//   or secondary and right of every kept primary literal (mode 3).
//
// 'seen' is all zero on entry (the analyses clear it before 'learn') and
// is cleared again on return.  'stats.minimized' counts the literals that
// minimisation removes beyond those the reduction after it removes anyway
// (the resolvents of 'analyze_q' still hold such literals; the old solver
// reduced them in the analysis, so its 'conflict literals ... deleted'
// counts the same literals); 'stats.minimizedchain' counts the reason ids
// appended to chains.

#include "internal.hpp"

#include <algorithm>
#include <cassert>
#include <span>

namespace miniqu {

namespace {

// Flags in 'seen'.
enum : uint8_t {
  in_learnt = 1, // a literal of the constraint
  removable = 2, // ccminmode 2: shown redundant
  failed = 4,    // ccminmode 2: shown not redundant
  cached = 8,    // ccminmode 3: 'Minimizer::bound' is valid
  chained = 16,  // its reason extends the chain
};

constexpr int max_depth = 1000;

class Minimize {
  Internal &s;
  Minimizer &m;
  const Kind kind;

public:
  Minimize (Internal &internal, Kind k)
      : s (internal), m (internal.minimizer), kind (k) {}

  void mark (Var v, uint8_t flag) {
    if (!s.seen[v])
      m.touched.push_back (v);
    s.seen[v] |= flag;
  }

  // Each returns the number of literals kept, which it moves to the
  // front in their order; the removed ones follow.
  size_t basic (std::vector<Lit> &lits);
  size_t deep (std::vector<Lit> &lits);
  size_t bounded (std::vector<Lit> &lits);

  void extend_chain (std::span<const Lit> removed);

  // Whether the first 'kept' literals leave a primary one right of the
  // asserting literal, if that is secondary.
  bool keeps_asserting (const std::vector<Lit> &lits, size_t kept) const {
    const Var asserting = var (lits[0]);
    return s.prefix.is_primary (kind, asserting) ||
           std::any_of (lits.begin () + 1, lits.begin () + (long) kept,
                        [&] (Lit l) {
                          return var (l) > asserting &&
                                 s.prefix.is_primary (kind, var (l));
                        });
  }

  // The number of literals of 'lits' that reduction keeps.
  size_t reduced_size (const std::vector<Lit> &lits) const {
    Var rightmost = no_var;
    for (Lit l : lits)
      if (s.prefix.is_primary (kind, var (l)) &&
          (rightmost == no_var || var (l) > rightmost))
        rightmost = var (l);
    return rightmost == no_var
               ? 0
               : (size_t) std::count_if (
                     lits.begin (), lits.end (),
                     [=] (Lit l) { return var (l) <= rightmost; });
  }

private:
  // A reason of the analysed kind, or 'nullptr'.
  const Constraint *same_kind_reason (Var v) const {
    const Ref r = s.reason (v);
    if (r == Ref::none)
      return nullptr;
    const Constraint &c = deref (s.arena, r);
    return c.kind () == kind ? &c : nullptr;
  }

  bool free_root (Var v) const {
    const Constraint *c = same_kind_reason (v);
    return !s.level (v) && c && c->size () == 1;
  }

  bool locally_redundant (Var v) const;
  bool redundant (Lit p);
  Var bound (Lit, int asserting_level, int depth);

  bool resolved_away (Var removed) const {
    return s.opts.ccminmode != 3 || s.prefix.is_primary (kind, removed);
  }
  // Whether the decision of the mode allows to resolve away 'v', a literal
  // of a reason that is not in C (for assertions).
  bool shown_removable (Var v) const {
    switch (s.opts.ccminmode) {
    case 1:
      return free_root (v);
    case 2:
      return (s.seen[v] & removable) || free_root (v);
    default:
      return (s.seen[v] & cached) && m.bound[v];
    }
  }
};

bool Minimize::locally_redundant (Var v) const {
  const Constraint *c = same_kind_reason (v);
  if (!c)
    return false;
  for (uint32_t i = 1; i < c->size (); i++) {
    const Var u = var ((*c)[i]);
    if (!(s.seen[u] & in_learnt) && !free_root (u))
      return false;
  }
  return true;
}

size_t Minimize::basic (std::vector<Lit> &lits) {
  size_t j = 1;
  for (size_t i = 1; i < lits.size (); i++)
    if (!locally_redundant (var (lits[i])))
      std::swap (lits[j++], lits[i]);
  return j;
}

// Depth-first over the reasons, with an explicit stack of (position in
// the reason, literal whose reason it is).  On failure every literal on the
// stack is marked failed; on success every literal visited is removable.
bool Minimize::redundant (Lit p) {
  std::vector<std::pair<uint32_t, Lit>> &stack = m.stack;
  stack.clear ();
  const Constraint *c = same_kind_reason (var (p));
  assert (c);
  uint32_t i = 1;
  for (;;) {
    if (i < c->size ()) {
      const Lit l = (*c)[i];
      const Var u = var (l);
      if ((s.seen[u] & (in_learnt | removable)) || free_root (u)) {
        i++;
        continue;
      }
      const Constraint *reason = same_kind_reason (u);
      if (!reason || (s.seen[u] & failed)) {
        stack.emplace_back (0, p);
        for (const auto &entry : stack)
          if (!s.seen[var (entry.second)])
            mark (var (entry.second), failed);
        return false;
      }
      stack.emplace_back (i + 1, p);
      p = l;
      c = reason;
      i = 1;
    } else {
      if (!s.seen[var (p)])
        mark (var (p), removable);
      if (stack.empty ())
        return true;
      i = stack.back ().first;
      p = stack.back ().second;
      c = same_kind_reason (var (p));
      stack.pop_back ();
    }
  }
}

size_t Minimize::deep (std::vector<Lit> &lits) {
  size_t j = 1;
  for (size_t i = 1; i < lits.size (); i++)
    if (!same_kind_reason (var (lits[i])) || !redundant (lits[i]))
      std::swap (lits[j++], lits[i]);
  return j;
}

Var Minimize::bound (Lit lit, int asserting_level, int depth) {
  const Var v = var (lit);
  if (depth > max_depth)
    return 0;
  if (depth && (s.seen[v] & in_learnt))
    return no_var;
  if (s.seen[v] & cached)
    return m.bound[v];
  if (!s.prefix.is_primary (kind, v))
    return v;
  if (s.level (v) == asserting_level)
    return 0;
  const Constraint *c = same_kind_reason (v);
  if (!c)
    return 0;
  Var result = no_var;
  for (uint32_t i = 1; i < c->size () && result; i++)
    result = std::min (result, bound ((*c)[i], asserting_level, depth + 1));
  mark (v, cached);
  m.bound[v] = result;
  return result;
}

size_t Minimize::bounded (std::vector<Lit> &lits) {
  if (m.bound.size () < s.prefix.size ())
    m.bound.resize (s.prefix.size ());
  const int asserting_level = s.level (var (lits[0]));
  m.keys.clear ();
  for (size_t i = 1; i < lits.size (); i++)
    m.keys.emplace_back (bound (lits[i], asserting_level, 0), lits[i]);
  std::sort (
      m.keys.begin (), m.keys.end (),
      [] (const auto &a, const auto &b) { return a.first < b.first; });
  // The asserting literal may be secondary in mode 1.
  Var rightmost = var (lits[0]);
  size_t kept = 0;
  while (kept < m.keys.size () && m.keys[kept].first <= rightmost) {
    const Var v = var (m.keys[kept++].second);
    if (s.prefix.is_primary (kind, v))
      rightmost = std::max (rightmost, v);
  }
  for (size_t i = 0; i < m.keys.size (); i++)
    lits[i + 1] = m.keys[i].second;
  return kept + 1;
}

// The marking pass of the header comment, then the reason ids in reverse
// trail order.  'Minimizer::resolved' doubles as the work list.
void Minimize::extend_chain (std::span<const Lit> removed) {
  std::vector<Var> &resolved = m.resolved;
  assert (resolved.empty ());
  for (Lit l : removed)
    if (resolved_away (var (l))) {
      mark (var (l), chained);
      resolved.push_back (var (l));
    }
  for (size_t next = 0; next < resolved.size (); next++) {
    const Constraint *c = same_kind_reason (resolved[next]);
    assert (c);
    for (uint32_t i = 1; i < c->size (); i++) {
      const Var u = var ((*c)[i]);
      if ((s.seen[u] & (in_learnt | chained)) ||
          (s.opts.ccminmode == 3 && !s.prefix.is_primary (kind, u)))
        continue;
      assert (shown_removable (u));
      mark (u, chained);
      resolved.push_back (u);
    }
  }
  std::sort (resolved.begin (), resolved.end (), [this] (Var a, Var b) {
    return s.vtab[a].trail > s.vtab[b].trail;
  });
  for (Var v : resolved)
    s.chain.push_back (same_kind_reason (v)->id ());
  s.stats.minimizedchain += (int64_t) resolved.size ();
  resolved.clear ();
}

} // namespace

// 'lits[0]' is the asserting literal.
void Internal::minimize (std::vector<Lit> &lits, Kind kind) {
  assert (!lits.empty () && minimizer.touched.empty ());
  Minimize pass (*this, kind);
  const size_t before = pass.reduced_size (lits);
  for (Lit l : lits)
    pass.mark (var (l), in_learnt);
  size_t kept;
  switch (opts.ccminmode) {
  case 1:
    kept = pass.basic (lits);
    break;
  case 2:
    kept = pass.deep (lits);
    break;
  default:
    kept = pass.bounded (lits);
    break;
  }
  if (!pass.keeps_asserting (lits, kept))
    kept = lits.size ();
  LOG ("minimisation removed %zu of %zu literals", lits.size () - kept,
       lits.size ());
  if (proof)
    pass.extend_chain (std::span (lits).subspan (kept));
  lits.resize (kept);
  stats.minimized += (int64_t) (before - pass.reduced_size (lits));
  for (Var v : minimizer.touched)
    seen[v] = 0;
  minimizer.touched.clear ();
}

} // namespace miniqu
