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
// Soundness: the minimised constraint is C resolved with reasons of its
// own kind, then reduced; every resolution is on a primary pivot and every
// literal it brings in is vanished, so no complementary pair arises.  It
// is one QLRUP step from C's antecedents plus those reasons, but the chain
// of the analysis does not list them, so in M1 minimisation is off while a
// tracer is connected ('Internal::minimizing'; M2.3 extends the chain).
// The old code never minimised long-distance resolvents; neither does this.
//
// 'seen' is all zero on entry (the analyses clear it before 'learn') and
// is cleared again on return.  'stats.minimized' counts removed literals.

#include "internal.hpp"

#include <algorithm>
#include <cassert>

namespace miniqu {

namespace {

// Flags in 'seen'.
enum : uint8_t {
  in_learnt = 1, // a literal of the constraint
  removable = 2, // ccminmode 2: shown redundant
  failed = 4,    // ccminmode 2: shown not redundant
  cached = 8,    // ccminmode 3: 'Minimizer::bound' is valid
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

  size_t basic (std::vector<Lit> &lits);
  size_t deep (std::vector<Lit> &lits);
  size_t bounded (std::vector<Lit> &lits);

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
      lits[j++] = lits[i];
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
      lits[j++] = lits[i];
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
  size_t j = 1;
  for (const auto &[limit, l] : m.keys) {
    if (limit > rightmost)
      break;
    lits[j++] = l;
    if (s.prefix.is_primary (kind, var (l)))
      rightmost = std::max (rightmost, var (l));
  }
  return j;
}

} // namespace

// 'lits[0]' is the asserting literal.
void Internal::minimize (std::vector<Lit> &lits, Kind kind) {
  assert (!lits.empty () && minimizer.touched.empty ());
  Minimize pass (*this, kind);
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
  LOG ("minimisation removed %zu of %zu literals", lits.size () - kept,
       lits.size ());
  stats.minimized += (int64_t) (lits.size () - kept);
  lits.resize (kept);
  for (Var v : minimizer.touched)
    seen[v] = 0;
  minimizer.touched.clear ();
}

} // namespace miniqu
