// Long-distance conflict analysis, mode 2 (ARCHITECTURE 4.7, 7.5; the old
// 'analyzeLDQ').
//
// A conflict of kind K (no primary literal left non-vanished; secondary
// literals may be unassigned) is resolved with the reasons of its primary
// literals.  Propagation in mode 2 only forces primary literals, so such a
// reason has kind K, and its secondary literals are vanished or were
// unassigned and right of the forced literal when it propagated.  Two such
// unassigned literals of one secondary variable may enter the resolvent
// with opposite signs: that is long-distance resolution, and why the
// resolvent is kept per literal ('LongDistanceAnalysis').
//
// The resolvent is kept reduced along the way, as in 'analyze_qu': only
// blocks up to the rightmost one holding a primary literal are kept, and a
// secondary literal of a reason enters only if it is left of that block.
// Resolution stops when the primary literals of the highest level present
// ('max_level', above 0) are a single one, the asserting literal 'a'
// (the first one on that level in block order), and the result is
// asserting in the long-distance sense: every secondary literal left of
// 'a' is assigned below the level of 'a', and unless 'a' is alone there is
// a second literal to watch, the one of the highest level below that of
// 'a' among the primary literals and the assigned secondary literals left
// of 'a'.  Its level is the backjump level, and after the backjump 'a' is
// unit under the rule of 'propagate_ldq.cpp' (every literal that could
// block it is assigned, the others are to its right).
//
// Pivots are taken in reverse trail order among the primary literals of
// the resolvent that have a reason, whatever their level: unlike mode 0,
// a decision in the way is passed over, and a primary literal below the
// highest level may be resolved while no asserting literal is found.  Only
// when every primary literal left is a decision does the analysis end in a
// dependency (only possible with '--dl'): the rightmost primary decision x
// depends on the first secondary variable y left of it that is unassigned
// or assigned on the level of x or above; backtracking below x unassigns
// y.  Root-level literals are resolved only while no literal above the
// root is left, which then ends with the empty constraint.
//
// Every variable that enters the resolvent is bumped.  Minimisation does
// not apply to long-distance resolvents (the old code calls it only from
// the other two analyses).
//
// No proof: long-distance steps are not expressible in QLRUP or the trace
// format, so no tracer is connected in mode 2 ('--proof' and '--trace' are
// rejected at start-up, the internal 'Checker' is not connected).

#include "internal.hpp"

#include <algorithm>
#include <cassert>
#include <cstdint>

namespace miniqu {

namespace {

class LongDistanceAnalyzer {
  Internal &s;
  std::vector<std::vector<Lit>> &at;
  std::vector<int> &position;
  const Kind kind;
  int rightmost = -1; // depth of the rightmost primary block, or -1
  int max_level = 0;  // highest level with a primary literal
  size_t next;        // the pivot search goes on below this position

public:
  Var asserting = no_var;
  Var second = no_var; // the other watched variable

  LongDistanceAnalyzer (Internal &internal, Kind k)
      : s (internal), at (internal.ldq.at),
        position (internal.ldq.position), kind (k),
        next (internal.trail.size ()) {}

  void start (Ref conflict);
  bool resolving ();
  Var next_pivot ();
  void resolve (Var pivot);
  Var dependency (Var &decision) const;
  void derive ();
  void clear ();

private:
  bool is_primary (Var v) const { return s.prefix.is_primary (kind, v); }
  int depth (Var v) const { return (int) s.prefix.depth (v); }
  bool contains (Lit l) const { return position[index (l)] >= 0; }
  int &count (Var v) { return s.level_count[(size_t) s.level (v)]; }

  void add (Lit l) {
    std::vector<Lit> &list = at[(size_t) depth (var (l))];
    position[index (l)] = (int) list.size ();
    list.push_back (l);
    s.bump_variable (var (l));
  }

  void add_primary (Lit l) {
    s.seen[var (l)] = 1;
    count (var (l))++;
    rightmost = std::max (rightmost, depth (var (l)));
    add (l);
  }

  void remove (Lit l) {
    std::vector<Lit> &list = at[(size_t) depth (var (l))];
    const Lit last = list.back ();
    list[(size_t) position[index (l)]] = last;
    position[index (last)] = position[index (l)];
    list.pop_back ();
    position[index (l)] = -1;
  }

  void lower_max_level () {
    while (max_level && !s.level_count[(size_t) max_level])
      max_level--;
  }

  // The vanished literal of an assigned variable.
  Lit vanished (Var v) const {
    const Lit l = mk_lit (v);
    return s.kval (kind, l) < 0 ? l : ~l;
  }

  Var first_on_max_level () const;
  bool is_asserting ();
};

void LongDistanceAnalyzer::start (Ref conflict) {
  const Constraint &c = deref (s.arena, conflict);
  for (Lit l : c)
    if (is_primary (var (l)))
      rightmost = std::max (rightmost, depth (var (l)));
  for (Lit l : c) {
    if (is_primary (var (l)))
      add_primary (l);
    else if (depth (var (l)) < rightmost)
      add (l);
  }
  max_level = s.decision_level ();
  lower_max_level ();
}

// The old 'getAssertingVarLDQ'.
Var LongDistanceAnalyzer::first_on_max_level () const {
  for (int d = 0; d <= rightmost; d++)
    for (Lit l : at[(size_t) d])
      if (is_primary (var (l)) && s.level (var (l)) == max_level)
        return var (l);
  return no_var;
}

// The old 'isAsserting'; also chooses 'second'.
bool LongDistanceAnalyzer::is_asserting () {
  const int alevel = s.level (asserting);
  for (int d = 0; d < depth (asserting); d++)
    for (Lit l : at[(size_t) d])
      if (!is_primary (var (l)) &&
          (!s.val (l) || s.level (var (l)) >= alevel))
        return false;
  second = no_var;
  size_t size = 0;
  for (int d = 0; d <= rightmost; d++)
    for (Lit l : at[(size_t) d]) {
      size++;
      const Var v = var (l);
      if ((is_primary (v) || (v < asserting && s.val (l))) &&
          s.level (v) < alevel &&
          (second == no_var || s.level (second) < s.level (v)))
        second = v;
    }
  return size == 1 || second != no_var;
}

bool LongDistanceAnalyzer::resolving () {
  if (rightmost < 0)
    return false;
  if (max_level == 0 || s.level_count[(size_t) max_level] > 1)
    return true;
  asserting = first_on_max_level ();
  return !is_asserting ();
}

// Returns 'no_var' when every primary variable left is a decision.
Var LongDistanceAnalyzer::next_pivot () {
  while (next > 0) {
    const Var v = var (s.trail[--next]);
    if (s.seen[v] && s.reason (v) != Ref::none)
      return v;
  }
  return no_var;
}

void LongDistanceAnalyzer::resolve (Var pivot) {
  const Constraint &c = deref (s.arena, s.reason (pivot));
  assert (var (c[0]) == pivot && c.kind () == kind);
  remove (vanished (pivot));
  count (pivot)--;
  s.seen[pivot] = 0;
  for (uint32_t i = 1; i < c.size (); i++)
    if (is_primary (var (c[i])) && !contains (c[i]))
      add_primary (c[i]);
  if (s.level (pivot) == max_level)
    lower_max_level ();
  // Reduction: drop the blocks right of the rightmost primary one.  They
  // hold secondary literals only, primary literals are never dropped.
  while (rightmost >= 0 &&
         (s.prefix.blocks[(size_t) rightmost].quant != primary (kind) ||
          at[(size_t) rightmost].empty ())) {
    for (Lit l : at[(size_t) rightmost])
      position[index (l)] = -1;
    at[(size_t) rightmost].clear ();
    rightmost--;
  }
  if (rightmost < 0)
    return;
  for (uint32_t i = 1; i < c.size (); i++) {
    const Lit l = c[i];
    if (!contains (l) && !is_primary (var (l)) &&
        depth (var (l)) < rightmost)
      add (l);
  }
}

// The old 'getBlockedVariable', for the rightmost primary decision.
Var LongDistanceAnalyzer::dependency (Var &decision) const {
  decision = var (at[(size_t) rightmost].back ());
  assert (is_primary (decision) && s.reason (decision) == Ref::none);
  for (int d = 0; d < depth (decision); d++)
    for (Lit l : at[(size_t) d])
      if (!is_primary (var (l)) &&
          (!s.val (l) || s.level (var (l)) >= s.level (decision)))
        return var (l);
  return no_var;
}

// Writes the resolvent to 'derived' in block order, with the asserting
// literal at position 0 and the second watched literal at position 1 (of
// the two literals of 'second', the one met last, as the old code).
void LongDistanceAnalyzer::derive () {
  constexpr size_t none = SIZE_MAX;
  s.derived.clear ();
  size_t first = none, other = none;
  for (int d = 0; d <= rightmost; d++)
    for (Lit l : at[(size_t) d]) {
      if (var (l) == asserting)
        first = s.derived.size ();
      else if (var (l) == second)
        other = s.derived.size ();
      s.derived.push_back (l);
    }
  if (s.derived.size () < 2)
    return;
  assert (first != none && other != none);
  std::swap (s.derived[0], s.derived[first]);
  if (other == 0)
    other = first;
  std::swap (s.derived[1], s.derived[other]);
}

void LongDistanceAnalyzer::clear () {
  for (int d = 0; d <= rightmost; d++) {
    for (Lit l : at[(size_t) d]) {
      position[index (l)] = -1;
      if (is_primary (var (l))) {
        s.seen[var (l)] = 0;
        count (var (l)) = 0;
      }
    }
    at[(size_t) d].clear ();
  }
}

} // namespace

void Internal::analyze_ldq (Ref conflict) {
  assert (opts.mode == 2 && !proof);
  const size_t levels = (size_t) decision_level () + 1;
  if (level_count.size () < levels) {
    level_count.resize (levels, 0);
    level_blocked.resize (levels, no_var);
  }
  ldq.at.resize (prefix.blocks.size ());
  ldq.position.resize (2 * (size_t) prefix.size (), -1);

  const Kind kind = deref (arena, conflict).kind ();
  LOG (conflict, "analyzing");
  LongDistanceAnalyzer analyzer (*this, kind);
  analyzer.start (conflict);
  while (analyzer.resolving ()) {
    const Var pivot = analyzer.next_pivot ();
    if (pivot != no_var) {
      LOG (reason (pivot), "resolving on %u with", pivot + 1);
      analyzer.resolve (pivot);
      continue;
    }
    Var decision;
    const Var blocked = analyzer.dependency (decision);
    if (!opts.dl || blocked == no_var)
      fatal ("internal error: decision %u in the way of a long-distance "
             "resolvent without dependency learning",
             decision + 1);
    analyzer.clear ();
    learn_dependency (decision, blocked);
    return;
  }
  analyzer.derive ();
  analyzer.clear ();
  if (derived.empty ())
    learn_empty (kind);
  else
    learn_watched (kind);
}

} // namespace miniqu
