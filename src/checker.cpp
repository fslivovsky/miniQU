// Online checker of proof steps (ARCHITECTURE 8.1), in the role of
// CaDiCaL's 'LratChecker': it receives every step the solver logs and
// replays each derived one exactly as doc/proof-format.md defines it.
//
// For a derived constraint C of kind K with chain id_1, ..., id_m: the
// resolvent R starts as constraint id_1; for every further premise A, if
// exactly one literal p of A has -p in R, R becomes (R \ {-p}) ∪ (A \ {p}),
// if none R stays, and if several the step is invalid; finally R is
// reduced and every literal of R must be in C.  If that fails, the variant
// that also reduces id_1 and every intermediate resolvent is tried.
// Reduction removes a secondary literal (universal in a clause,
// existential in a cube) when every primary variable of R comes before it
// in the extended prefix (all secondary literals if R has no primary one).
//
// The extended prefix is taken from the solver: the internal variable
// order is a linearisation of it (INV-ORDER, ARCHITECTURE 4.4), so the
// position of a proof number is the index of its internal variable.  For
// QCIR input a gate number has two variables, the existential one in
// clauses and the universal one in cubes; a number with a single variable
// (an input variable) means that variable in both kinds.
//
// Further checks: every id is fresh when added, every premise and every
// deleted id is live and of the step's kind, a deletion names the stored
// literals, no constraint has duplicate or complementary literals, every
// literal has a variable in that kind, and the concluded id is a live
// empty constraint of the concluded kind.  Original constraints cannot be
// validated against the circuit (the Lean checker does that); initial
// cubes from models are accepted as premise-free cubes (ARCHITECTURE 4.5),
// and both are then ordinary live constraints.

#include "checker.hpp"
#include "internal.hpp"
#include "message.hpp"

#include <algorithm>

namespace miniqu {

Checker::Checker (Internal &internal) : checked (internal.stats.checked) {
  const Prefix &prefix = internal.prefix;
  int largest = 0;
  for (const VarInfo &info : prefix.vars)
    largest = std::max (largest, info.proof);
  for (auto &list : places)
    list.assign ((size_t) largest + 1, Place{Quant::Exists, no_var});
  for (Var v = 0; v < prefix.size (); v++) {
    const VarInfo &info = prefix.vars[v];
    if (info.proof <= 0)
      continue;
    for (Kind kind : {Kind::Clause, Kind::Cube}) {
      Place &p = places[index (kind)][(size_t) info.proof];
      if (p.position == no_var || info.quant == primary (kind))
        p = Place{info.quant, v};
    }
  }
  in_resolvent.assign (2 * ((size_t) largest + 1), 0);
  in_step.assign (2 * ((size_t) largest + 1), 0);
}

void Checker::begin (const char *name, uint64_t id, Kind kind,
                     std::span<const int> lits,
                     std::span<const uint64_t> chain) {
  step_name = name;
  step_id = id;
  step_kind = kind;
  step_lits.assign (lits.begin (), lits.end ());
  step_chain.assign (chain.begin (), chain.end ());
}

void Checker::fail (const std::string &what) const {
  std::string step = std::string (step_name) + " " +
                     std::to_string (step_id) +
                     (step_kind == Kind::Clause ? " c" : " t");
  for (int lit : step_lits)
    step += " " + std::to_string (lit);
  step += " 0";
  for (uint64_t id : step_chain)
    step += " " + std::to_string (id);
  if (!step_chain.empty ())
    step += " 0";
  fatal ("proof checker: %s\n  step: %s", what.c_str (), step.c_str ());
}

const Checker::Place &Checker::place (Kind kind, int lit) const {
  const std::vector<Place> &list = places[index (kind)];
  const size_t number = (size_t) (lit < 0 ? -(int64_t) lit : lit);
  if (!lit || number >= list.size () || list[number].position == no_var)
    fail ("literal " + std::to_string (lit) + " has no variable in " +
          (kind == Kind::Clause ? "clauses" : "cubes"));
  return list[number];
}

// Marks the literals of the step in 'in_step'; the caller clears them.
void Checker::check_literals () {
  for (int lit : step_lits) {
    place (step_kind, lit);
    if (in_step[code (lit)])
      fail ("duplicate literal " + std::to_string (lit));
    if (in_step[code (-lit)])
      fail ("complementary literals " + std::to_string (lit));
    in_step[code (lit)] = 1;
  }
}

void Checker::check_fresh () const {
  if (!step_id || live.count (step_id))
    fail ("id " + std::to_string (step_id) + " is in use");
}

const Checker::Entry &Checker::premise (uint64_t id) const {
  const auto it = live.find (id);
  if (it == live.end ())
    fail ("id " + std::to_string (id) + " is not live");
  if (it->second.kind != step_kind)
    fail ("id " + std::to_string (id) + " has the other kind");
  return it->second;
}

void Checker::add_to_resolvent (int lit) {
  if (in_resolvent[code (lit)])
    return;
  in_resolvent[code (lit)] = 1;
  resolvent.push_back (lit);
}

void Checker::clear_resolvent () {
  for (int lit : resolvent)
    in_resolvent[code (lit)] = 0;
  resolvent.clear ();
}

void Checker::reduce () {
  const Quant primary_quant = primary (step_kind);
  bool any_primary = false;
  Var rightmost = 0;
  for (int lit : resolvent) {
    const Place &p = place (step_kind, lit);
    if (p.quant == primary_quant) {
      rightmost =
          any_primary ? std::max (rightmost, p.position) : p.position;
      any_primary = true;
    }
  }
  const auto reducible = [&] (int lit) {
    const Place &p = place (step_kind, lit);
    return p.quant != primary_quant && !in_resolvent[code (-lit)] &&
           (!any_primary || p.position > rightmost);
  };
  for (int lit : resolvent)
    if (reducible (lit))
      in_resolvent[code (lit)] = 0;
  std::erase_if (resolvent,
                 [this] (int lit) { return !in_resolvent[code (lit)]; });
}

bool Checker::replay (bool reduce_every_step, std::string &failure) {
  for (int lit : premise (step_chain[0]).lits)
    add_to_resolvent (lit);
  if (reduce_every_step)
    reduce ();
  for (size_t i = 1; i < step_chain.size (); i++) {
    const Entry &other = premise (step_chain[i]);
    int pivot = 0;
    for (int lit : other.lits)
      if (in_resolvent[code (-lit)]) {
        if (pivot) {
          failure = "premise " + std::to_string (step_chain[i]) +
                    " clashes in more than one literal";
          clear_resolvent ();
          return false;
        }
        pivot = lit;
      }
    if (!pivot)
      continue;
    in_resolvent[code (-pivot)] = 0;
    std::erase (resolvent, -pivot);
    for (int lit : other.lits)
      if (lit != pivot)
        add_to_resolvent (lit);
    if (reduce_every_step)
      reduce ();
  }
  reduce ();
  for (int lit : resolvent)
    if (!in_step[code (lit)]) {
      failure = "literal " + std::to_string (lit) +
                " of the resolvent is missing";
      clear_resolvent ();
      return false;
    }
  clear_resolvent ();
  return true;
}

void Checker::insert () {
  live.emplace (step_id, Entry{step_kind, step_lits});
}

void Checker::add_premise_free (const char *name, uint64_t id, Kind kind,
                                std::span<const int> lits) {
  begin (name, id, kind, lits, {});
  check_fresh ();
  check_literals ();
  for (int lit : step_lits)
    in_step[code (lit)] = 0;
  insert ();
}

void Checker::add_original (uint64_t id, Kind kind, int,
                            std::span<const int> lits) {
  add_premise_free ("original", id, kind, lits);
}

void Checker::add_derived (uint64_t id, Kind kind,
                           std::span<const int> lits,
                           std::span<const uint64_t> chain) {
  begin ("derived", id, kind, lits, chain);
  check_fresh ();
  if (step_chain.empty ())
    fail ("no premises");
  check_literals ();
  std::string failure, eager_failure;
  if (!replay (false, failure) && !replay (true, eager_failure))
    fail (failure +
          "; with reduction after every resolution: " + eager_failure);
  for (int lit : step_lits)
    in_step[code (lit)] = 0;
  insert ();
  checked++;
}

void Checker::delete_constraint (uint64_t id, Kind kind,
                                 std::span<const int> lits) {
  begin ("deletion", id, kind, lits, {});
  const auto it = live.find (id);
  if (it == live.end ())
    fail ("deleted id is not live");
  if (it->second.kind != kind)
    fail ("deleted id has the other kind");
  std::vector<int> stored = it->second.lits;
  std::sort (stored.begin (), stored.end ());
  std::sort (step_lits.begin (), step_lits.end ());
  if (stored != step_lits)
    fail ("deleted literals differ from the stored ones");
  live.erase (it);
}

void Checker::add_model_cube (uint64_t id, std::span<const int> lits) {
  add_premise_free ("model cube", id, Kind::Cube, lits);
}

void Checker::conclude (Kind kind, uint64_t id) {
  begin ("conclusion", id, kind, {}, {});
  const auto it = live.find (id);
  if (it == live.end () || it->second.kind != kind ||
      !it->second.lits.empty ())
    fail ("concluded id is not a live empty constraint of that kind");
}

} // namespace miniqu
