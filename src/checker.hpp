#ifndef MINIQU_CHECKER_HPP_INCLUDED
#define MINIQU_CHECKER_HPP_INCLUDED

#include "lit.hpp"
#include "tracer.hpp"

#include <array>
#include <cstdint>
#include <string>
#include <unordered_map>
#include <vector>

namespace miniqu {

struct Internal;

// Online checker of the proof steps (checker.cpp, ARCHITECTURE 8.1).  It
// reads the prefix of 'internal' when it is created, so it is connected
// after the last variable has been added, and counts every replayed step
// in 'internal.stats.checked'.  A step that fails a check ends the run
// through 'fatal' with the step printed.
class Checker : public Tracer {
  struct Entry {
    Kind kind;
    std::vector<int> lits;
  };

  // Where a proof number sits in the extended prefix of one kind.
  struct Place {
    Quant quant;
    Var position; // 'no_var' if the kind has no variable of that number
  };

  int64_t &checked;
  std::array<std::vector<Place>, 2> places; // per kind, per proof number
  std::unordered_map<uint64_t, Entry> live;

  // The step being checked, for the error message.
  const char *step_name = "";
  uint64_t step_id = 0;
  Kind step_kind = Kind::Clause;
  std::vector<int> step_lits;
  std::vector<uint64_t> step_chain;

  std::vector<int> resolvent;
  std::vector<uint8_t> in_resolvent; // per literal code
  std::vector<uint8_t> in_step;      // per literal code

  static size_t code (int lit) {
    return 2 * static_cast<size_t> (lit < 0 ? -lit : lit) +
           (lit < 0 ? 1u : 0u);
  }

  void begin (const char *name, uint64_t id, Kind, std::span<const int>,
              std::span<const uint64_t>);
  [[noreturn]] void fail (const std::string &what) const;
  const Place &place (Kind, int lit) const;
  void check_literals ();
  void check_fresh () const;
  const Entry &premise (uint64_t id) const;
  void add_to_resolvent (int lit);
  void clear_resolvent ();
  void reduce ();
  bool replay (bool reduce_every_step, std::string &failure);
  void insert ();
  void add_premise_free (const char *name, uint64_t id, Kind,
                         std::span<const int> lits);

public:
  explicit Checker (Internal &);

  void add_original (uint64_t id, Kind, int gate,
                     std::span<const int> lits) override;
  void add_derived (uint64_t id, Kind, std::span<const int> lits,
                    std::span<const uint64_t> chain) override;
  void delete_constraint (uint64_t id, Kind,
                          std::span<const int> lits) override;
  void add_model_cube (uint64_t id, std::span<const int> lits) override;
  void conclude (Kind, uint64_t id) override;
};

} // namespace miniqu

#endif
