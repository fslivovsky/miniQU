#ifndef MINIQU_RECORDER_HPP_INCLUDED
#define MINIQU_RECORDER_HPP_INCLUDED

// A tracer that remembers every step as text, for tests of the places
// where steps are logged.

#include "tracer.hpp"

#include <span>
#include <string>
#include <vector>

// Records every step as one line: "o ID KIND GATE: LITS", "a ID KIND: LITS
// : CHAIN", "d ID", "m ID: LITS", "e KIND ID" (conclude).
class Recorder : public miniqu::Tracer {
  using Kind = miniqu::Kind;
  static std::string kind (Kind k) { return k == Kind::Clause ? "c" : "t"; }
  template <class T> static std::string list (std::span<const T> xs) {
    std::string s;
    for (T x : xs)
      s += " " + std::to_string (x);
    return s;
  }

public:
  std::vector<std::string> steps;

  void add_original (uint64_t id, Kind k, int gate,
                     std::span<const int> lits) override {
    steps.push_back ("o " + std::to_string (id) + " " + kind (k) + " " +
                     std::to_string (gate) + ":" + list (lits));
  }
  void add_derived (uint64_t id, Kind k, std::span<const int> lits,
                    std::span<const uint64_t> chain) override {
    steps.push_back ("a " + std::to_string (id) + " " + kind (k) + ":" +
                     list (lits) + " :" + list (chain));
  }
  void delete_constraint (uint64_t id, Kind,
                          std::span<const int>) override {
    steps.push_back ("d " + std::to_string (id));
  }
  void add_model_cube (uint64_t id, std::span<const int> lits) override {
    steps.push_back ("m " + std::to_string (id) + ":" + list (lits));
  }
  void conclude (Kind k, uint64_t id) override {
    steps.push_back ("e " + kind (k) + " " + std::to_string (id));
  }
};

#endif
