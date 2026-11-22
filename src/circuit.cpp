#include "circuit.hpp"

#include "message.hpp"

#include <algorithm>
#include <array>
#include <cassert>
#include <cstdlib>
#include <limits>

namespace miniqu {

// The circuit built from a QCIR file.  Gate data is a few words per gate
// plus the flat input array, because benchmark files have tens of millions
// of gates and the parser must not use more memory than the old one.

static size_t index_of_gate (int number, int variables) {
  return static_cast<size_t> (number - variables - 1);
}

const Circuit::Gate &Circuit::gate (int number) const {
  assert (is_gate (number) && number <= variables_ + gates ());
  return gate_table[index_of_gate (number, variables_)];
}

std::span<const int> Circuit::inputs (int number) const {
  const Gate &g = gate (number);
  return {input_table.data () + g.offset, g.size};
}

bool Circuit::removed (int number) const {
  return !removed_.empty () && removed_[index_of_gate (number, variables_)];
}

Polarity Circuit::polarity (int number) const {
  return polarities.empty ()
             ? Polarity::None
             : polarities[index_of_gate (number, variables_)];
}

const std::string &Circuit::name (int number) const {
  static const std::string anonymous;
  const size_t i = static_cast<size_t> (number - 1);
  return i < names.size () && names[i] ? *names[i] : anonymous;
}

// The proof number of the 'count'-th gate from now on.
int Circuit::next_number (int count) const {
  const size_t number = static_cast<size_t> (variables_) +
                        gate_table.size () + static_cast<size_t> (count);
  if (number >= static_cast<size_t> (provisional))
    fatal ("circuit too large");
  return static_cast<int> (number);
}

// Binds an identifier to a proof number; false if it already has one.
bool Circuit::define (const std::string &id, int number) {
  auto [it, inserted] = ids.try_emplace (id, number);
  if (!inserted) {
    if (it->second < provisional)
      return false;
    pending[static_cast<size_t> (it->second - provisional)].number = number;
    it->second = number;
  }
  const size_t i = static_cast<size_t> (number - 1);
  if (names.size () <= i)
    names.resize (i + 1, nullptr);
  names[i] = &it->first;
  return true;
}

bool Circuit::add_variable (Quant quant, const std::string &id) {
  assert (gate_table.empty ());
  if (!define (id, variables_ + 1))
    return false;
  variables_++;
  if (blocks_.empty () || blocks_.back ().quant != quant)
    blocks_.push_back ({quant, variables_, variables_});
  else
    blocks_.back ().last = variables_;
  return true;
}

int Circuit::reference (const std::string &id, uint64_t line) {
  auto [it, inserted] = ids.try_emplace (id, provisional);
  if (inserted) {
    it->second = provisional + static_cast<int> (pending.size ());
    pending.push_back ({&it->first, line, 0});
  }
  return it->second;
}

void Circuit::append_gate (GateType type, std::span<const int> in) {
  if (input_table.size () + in.size () >
      std::numeric_limits<uint32_t>::max ())
    fatal ("circuit too large");
  gate_table.push_back ({static_cast<uint32_t> (input_table.size ()),
                         static_cast<uint32_t> (in.size ()), type});
  input_table.insert (input_table.end (), in.begin (), in.end ());
}

int Circuit::add_gate (GateType type, const std::string &id,
                       std::span<const int> in) {
  const int number = next_number (1);
  if (!define (id, number))
    return 0;
  append_gate (type, in);
  return number;
}

// An xor or ite is two helper gates, which carry no name, followed by the
// or gate that carries it.  This is the order of doc/proof-format.md.
int Circuit::add_xor (const std::string &id, int a, int b) {
  const int number = next_number (3);
  if (!define (id, number))
    return 0;
  append_gate (GateType::And, std::array{a, -b});
  append_gate (GateType::And, std::array{-a, b});
  append_gate (GateType::Or, std::array{number - 2, number - 1});
  return number;
}

int Circuit::add_ite (const std::string &id, int c, int a, int b) {
  const int number = next_number (3);
  if (!define (id, number))
    return 0;
  append_gate (GateType::And, std::array{c, a});
  append_gate (GateType::And, std::array{-c, b});
  append_gate (GateType::Or, std::array{number - 2, number - 1});
  return number;
}

// Depth-first search with colours; a gate that is reached again while it is
// still open depends on itself.  Only needed when a gate was used before
// its definition: otherwise every input has a smaller number.  Returns the
// number of a named gate on a cycle, 0 if there is none.
int Circuit::find_cycle () const {
  enum : uint8_t { unseen, open, done };
  std::vector<uint8_t> colour (gate_table.size (), unseen);
  std::vector<std::pair<int, uint32_t>> stack; // gate, next input
  for (int root = variables_ + 1; root <= variables_ + gates (); root++) {
    if (colour[index_of_gate (root, variables_)] != unseen)
      continue;
    colour[index_of_gate (root, variables_)] = open;
    stack.push_back ({root, 0});
    while (!stack.empty ()) {
      auto &[number, next] = stack.back ();
      const auto in = inputs (number);
      if (next == in.size ()) {
        colour[index_of_gate (number, variables_)] = done;
        stack.pop_back ();
        continue;
      }
      const int input = std::abs (in[next++]);
      if (!is_gate (input))
        continue;
      uint8_t &c = colour[index_of_gate (input, variables_)];
      if (c == open) {
        auto at = std::find_if (stack.begin (), stack.end (),
                                [&] (auto &e) { return e.first == input; });
        while (name (at->first).empty ())
          at++;
        return at->first;
      }
      if (c == unseen) {
        c = open;
        stack.push_back ({input, 0});
      }
    }
  }
  return 0;
}

std::optional<Circuit::Defect> Circuit::resolve () {
  if (pending.empty ())
    return std::nullopt;
  for (const Pending &p : pending)
    if (!p.number)
      return Defect{Defect::Kind::Undefined, *p.name, p.line};
  auto replace = [&] (int &literal) {
    const int number = std::abs (literal);
    if (number >= provisional) {
      const int target =
          pending[static_cast<size_t> (number - provisional)].number;
      literal = literal < 0 ? -target : target;
    }
  };
  for (int &literal : input_table)
    replace (literal);
  replace (output_);
  pending = {};
  if (const int number = find_cycle ())
    return Defect{Defect::Kind::Cyclic, name (number), 0};
  return std::nullopt;
}

int Circuit::remove_redundant () {
  removed_.assign (gate_table.size (), 1);
  std::vector<int> stack;
  auto visit = [&] (int literal) {
    const int number = std::abs (literal);
    if (is_gate (number) && removed_[index_of_gate (number, variables_)]) {
      removed_[index_of_gate (number, variables_)] = 0;
      stack.push_back (number);
    }
  };
  visit (output_);
  while (!stack.empty ()) {
    const int number = stack.back ();
    stack.pop_back ();
    for (int input : inputs (number))
      visit (input);
  }
  return static_cast<int> (
      std::count (removed_.begin (), removed_.end (), 1));
}

// Polarities spread from the output.  A gate is visited again whenever it
// gains a polarity, which happens at most twice, so the order in which
// gates are visited does not matter (inputs may have larger numbers).
void Circuit::compute_polarities () {
  polarities.assign (gate_table.size (), Polarity::None);
  std::vector<int> stack;
  auto spread = [&] (int literal, Polarity p) {
    const int number = std::abs (literal);
    if (!is_gate (number))
      return;
    Polarity &current = polarities[index_of_gate (number, variables_)];
    const Polarity updated = current | (literal < 0 ? negate (p) : p);
    if (updated != current) {
      current = updated;
      stack.push_back (number);
    }
  };
  spread (output_, Polarity::Positive);
  while (!stack.empty ()) {
    const int number = stack.back ();
    stack.pop_back ();
    const Polarity p = polarities[index_of_gate (number, variables_)];
    for (int input : inputs (number))
      spread (input, p);
  }
}

// Iterative, because circuits are deep.  A gate is finished when all its
// inputs are.
std::vector<int> Circuit::gate_depths () const {
  std::vector<int> depth (static_cast<size_t> (variables_ + gates ()) + 1,
                          -1);
  for (size_t b = 0; b < blocks_.size (); b++)
    for (int v = blocks_[b].first; v <= blocks_[b].last; v++)
      depth[static_cast<size_t> (v)] = static_cast<int> (b);
  std::vector<uint8_t> started (gate_table.size (), 0);
  std::vector<std::pair<int, uint32_t>> stack; // gate, next input
  for (int root = variables_ + 1; root <= variables_ + gates (); root++) {
    if (started[index_of_gate (root, variables_)])
      continue;
    started[index_of_gate (root, variables_)] = 1;
    stack.push_back ({root, 0});
    while (!stack.empty ()) {
      auto &[number, next] = stack.back ();
      const auto in = inputs (number);
      if (next < in.size ()) {
        const int input = std::abs (in[next++]);
        if (is_gate (input) &&
            !started[index_of_gate (input, variables_)]) {
          started[index_of_gate (input, variables_)] = 1;
          stack.push_back ({input, 0});
        }
      } else {
        int &d = depth[static_cast<size_t> (number)];
        for (int input : in)
          d = std::max (d, depth[static_cast<size_t> (std::abs (input))]);
        stack.pop_back ();
      }
    }
  }
  return depth;
}

} // namespace miniqu
