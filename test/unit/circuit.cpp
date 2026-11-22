#include "circuit.hpp"
#include "test.hpp"

#include <vector>

using namespace miniqu;

using Inputs = std::vector<int>;

static Inputs inputs_of (const Circuit &c, int number) {
  const auto in = c.inputs (number);
  return Inputs (in.begin (), in.end ());
}

// Variables a=1, b=2, c=3 in blocks E{a,b} A{c}.
static Circuit prefix () {
  Circuit c;
  CHECK (c.add_variable (Quant::Exists, "a"));
  CHECK (c.add_variable (Quant::Exists, "b"));
  CHECK (c.add_variable (Quant::Forall, "c"));
  return c;
}

static void test_blocks () {
  Circuit c;
  c.add_variable (Quant::Exists, "free1");
  c.add_variable (Quant::Exists, "e1");
  c.add_variable (Quant::Forall, "u1");
  c.add_variable (Quant::Forall, "u2");
  c.add_variable (Quant::Exists, "e2");
  CHECK_EQ (c.variables (), 5);
  CHECK_EQ (c.blocks ().size (), 3u);
  CHECK (c.blocks ()[0].quant == Quant::Exists);
  CHECK (c.blocks ()[0].first == 1 && c.blocks ()[0].last == 2);
  CHECK (c.blocks ()[1].quant == Quant::Forall);
  CHECK (c.blocks ()[1].first == 3 && c.blocks ()[1].last == 4);
  CHECK (c.blocks ()[2].first == 5 && c.blocks ()[2].last == 5);
  CHECK (!c.add_variable (Quant::Forall, "e1"));
  CHECK_EQ (c.variables (), 5);
  CHECK_EQ (c.name (3), "u1");
}

static void test_numbering () {
  Circuit c = prefix ();
  const int a = c.reference ("a", 1), b = c.reference ("b", 1);
  const int u = c.reference ("c", 1);
  CHECK (a == 1 && b == 2 && u == 3);

  const int g = c.add_gate (GateType::And, "g", std::array{a, -b, u});
  CHECK_EQ (g, 4);
  CHECK (c.is_gate (g) && !c.is_gate (3));
  CHECK (c.gate (g).type == GateType::And);
  CHECK (inputs_of (c, g) == (Inputs{1, -2, 3}));
  CHECK_EQ (c.reference ("g", 2), g);

  // xor (a, b) is and (a, -b), and (-a, b), or of the two; the or gate has
  // the name and the last number.
  const int x = c.add_xor ("x", a, -b);
  CHECK_EQ (x, 7);
  CHECK (c.gate (5).type == GateType::And &&
         c.gate (6).type == GateType::And);
  CHECK (c.gate (7).type == GateType::Or);
  CHECK (inputs_of (c, 5) == (Inputs{1, 2}));
  CHECK (inputs_of (c, 6) == (Inputs{-1, -2}));
  CHECK (inputs_of (c, 7) == (Inputs{5, 6}));
  CHECK_EQ (c.name (5), "");
  CHECK_EQ (c.name (7), "x");

  // ite (c, a, b) is and (c, a), and (-c, b), or of the two.
  const int i = c.add_ite ("i", u, a, -x);
  CHECK_EQ (i, 10);
  CHECK (inputs_of (c, 8) == (Inputs{3, 1}));
  CHECK (inputs_of (c, 9) == (Inputs{-3, -7}));
  CHECK (inputs_of (c, 10) == (Inputs{8, 9}));

  CHECK_EQ (c.gates (), 7);
  CHECK_EQ (c.add_gate (GateType::Or, "g", std::array<int, 0>{}), 0);
  CHECK_EQ (c.add_gate (GateType::Or, "a", std::array<int, 0>{}), 0);
  CHECK_EQ (c.add_xor ("x", a, b), 0);
  CHECK_EQ (c.add_ite ("i", a, b, u), 0);
  CHECK_EQ (c.gates (), 7);

  const int empty = c.add_gate (GateType::Or, "empty", {});
  CHECK_EQ (empty, 11);
  CHECK (c.inputs (empty).empty ());
  CHECK (inputs_of (c, 10) == (Inputs{8, 9}));
}

static void test_forward_references () {
  Circuit c = prefix ();
  // out = and (h, -k) comes first; h and k are defined later.
  const int h = c.reference ("h", 5), k = c.reference ("k", 6);
  CHECK (h > 100 && k > 100 && h != k);
  CHECK_EQ (c.add_gate (GateType::And, "out", std::array{h, -k}), 4);
  CHECK_EQ (c.add_gate (GateType::Or, "k", std::array{1, 2}), 5);
  CHECK_EQ (c.add_gate (GateType::Or, "h", std::array{-1, 3}), 6);
  c.set_output (-c.reference ("out", 7));
  CHECK (!c.resolve ());
  CHECK (inputs_of (c, 4) == (Inputs{6, -5}));
  CHECK_EQ (c.output (), -4);
}

static void test_defects () {
  Circuit c = prefix ();
  const int ghost = c.reference ("ghost", 12);
  c.add_gate (GateType::And, "g", std::array{ghost, 1});
  c.set_output (4);
  auto defect = c.resolve ();
  CHECK (defect && defect->kind == Circuit::Defect::Kind::Undefined);
  CHECK (defect && defect->name == "ghost" && defect->line == 12);

  Circuit d = prefix ();
  const int p = d.reference ("p", 3), q = d.reference ("q", 4);
  d.add_gate (GateType::And, "q", std::array{p, 1});
  d.add_gate (GateType::And, "p", std::array{-q});
  d.set_output (p);
  defect = d.resolve ();
  CHECK (defect && defect->kind == Circuit::Defect::Kind::Cyclic);
  CHECK (defect && (defect->name == "p" || defect->name == "q"));

  Circuit e = prefix ();
  const int self = e.reference ("self", 1);
  e.add_gate (GateType::Or, "self", std::array{self});
  e.set_output (4);
  defect = e.resolve ();
  CHECK (defect && defect->kind == Circuit::Defect::Kind::Cyclic);
  CHECK (defect && defect->name == "self");

  // A cycle through the helper gates of an xor is reported by the xor.
  Circuit f = prefix ();
  const int loop = f.reference ("loop", 1);
  f.add_xor ("loop", 1, loop);
  f.set_output (4);
  defect = f.resolve ();
  CHECK (defect && defect->kind == Circuit::Defect::Kind::Cyclic);
  CHECK (defect && defect->name == "loop");
}

static void test_redundant () {
  Circuit c = prefix ();
  const int g1 = c.add_gate (GateType::And, "g1", std::array{1, 2});
  const int g2 = c.add_gate (GateType::Or, "g2", std::array{g1, 3});
  const int dead1 = c.add_gate (GateType::And, "dead1", std::array{g2, 1});
  const int dead2 = c.add_gate (GateType::Or, "dead2", std::array{dead1});
  const int g3 = c.add_gate (GateType::And, "g3", std::array{-g2, g1});
  c.set_output (g3);
  CHECK (!c.resolve ());
  CHECK_EQ (c.remove_redundant (), 2);
  CHECK (!c.removed (g1) && !c.removed (g2) && !c.removed (g3));
  CHECK (c.removed (dead1) && c.removed (dead2));
  // Removed gates keep numbers and inputs.
  CHECK (inputs_of (c, dead2) == Inputs{dead1});

  Circuit d = prefix ();
  const int g = d.add_gate (GateType::And, "g", std::array{1, 2});
  d.set_output (-3);
  CHECK_EQ (d.remove_redundant (), 1);
  CHECK (d.removed (g));
}

static void test_polarities () {
  Circuit c = prefix ();
  const int g1 = c.add_gate (GateType::And, "g1", std::array{1, 2});   // 4
  const int g2 = c.add_gate (GateType::Or, "g2", std::array{-g1, 3});  // 5
  const int g3 = c.add_gate (GateType::And, "g3", std::array{g1, g2}); // 6
  const int g4 = c.add_gate (GateType::Or, "g4", std::array{-g3, 1});  // 7
  const int g5 = c.add_gate (GateType::And, "g5", std::array{g4, g3}); // 8
  c.set_output (-g5);
  CHECK (!c.resolve ());
  c.remove_redundant ();
  c.compute_polarities ();
  CHECK (c.polarity (g5) == Polarity::Negative);
  CHECK (c.polarity (g4) == Polarity::Negative);
  CHECK (c.polarity (g3) == (Polarity::Positive | Polarity::Negative));
  // g3 is used by g5 directly and by g4 negated, and g2 only by g3.
  CHECK (c.polarity (g2) == Polarity::Both);
  CHECK (c.polarity (g1) == Polarity::Both);
  CHECK (negate (Polarity::Positive) == Polarity::Negative);
  CHECK (negate (Polarity::Both) == Polarity::Both);
  CHECK (negate (Polarity::None) == Polarity::None);

  // Inputs with larger numbers than the gate: a forward reference.
  Circuit f = prefix ();
  const int later = f.reference ("later", 1);
  const int top = f.add_gate (GateType::Or, "top", std::array{-later});
  f.add_gate (GateType::And, "later", std::array{1, 2});
  f.set_output (top);
  CHECK (!f.resolve ());
  f.remove_redundant ();
  f.compute_polarities ();
  CHECK (f.polarity (top) == Polarity::Positive);
  CHECK (f.polarity (5) == Polarity::Negative);
}

static void test_depths () {
  Circuit c;
  c.add_variable (Quant::Exists, "a");
  c.add_variable (Quant::Forall, "u");
  c.add_variable (Quant::Exists, "b");
  c.add_variable (Quant::Exists, "b2");
  const int top = c.add_gate (GateType::And, "top", {});              // 5
  const int ga = c.add_gate (GateType::Or, "ga", std::array{1, top}); // 6
  const int gu = c.add_gate (GateType::And, "gu", std::array{-ga, 2});
  const int gb = c.add_gate (GateType::And, "gb", std::array{gu, 4});
  const int unused = c.add_gate (GateType::Or, "unused", std::array{gb});
  c.set_output (gu);
  CHECK (!c.resolve ());
  c.remove_redundant ();
  CHECK (c.removed (gb) && c.removed (unused));
  const std::vector<int> depth = c.gate_depths ();
  CHECK_EQ (depth.size (), 10u);
  // Blocks: {a}, {u}, {b, b2}.
  CHECK (depth[1] == 0 && depth[2] == 1 && depth[3] == 2 && depth[4] == 2);
  CHECK_EQ (depth[static_cast<size_t> (top)], -1);
  CHECK_EQ (depth[static_cast<size_t> (ga)], 0);
  CHECK_EQ (depth[static_cast<size_t> (gu)], 1);
  // Removed gates are included: they still get variables.
  CHECK_EQ (depth[static_cast<size_t> (gb)], 2);
  CHECK_EQ (depth[static_cast<size_t> (unused)], 2);

  // A long chain does not overflow the stack.
  Circuit chain;
  chain.add_variable (Quant::Exists, "x");
  int last = 1;
  for (int i = 0; i < 1000000; i++)
    last = chain.add_gate (GateType::And, "g" + std::to_string (i),
                           std::array{last});
  chain.set_output (last);
  CHECK (!chain.resolve ());
  CHECK_EQ (chain.remove_redundant (), 0);
  chain.compute_polarities ();
  CHECK_EQ (chain.gate_depths ().back (), 0);
  CHECK (chain.polarity (last) == Polarity::Positive);
}

int main () {
  test_blocks ();
  test_numbering ();
  test_forward_references ();
  test_defects ();
  test_redundant ();
  test_polarities ();
  test_depths ();
  return test_result ();
}
