#include "frontend_test.hpp"
#include "message.hpp"
#include "parse.hpp"
#include "test.hpp"

#include <string>
#include <vector>

using namespace miniqu;

using Inputs = std::vector<int>;

static Inputs inputs_of (const Circuit &c, int number) {
  const auto in = c.inputs (number);
  return Inputs (in.begin (), in.end ());
}

static Circuit parse (const std::string &text) {
  return parse_qcir (write_file ("input.qcir", text));
}

static void test_syntax () {
  // Header, comments, mixed case, blanks everywhere, free, empty gates, a
  // trailing comma, windows line ends, a gate used before its definition.
  const Circuit c = parse ("#QCIR-G14\n"
                           "# a comment\n"
                           "\n"
                           "  FREE ( f )\r\n"
                           "Exists(a,b ,c)\n"
                           "forall (u)\n"
                           "  Output ( -g2 )\n"
                           "g2\t=  OR ( g1 , -u,)\n"
                           "g1=and(a,-b)\n"
                           "e = And()\n"
                           "o2 = or ()\n"
                           "# end\n");
  CHECK_EQ (c.variables (), 5);
  CHECK_EQ (c.blocks ().size (), 2u);
  CHECK (c.blocks ()[0].quant == Quant::Exists && c.blocks ()[0].last == 4);
  CHECK (c.blocks ()[1].quant == Quant::Forall &&
         c.blocks ()[1].first == 5);
  CHECK_EQ (c.name (1), "f");
  CHECK_EQ (c.name (5), "u");
  CHECK_EQ (c.gates (), 4);
  CHECK_EQ (c.name (6), "g2");
  CHECK_EQ (c.name (7), "g1");
  CHECK (inputs_of (c, 6) == (Inputs{7, -5}));
  CHECK (inputs_of (c, 7) == (Inputs{2, -3}));
  CHECK (c.gate (6).type == GateType::Or &&
         c.gate (7).type == GateType::And);
  CHECK (c.inputs (8).empty () && c.inputs (9).empty ());
  CHECK_EQ (c.output (), -6);
  // e and o2 are not in the cone of the output.
  CHECK (c.removed (8) && c.removed (9));
  CHECK (!c.removed (6) && !c.removed (7));
  CHECK (c.polarity (6) == Polarity::Negative);
  CHECK (c.polarity (7) == Polarity::Negative);
}

static void test_expansion () {
  const Circuit c = parse ("exists(a, b)\n"
                           "forall(u)\n"
                           "output(i)\n"
                           "x = xor(a, -b)\n"
                           "i = ite(u, x, b)\n");
  // x: and (a, b), and (-a, -b), or;  i: and (u, x), and (-u, b), or
  CHECK_EQ (c.gates (), 6);
  CHECK (inputs_of (c, 4) == (Inputs{1, 2}));
  CHECK (inputs_of (c, 5) == (Inputs{-1, -2}));
  CHECK (inputs_of (c, 6) == (Inputs{4, 5}));
  CHECK (inputs_of (c, 7) == (Inputs{3, 6}));
  CHECK (inputs_of (c, 8) == (Inputs{-3, 2}));
  CHECK (inputs_of (c, 9) == (Inputs{7, 8}));
  CHECK_EQ (c.output (), 9);
  CHECK_EQ (c.name (6), "x");
  CHECK_EQ (c.name (9), "i");
}

static void test_cone () {
  const Circuit c = parse ("exists(a)\n"
                           "output(a)\n"
                           "g = and(a)\n");
  CHECK (c.removed (2));
  const Circuit gz =
      parse_qcir (write_gzip ("input.qcir.gz", "exists(a)\noutput(-a)\n"));
  CHECK_EQ (gz.output (), -1);
}

static void test_long_line () {
  std::string text = "exists(a)\noutput(g)\ng = and(a";
  for (int i = 0; i < 1000000; i++)
    text += ",a";
  const Circuit c = parse (text + ")\n");
  CHECK_EQ (c.inputs (2).size (), 1000001u);
}

static void expect_error (const std::string &text,
                          const std::string &message) {
  const std::string path = write_file ("bad.qcir", text);
  CHECK (dies_with ([&] { parse_qcir (path); }, message));
}

static void test_errors () {
  expect_error ("exists(a)\noutput(g)\n",
                "bad.qcir:2: identifier 'g' is neither");
  expect_error ("exists(a)\noutput(a)\n\nh = and(a, zzz)\n",
                "bad.qcir:4: identifier 'zzz' is neither");
  expect_error ("exists(a)\noutput(a)\ng = and(a)\ng = or(a)\n",
                "bad.qcir:4: identifier 'g' is already defined");
  expect_error ("exists(a)\noutput(a)\na = and()\n",
                "bad.qcir:3: identifier 'a' is already defined");
  expect_error ("exists(a)\nforall(b, a)\noutput(a)\n",
                "bad.qcir:2: variable 'a' is already defined");
  expect_error ("exists(a)\noutput(a)\ng = xor(a, a, a)\n",
                "bad.qcir:3: xor takes 2 inputs, not 3");
  expect_error ("exists(a)\noutput(a)\ng = ite(a, a)\n",
                "bad.qcir:3: ite takes 3 inputs, not 2");
  expect_error ("exists(a)\noutput(a)\ng = nand(a)\n",
                "bad.qcir:3: unknown gate type 'nand'");
  expect_error ("exists(a)\n", "bad.qcir: missing output statement");
  expect_error ("", "bad.qcir: missing output statement");
  expect_error ("exists(a)\noutput(a)\noutput(a)\n",
                "bad.qcir:3: repeated output statement");
  expect_error ("exists(a)\noutput(a, a)\n",
                "bad.qcir:2: output takes exactly one literal");
  expect_error ("exists(a)\noutput()\n",
                "bad.qcir:2: output takes exactly one literal");
  expect_error ("exists(a)\noutput(-)\n",
                "bad.qcir:2: identifier expected");
  expect_error ("exists(a)\ng = and(a)\nforall(b)\noutput(g)\n",
                "bad.qcir:3: quantifier statement after a gate definition");
  expect_error ("exists(a)\noutput a\n", "bad.qcir:2: malformed line");
  expect_error ("exists(a)\n= and(a)\n", "bad.qcir:2: malformed line");
  expect_error ("exists(a)\n(a)\n", "bad.qcir:2: malformed line");
  expect_error ("exists(a)\nmax(a)\n",
                "bad.qcir:2: unknown statement 'max'");
  expect_error ("exists(a\noutput(a)\n", "bad.qcir:1: expected ',' or ')'");
  expect_error ("exists(a b)\n", "bad.qcir:1: expected ',' or ')'");
  expect_error ("exists(a)\noutput(a) x\n",
                "bad.qcir:2: unexpected characters after ')'");
  expect_error ("exists(a)\noutput(a)\ng = and(a,,a)\n",
                "bad.qcir:3: identifier expected");
  expect_error ("exists(a)\noutput(a)\ng = and(,a)\n",
                "bad.qcir:3: identifier expected");
  expect_error ("exists(a,,b)\n", "bad.qcir:1: identifier expected");
  expect_error ("exists(--a)\n", "bad.qcir:1: identifier '--a' must not");
  expect_error ("exists(a)\noutput(a)\ng = and(--a)\n",
                "bad.qcir:3: identifier '-a' must not");
  expect_error ("exists(a)\noutput(a)\n-g = and(a)\n",
                "bad.qcir:3: identifier '-g' must not");
  expect_error ("exists(a)\noutput(a)\ng and(a)\n",
                "bad.qcir:3: malformed line");
  expect_error ("exists(a)\noutput(a)\ng = and a\n",
                "bad.qcir:3: '(' expected after 'and'");
  expect_error ("exists(a)\noutput(g)\ng = and(h, a)\nh = or(g)\n",
                "depends on itself");
  expect_error ("exists(a)\noutput(g)\ng = and(g)\n",
                "'g' depends on itself");
  const std::string missing = temp_dir () + "/no-such-file.qcir";
  CHECK (dies_with ([&] { parse_qcir (missing); }, "cannot open"));
}

int main () {
  set_verbosity (0);
  test_syntax ();
  test_expansion ();
  test_cone ();
  test_long_line ();
  test_errors ();
  return test_result ();
}
