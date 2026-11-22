#include "frontend_test.hpp"
#include "message.hpp"
#include "parse.hpp"
#include "test.hpp"

#include <string>
#include <vector>

using namespace miniqu;

using Ints = std::vector<int>;

static const std::string formula = "c a comment\n"
                                   "c another\n"
                                   "p cnf 6 3\n"
                                   "a 1 2 0\n"
                                   "e 3\n"
                                   "  4 0\n"
                                   "a 5 0\n"
                                   "1 -3 0\n"
                                   "-2 4\n"
                                   "5 0\n"
                                   "0\n";

static void check_formula (const Qdimacs &q, size_t blocks) {
  CHECK_EQ (q.blocks.size (), blocks);
  const size_t first = q.blocks.size () - 3;
  CHECK (q.blocks[first].quant == Quant::Forall);
  CHECK (q.blocks[first].variables == (Ints{1, 2}));
  CHECK (q.blocks[first + 1].quant == Quant::Exists);
  CHECK (q.blocks[first + 1].variables == (Ints{3, 4}));
  CHECK (q.blocks[first + 2].quant == Quant::Forall);
  CHECK (q.blocks[first + 2].variables == Ints{5});
  CHECK_EQ (q.clauses, 3u);
  // The last clause is the empty one.
  CHECK (q.literals == (Ints{1, -3, 0, -2, 4, 5, 0, 0}));
}

static void test_formats () {
  check_formula (parse_qdimacs (write_file ("a.qdimacs", formula)), 3);
  check_formula (parse_qdimacs (write_gzip ("a.qdimacs.gz", formula)), 3);
  // Without a header, with quantifier lines between clauses.
  const Qdimacs q =
      parse_qdimacs (write_file ("b.qdimacs", "e 1 0\n1 0\na 2 0\n"));
  CHECK_EQ (q.blocks.size (), 2u);
  CHECK_EQ (q.clauses, 1u);
  const Qdimacs empty =
      parse_qdimacs (write_file ("c.qdimacs", "p cnf 0 0\n"));
  CHECK (empty.blocks.empty () && empty.literals.empty ());
}

static void test_free_variables () {
  // 7 and 9 are used without being quantified; 8 is not used at all.
  const Qdimacs q = parse_qdimacs (
      write_file ("d.qdimacs", "a 1 0\ne 2 0\n9 -1 7 0\n-2 8 0\n"));
  CHECK_EQ (q.blocks.size (), 3u);
  CHECK (q.blocks[0].quant == Quant::Exists);
  CHECK (q.blocks[0].variables == (Ints{7, 8, 9}));
  CHECK (q.blocks[1].quant == Quant::Forall);
  CHECK (q.blocks[2].variables == Ints{2});
}

static void expect_error (const std::string &text,
                          const std::string &message) {
  const std::string path = write_file ("bad.qdimacs", text);
  CHECK (dies_with ([&] { parse_qdimacs (path); }, message));
}

static void test_errors () {
  expect_error ("p dnf 1 1\n", "bad.qdimacs:1: 'p cnf' expected");
  expect_error ("p cnf -1 1\n", "negative number in the header");
  expect_error ("e 1 1 0\n",
                "bad.qdimacs:1: variable 1 is quantified more than once");
  expect_error ("e 1 0\na 1 0\n",
                "bad.qdimacs:2: variable 1 is quantified more than once");
  expect_error ("e -1 0\n", "negative variable -1 in the prefix");
  expect_error ("e 1 0\n1 2\n", "number expected");
  expect_error ("e 1 0\n1 x 0\n", "bad.qdimacs:2: number expected");
  expect_error ("e 1 0\n99999999999 0\n", "number out of range");
  const std::string missing = temp_dir () + "/no-such-file.qdimacs";
  CHECK (dies_with ([&] { parse_qdimacs (missing); }, "cannot open"));
}

int main () {
  set_verbosity (0);
  test_formats ();
  test_free_variables ();
  test_errors ();
  return test_result ();
}
