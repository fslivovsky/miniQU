// encoding-dump [--prefix] [--count] [--no-early-tseitin] FILE
//
// Parses FILE (QCIR if the name ends in "qcir" or "qcir.gz", else QDIMACS),
// encodes it into the recording fake solver and prints what the solver
// would have been given.  tests/encoding_diff.sh compares the output with
// the original constraints in a proof of the baseline solver.
//
//   o <c|t> <gate> <lits>   one line per constraint; literals are proof
//                           numbers (the user number if a variable has
//                           none), sorted, duplicates removed; constraints
//                           with a literal and its negation are skipped
//   var <n> <e|a> <d|-> <proof>   with --prefix: the variables in order
//   vars N clauses N cubes N literals N   with --count, which keeps nothing
//                           in memory and so works for the largest files

#include "encode.hpp"
#include "fake_solver.hpp"
#include "message.hpp"
#include "parse.hpp"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>

using namespace miniqu;

static bool ends_with (const std::string &s, const char *suffix) {
  const size_t n = strlen (suffix);
  return s.size () >= n && s.compare (s.size () - n, n, suffix) == 0;
}

static void print_prefix () {
  for (const std::string &line : fake_trace ())
    if (line.starts_with ("var"))
      printf ("%s\n", line.c_str ());
}

// The proof number of every user variable that was declared.
static std::vector<int> proof_numbers () {
  std::vector<int> numbers;
  for (const FakeCall &call : fake_calls ()) {
    if (call.type != FakeCall::Type::AddVar)
      continue;
    const size_t v = static_cast<size_t> (call.var);
    if (numbers.size () <= v)
      numbers.resize (v + 1, 0);
    numbers[v] = call.proof_number ? call.proof_number : call.var;
  }
  return numbers;
}

static void print_constraints () {
  const std::vector<int> numbers = proof_numbers ();
  std::vector<int> lits;
  for (const FakeCall &call : fake_calls ()) {
    if (call.type != FakeCall::Type::AddOriginal)
      continue;
    lits.clear ();
    for (int lit : call.lits) {
      const int number = numbers[static_cast<size_t> (std::abs (lit))];
      lits.push_back (lit < 0 ? -number : number);
    }
    std::sort (lits.begin (), lits.end ());
    lits.erase (std::unique (lits.begin (), lits.end ()), lits.end ());
    bool tautology = false;
    for (int lit : lits)
      tautology |=
          lit < 0 && std::binary_search (lits.begin (), lits.end (), -lit);
    if (tautology)
      continue;
    printf ("o %c %d", call.kind == Kind::Clause ? 'c' : 't',
            call.proof_gate);
    for (int lit : lits)
      printf (" %d", lit);
    printf ("\n");
  }
}

int main (int argc, char **argv) {
  bool prefix = false, count = false, early = true;
  const char *path = nullptr;
  for (int i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "--prefix"))
      prefix = true;
    else if (!strcmp (argv[i], "--count"))
      count = true;
    else if (!strcmp (argv[i], "--no-early-tseitin"))
      early = false;
    else if (!path && argv[i][0] != '-')
      path = argv[i];
    else {
      fprintf (stderr, "usage: encoding-dump [--prefix] [--count] "
                       "[--no-early-tseitin] FILE\n");
      return 2;
    }
  }
  if (!path) {
    fprintf (stderr, "encoding-dump: no file\n");
    return 2;
  }
  set_verbosity (0);
  fake_recording = !count;
  Solver solver;
  if (ends_with (path, "qcir") || ends_with (path, "qcir.gz"))
    encode (parse_qcir (path), solver, early);
  else
    encode_qdimacs (parse_qdimacs (path), solver);
  if (count) {
    const FakeCounts &c = fake_counts ();
    printf ("vars %zu clauses %zu cubes %zu literals %zu\n", c.vars,
            c.clauses, c.cubes, c.literals);
    return 0;
  }
  if (prefix)
    print_prefix ();
  print_constraints ();
  return 0;
}
