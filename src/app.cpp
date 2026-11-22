// The 'miniQU' executable (ARCHITECTURE 3.5, 9.5): command line, input,
// limits, signals, result line, exit code and the 'V' line.
//
//   miniQU [options] [input [result]]
//
// The input is QCIR if its name ends in "qcir" or '--qcir' is given, and
// QDIMACS (plain or gzip) otherwise; without an input file QDIMACS is read
// from standard input.  The result file, if named, receives "SAT", "UNSAT"
// or "INDET" (the old binary opened it but only ever wrote "UNSAT" for
// formulas decided while parsing).
//
// stdout carries comment lines "c ..." (at '--verb' >= 1: banner, parser
// summary, statistics), then the result line SATISFIABLE, UNSATISFIABLE or
// INDETERMINATE, then with '--cert' the line "V <literals> 0" over QCIR
// identifiers or QDIMACS numbers.  Exit code 10, 20 or 0 as the old binary;
// errors go to stderr with exit code 1.
//
// Proofs: '--proof=FILE' writes a QLRUP proof (binary with
// '--proofbinary'), only for QCIR input outside mode 2 (checked before
// parsing, with the old message); '--trace=FILE' writes the older trace
// format for any input. Both files are opened here and handed to the solver
// as tracers before the formula is added.  A signal only stops the search;
// the proof is flushed after 'solve' returns (ARCHITECTURE 8.2).

#include "encode.hpp"
#include "logging.hpp"
#include "message.hpp"
#include "miniqu.hpp"
#include "options.hpp"
#include "parse.hpp"
#include "qlrup_tracer.hpp"
#include "resources.hpp"
#include "signal.hpp"
#include "trace_tracer.hpp"
#include "util.hpp"

#include <cstdio>
#include <cstring>
#include <new>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace miniqu {

namespace {

void print_usage () {
  printf ("usage: miniQU [options] [input [result]]\n\n"
          "The input is QCIR if its name ends in 'qcir' (or with --qcir), "
          "else QDIMACS,\n"
          "plain or gzip-compressed; without input QDIMACS is read from "
          "standard input.\n"
          "Options are --name=value, --name (=1) and --no-name (=0); "
          "a single dash and\n"
          "hyphens inside names are accepted (-ccmin-mode=3).\n\n"
          "  --proof=FILE   write a QLRUP proof (QCIR, modes 0 and 1)\n"
          "  --trace=FILE   write a trace in the older format\n\n");
  Options::print_usage (stdout);
}

bool has_prefix (const char *s, const char *prefix) {
  return !strncmp (s, prefix, strlen (prefix));
}

bool ends_with (const std::string &s, const char *suffix) {
  const size_t n = strlen (suffix);
  return s.size () >= n && s.compare (s.size () - n, n, suffix) == 0;
}

// The value of '--NAME=VALUE' or '-NAME=VALUE', if 'arg' is of that form.
std::optional<std::string> file_argument (const char *arg,
                                          const char *name) {
  const std::string prefix = std::string (name) + "=";
  for (const char *dashes : {"--", "-"}) {
    const std::string option = dashes + prefix;
    if (has_prefix (arg, option.c_str ()))
      return std::string (arg + option.size ());
  }
  return std::nullopt;
}

std::unique_ptr<OutputFile> open_output (const std::string &path,
                                         const char *what) {
  auto file = std::make_unique<OutputFile> (path);
  if (!file->is_open ())
    fatal ("could not open %s file '%s'", what, path.c_str ());
  return file;
}

class App {
  Options opts;
  std::vector<std::pair<std::string, int>> given; // in command line order
  std::vector<std::string> files;
  std::optional<std::string> proof_path, trace_path;
  std::optional<Circuit> circuit; // QCIR input: names for the 'V' line

  bool qcir_input () const;
  void parse_arguments (int argc, char **argv);
  void connect_tracers (Solver &) const;
  void read_input (Solver &);
  void print_certificate (const Solver &) const;
  void write_result_file (int result) const;

public:
  int main (int argc, char **argv);
};

void App::parse_arguments (int argc, char **argv) {
  for (int i = 1; i < argc; i++) {
    const char *arg = argv[i];
    if (!strcmp (arg, "-h") || !strcmp (arg, "-help") ||
        !strcmp (arg, "--help")) {
      print_usage ();
      exit (0);
    }
    std::string name;
    int value;
    if (parse_option (arg, name, value)) {
      if (!opts.set (name, value))
        fatal ("invalid option '%s' (unknown name or value out of range; "
               "try '--help')",
               arg);
      given.emplace_back (name, value);
    } else if (auto path = file_argument (arg, "proof"))
      proof_path = *path;
    else if (auto trace = file_argument (arg, "trace"))
      trace_path = *trace;
    else if (arg[0] == '-' && arg[1])
      fatal ("invalid option '%s' (try '--help')", arg);
    else if (files.size () == 2)
      fatal ("too many file arguments: '%s'", arg);
    else
      files.push_back (arg);
  }
}

bool App::qcir_input () const {
  return opts.qcir || (!files.empty () && ends_with (files[0], "qcir"));
}

void App::connect_tracers (Solver &solver) const {
  if (proof_path) {
    if (!qcir_input () || opts.mode == 2)
      fatal ("Proofs are only available for QCIR input in modes 0 and 1.");
    solver.connect_tracer (std::make_unique<QlrupTracer> (
        open_output (*proof_path, "proof"), opts.proofbinary));
  }
  if (trace_path)
    solver.connect_tracer (
        std::make_unique<TraceTracer> (open_output (*trace_path, "trace")));
}

void App::read_input (Solver &solver) {
  const std::string path = files.empty () ? "-" : files[0];
  if (path == "-")
    MSG ("reading QDIMACS from standard input");
  if (qcir_input ()) {
    circuit = parse_qcir (path);
    encode (*circuit, solver, opts.earlytseitin);
  } else
    encode_qdimacs (parse_qdimacs (path), solver);
}

void App::print_certificate (const Solver &solver) const {
  printf ("V");
  for (int lit : solver.certificate ()) {
    const int v = lit < 0 ? -lit : lit;
    printf (" %s", lit < 0 ? "-" : "");
    if (circuit)
      fputs (circuit->name (v).c_str (), stdout);
    else
      printf ("%d", v);
  }
  printf (" 0\n");
}

void App::write_result_file (int result) const {
  if (files.size () < 2)
    return;
  FILE *file = fopen (files[1].c_str (), "w");
  if (!file)
    fatal ("cannot write result file '%s'", files[1].c_str ());
  fputs (result == 10   ? "SAT\n"
         : result == 20 ? "UNSAT\n"
                        : "INDET\n",
         file);
  fclose (file);
}

int App::main (int argc, char **argv) {
  parse_arguments (argc, argv);
  set_verbosity (opts.verb);
#ifdef MINIQU_LOGGING
  set_logging (opts.log);
#endif
  catch_signals ();
  limit_time (opts.cpulim);
  limit_memory (opts.memlim);
  MSG ("miniQU, QCDCL solver for QBF (CaDiCaL-style rewrite)");

  Solver solver;
  for (const auto &[name, value] : given)
    solver.set (name, value);
  connect_tracers (solver);
  read_input (solver);
  MSG ("parsed and encoded in %.2f seconds", process_time ());

  forward_signals (solver);
  const int result = solver.solve ();
  solver.flush_proof ();

  if (verbosity () > 0) {
    solver.statistics ();
    MSG ("%-16s %12.1f MB", "maximum memory:",
         (double) maximum_resident_set_size () / (1 << 20));
  }
  printf ("%s\n", result == 10   ? "SATISFIABLE"
                  : result == 20 ? "UNSATISFIABLE"
                                 : "INDETERMINATE");
  if (opts.cert)
    print_certificate (solver);
  fflush (stdout);
  write_result_file (result);
  return result;
}

} // namespace

} // namespace miniqu

// A failed allocation under '--memlim' ends the run as in the old binary.
// (The arena reports its own failure through 'fatal'.)
int main (int argc, char **argv) {
  try {
    return miniqu::App ().main (argc, argv);
  } catch (const std::bad_alloc &) {
    MSG ("out of memory");
    printf ("INDETERMINATE\n");
    return 0;
  }
}
