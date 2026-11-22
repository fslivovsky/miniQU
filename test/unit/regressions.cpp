// End to end through the real frontend and the real 'Solver': every file
// in tests/regressions is parsed, encoded, propagated at the root in modes
// 0 and 1, and the invariants are checked.  No search yet.

#include "encode.hpp"
#include "internal.hpp"
#include "miniqu.hpp"
#include "parse.hpp"
#include "test.hpp"

#include <filesystem>
#include <string>

using namespace miniqu;

static void check (const std::filesystem::path &path, int mode,
                   bool early_tseitin) {
  Solver solver;
  CHECK (solver.set ("mode", mode));
  if (path.extension () == ".qdimacs")
    encode_qdimacs (parse_qdimacs (path.string ()), solver);
  else
    encode (parse_qcir (path.string ()), solver, early_tseitin);
  Internal &internal = internal_of (solver);
  internal.check_invariants ();
  const std::string name = path.filename ().string ();
  const bool sat = name.find (".sat.") != std::string::npos;
  // A formula decided by the input must be decided correctly.
  if (internal.status != Status::Unknown) {
    CHECK (internal.status == (sat ? Status::True : Status::False));
    return;
  }
  if (internal.propagate () == Ref::none) {
    CHECK_EQ (internal.propagated, internal.trail.size ());
    internal.check_invariants ();
  }
}

int main () {
  size_t files = 0;
  for (const auto &entry :
       std::filesystem::directory_iterator (MINIQU_REGRESSIONS)) {
    const std::filesystem::path &path = entry.path ();
    if (path.extension () != ".qcir" && path.extension () != ".qdimacs")
      continue;
    files++;
    for (int mode : {0, 1})
      for (bool early : {true, false})
        check (path, mode, early);
  }
  CHECK (files >= 7);
  return test_result ();
}
