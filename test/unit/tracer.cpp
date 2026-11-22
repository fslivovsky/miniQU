// The proof writers (qlrup_tracer.cpp, trace_tracer.cpp): a fixed list of
// steps against the bytes doc/proof-format.md prescribes, which are also
// the bytes the old solver wrote.

#include "child.hpp"
#include "qlrup_tracer.hpp"
#include "test.hpp"
#include "trace_tracer.hpp"

#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iterator>
#include <memory>
#include <string>
#include <unistd.h>

using namespace miniqu;

static std::string directory () {
  const char *tmp = getenv ("TMPDIR");
  std::string dir = std::string (tmp ? tmp : "/tmp") + "/miniqu-XXXXXX";
  CHECK (mkdtemp (dir.data ()) != nullptr);
  return dir;
}

static std::string slurp (const std::string &path) {
  std::ifstream in (path, std::ios::binary);
  return {std::istreambuf_iterator<char> (in),
          std::istreambuf_iterator<char> ()};
}

// Ids and literals above 127 need two bytes in the binary encoding.
static void write_steps (Tracer &tracer) {
  const int original[] = {1, -3}, derived[] = {-70};
  const uint64_t chain[] = {1, 2}, empty_chain[] = {130};
  tracer.add_original (1, Kind::Clause, 3, original);
  tracer.add_derived (130, Kind::Cube, derived, chain);
  tracer.delete_constraint (1, Kind::Clause, original);
  tracer.add_derived (131, Kind::Clause, {}, empty_chain);
  tracer.flush ();
}

static std::string written (const std::string &path, bool binary) {
  QlrupTracer tracer (std::make_unique<OutputFile> (path), binary);
  write_steps (tracer);
  return slurp (path);
}

static void test_text (const std::string &dir) {
  CHECK_EQ (written (dir + "/p.txt", false),
            std::string ("o 1 c 3 1 -3 0 \n"
                         "130 t -70 0 1 2 0 \n"
                         "d 1 0 \n"
                         "131 c 0 130 0 \n"));
}

static void test_binary (const std::string &dir) {
  // 1 -> 2, -3 -> 7, -70 -> 141 = 0x8d 0x01, 130 = 0x82 0x01.
  const unsigned char expected[] = {
      'Q', 'L',  'R', 'U', 'P',  'b',  '1', '\n',       //
      'o', 1,    0,   3,   2,    7,    0,               //
      'a', 0x82, 1,   1,   0x8d, 1,    0,   1,    2, 0, //
      'd', 1,    0,                                     //
      'a', 0x83, 1,   0,   0,    0x82, 1,   0};
  CHECK_EQ (written (dir + "/p.bin", true),
            std::string ((const char *) expected, sizeof expected));
}

static void test_trace (const std::string &dir) {
  const std::string path = dir + "/t.trace";
  {
    TraceTracer tracer (std::make_unique<OutputFile> (path));
    write_steps (tracer);
    const int cube[] = {4, -5};
    tracer.add_model_cube (132, cube);
  }
  CHECK_EQ (slurp (path), std::string ("1 0 1 -3 0 0\n"
                                       "130 1 -70 0 1 2 0 \n"
                                       "131 0 0 130 0 \n"
                                       "132 1 4 -5 0 0\n"));
}

// An initial cube from a model has no QLRUP derivation.
static void test_model_cube (const std::string &dir) {
  CHECK (dies_with (
      [&] {
        QlrupTracer tracer (std::make_unique<OutputFile> (dir + "/m.txt"),
                            false);
        const int cube[] = {1};
        tracer.add_model_cube (1, cube);
      },
      "Proof logging does not support terms obtained from satisfying "
      "assignments."));
}

int main () {
  const std::string dir = directory ();
  test_text (dir);
  test_binary (dir);
  test_trace (dir);
  test_model_cube (dir);
  for (const char *file : {"p.txt", "p.bin", "t.trace", "m.txt"})
    unlink ((dir + "/" + file).c_str ());
  rmdir (dir.c_str ());
  return test_result ();
}
