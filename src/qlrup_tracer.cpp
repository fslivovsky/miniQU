// The QLRUP writer (doc/proof-format.md; the old 'proofNumber',
// 'proofLits', 'proofOriginal', 'proofDerived', 'proofDelete').
//
// Text: every number, literal and type letter is followed by one space and
// every step ends with "0 " and a newline, so that a line reads
//
//   o 3 c 7 -7 2 0 \n        4 c -7 0 3 0 \n        d 3 0 \n
//
// Binary: the magic line "QLRUPb1\n", then per step the byte 'o', 'a' or
// 'd' and the numbers as variable-length unsigned integers (seven bits per
// byte, least significant group first), a literal l as 2*|l| + (l < 0),
// the type as 0 (clause) or 1 (term).  Both are what the old solver wrote
// for the same steps, so 'qlrup-trim', 'tests/qlrup_check.py' and the Lean
// checker read them unchanged.

#include "qlrup_tracer.hpp"
#include "message.hpp"

#include <cstdlib>

namespace miniqu {

QlrupTracer::QlrupTracer (std::unique_ptr<OutputFile> f, bool b)
    : file (std::move (f)), binary (b) {
  if (binary)
    file->put ("QLRUPb1\n");
}

void QlrupTracer::number (uint64_t n) {
  if (binary) {
    for (; n >= 128; n >>= 7)
      file->put_byte (static_cast<uint8_t> ((n & 127) | 128));
    file->put_byte (static_cast<uint8_t> (n));
    return;
  }
  file->put_decimal (n);
  file->put_byte (' ');
}

void QlrupTracer::literals (std::span<const int> lits) {
  for (int lit : lits)
    if (binary)
      number (2 * static_cast<uint64_t> (std::abs (lit)) +
              (lit < 0 ? 1u : 0u));
    else {
      file->put_decimal (int64_t{lit});
      file->put_byte (' ');
    }
  number (0);
}

void QlrupTracer::kind (Kind k) {
  if (binary)
    number (index (k));
  else
    file->put (k == Kind::Clause ? "c " : "t ");
}

void QlrupTracer::end_of_step () {
  number (0);
  if (!binary)
    file->put_byte ('\n');
}

void QlrupTracer::add_original (uint64_t id, Kind k, int gate,
                                std::span<const int> lits) {
  file->put (binary ? "o" : "o ");
  number (id);
  kind (k);
  number (static_cast<uint64_t> (gate));
  literals (lits);
  if (!binary)
    file->put_byte ('\n');
}

void QlrupTracer::add_derived (uint64_t id, Kind k,
                               std::span<const int> lits,
                               std::span<const uint64_t> chain) {
  if (binary)
    file->put_byte ('a');
  number (id);
  kind (k);
  literals (lits);
  for (uint64_t premise : chain)
    number (premise);
  end_of_step ();
}

void QlrupTracer::delete_constraint (uint64_t id, Kind,
                                     std::span<const int>) {
  file->put (binary ? "d" : "d ");
  number (id);
  end_of_step ();
}

void QlrupTracer::add_model_cube (uint64_t, std::span<const int>) {
  fatal ("Proof logging does not support terms obtained from satisfying "
         "assignments.");
}

void QlrupTracer::flush () { file->flush (); }

} // namespace miniqu
