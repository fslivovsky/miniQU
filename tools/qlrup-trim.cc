// qlrup-trim: backward trimming of QLRUP proofs (miniQU proof format).
//
// Usage: qlrup-trim [--binary|--text] [--keep-ids|--renumber] [--quiet] INPUT OUTPUT
//
// The tool is purely syntactic.  Pass 1 reads the proof, remembers for every
// original / derived step only (id, kind, antecedents as step indices) and
// finds the first derived step without literals (the conclusion).  A backward
// sweep marks everything the conclusion depends on.  Pass 2 streams the input a
// second time and writes the marked steps, each followed by a deletion step for
// the antecedents that it uses for the last time.  Literals are never kept in
// memory.
//
// Identifier reuse: pass 1 keeps a hash table id -> index of the live step
// defining it; derived steps resolve their antecedents through it at the moment
// they are read (i.e. to the most recent earlier definition), a definition
// overwrites the entry and a deletion of the input removes it.  Antecedents are
// stored as step indices, so later reuse of an id is harmless.

#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <stdexcept>
#include <string>
#include <vector>

#include <unistd.h>

namespace {

using u8 = uint8_t;
using u32 = uint32_t;
using u64 = uint64_t;
using i64 = int64_t;

const char MAGIC[8] = {'Q', 'L', 'R', 'U', 'P', 'b', '1', '\n'};
const u64 MAX_ID = (u64(1) << 62);   // ids and gate numbers must be below this
const u64 MAX_VAR = (u64(1) << 62);  // literal magnitudes must be below this

struct ParseError : std::runtime_error {
  using std::runtime_error::runtime_error;
};

// ---------------------------------------------------------------- input ----

class Input {
 public:
  explicit Input(const std::string& path) : buf_(1 << 20) {
    f_ = fopen(path.c_str(), "rb");
    if (!f_) throw std::runtime_error("cannot open '" + path + "': " + strerror(errno));
  }
  ~Input() {
    if (f_) fclose(f_);
  }
  Input(const Input&) = delete;
  Input& operator=(const Input&) = delete;

  int get() {
    if (pos_ == len_ && !refill()) return -1;
    return buf_[pos_++];
  }
  int peek() {
    if (pos_ == len_ && !refill()) return -1;
    return buf_[pos_];
  }
  u64 offset() const { return base_ + pos_; }

 private:
  bool refill() {
    base_ += len_;
    pos_ = len_ = 0;
    len_ = fread(buf_.data(), 1, buf_.size(), f_);
    if (len_ == 0) {
      if (ferror(f_)) throw std::runtime_error("read error");
      return false;
    }
    return true;
  }
  FILE* f_ = nullptr;
  std::vector<unsigned char> buf_;
  size_t pos_ = 0, len_ = 0;
  u64 base_ = 0;
};

enum Kind : u8 { ORIG = 0, DER = 1, DEL = 2 };

struct Step {
  Kind kind = ORIG;
  u64 id = 0;
  int term = 0;  // 0 clause, 1 term
  u64 gate = 0;
  std::vector<i64> lits;
  std::vector<u64> ants;  // antecedents for DER, identifiers for DEL
};

class Parser {
 public:
  Parser(const std::string& path, bool binary) : in_(path), binary_(binary) {
    if (binary_) {
      for (int i = 0; i < 8; i++)
        if (in_.get() != (unsigned char)MAGIC[i]) fail("bad binary header");
    }
  }

  // Returns false at a clean end of file.
  bool next(Step& s) { return binary_ ? nextBinary(s) : nextText(s); }

  u64 offset() const { return in_.offset(); }

 private:
  Input in_;
  bool binary_;
  u64 line_ = 1;
  u64 stepOff_ = 0;

  [[noreturn]] void fail(const std::string& msg) {
    std::string m = "parse error at byte offset " + std::to_string(in_.offset());
    if (!binary_) m += " (line " + std::to_string(line_) + ")";
    m += ": " + msg;
    if (stepOff_ || !binary_) m += " [step starting at byte " + std::to_string(stepOff_) + "]";
    throw ParseError(m);
  }

  // ---- binary ----
  u64 varint() {
    u64 v = 0;
    int shift = 0;
    for (;;) {
      int c = in_.get();
      if (c < 0) fail("unexpected end of file (truncated proof)");
      if (shift == 63 && (c & 0x7f) > 1) fail("number overflows 64 bits");
      v |= u64(c & 0x7f) << shift;
      if (!(c & 0x80)) return v;
      shift += 7;
      if (shift > 63) fail("number overflows 64 bits");
    }
  }
  u64 binId() {
    u64 v = varint();
    if (v == 0) fail("zero identifier");
    if (v >= MAX_ID) fail("identifier too large");
    return v;
  }
  void binLits(std::vector<i64>& lits) {
    for (;;) {
      u64 v = varint();
      if (v == 0) return;
      if (v == 1) fail("invalid literal encoding (variable 0)");
      if ((v >> 1) >= MAX_VAR) fail("literal too large");
      i64 m = (i64)(v >> 1);
      lits.push_back((v & 1) ? -m : m);
    }
  }
  void binIds(std::vector<u64>& ids) {
    for (;;) {
      u64 v = varint();
      if (v == 0) return;
      if (v >= MAX_ID) fail("identifier too large");
      ids.push_back(v);
    }
  }
  bool nextBinary(Step& s) {
    s.lits.clear();
    s.ants.clear();
    stepOff_ = in_.offset();
    int c = in_.get();
    if (c < 0) return false;
    if (c == 'o' || c == 'a') {
      s.kind = c == 'o' ? ORIG : DER;
      s.id = binId();
      u64 t = varint();
      if (t > 1) fail("invalid constraint type (expected 0 or 1)");
      s.term = (int)t;
      s.gate = 0;
      if (c == 'o') {
        s.gate = varint();
        if (s.gate >= MAX_ID) fail("gate number too large");
      }
      binLits(s.lits);
      if (c == 'a') {
        binIds(s.ants);
        if (s.ants.empty()) fail("derived step without antecedents");
      }
    } else if (c == 'd') {
      s.kind = DEL;
      s.id = 0;
      binIds(s.ants);
    } else {
      stepOff_ = in_.offset() - 1;
      fail(std::string("unknown step tag 0x") + hex(c));
    }
    return true;
  }
  static std::string hex(int c) {
    const char* d = "0123456789abcdef";
    std::string r;
    r += d[(c >> 4) & 15];
    r += d[c & 15];
    return r;
  }

  // ---- text ----
  static bool isBlank(int c) { return c == ' ' || c == '\t' || c == '\r'; }
  void skipBlanks() {
    while (isBlank(in_.peek())) in_.get();
  }
  // Reads a possibly signed integer token on the current line.
  // Returns magnitude and sets neg.
  u64 textNumber(bool allowNeg, bool& neg) {
    skipBlanks();
    int c = in_.peek();
    if (c < 0 || c == '\n') fail("unexpected end of line (missing 0 terminator?)");
    neg = false;
    if (c == '-') {
      if (!allowNeg) fail("unexpected '-'");
      neg = true;
      in_.get();
      c = in_.peek();
    }
    if (c < '0' || c > '9') fail("expected a number");
    u64 v = 0;
    while ((c = in_.peek()) >= '0' && c <= '9') {
      in_.get();
      u64 d = (u64)(c - '0');
      if (v > (UINT64_MAX - d) / 10) fail("number overflows 64 bits");
      v = v * 10 + d;
    }
    if (c >= 0 && c != '\n' && !isBlank(c)) fail("unexpected character in number");
    return v;
  }
  u64 textId(bool allowZero = false) {
    bool neg;
    u64 v = textNumber(false, neg);
    if (v == 0 && !allowZero) fail("zero identifier");
    if (v >= MAX_ID) fail("number too large");
    return v;
  }
  void textLits(std::vector<i64>& lits) {
    for (;;) {
      bool neg;
      u64 v = textNumber(true, neg);
      if (v == 0) {
        if (neg) fail("'-0' is not a valid literal");
        return;
      }
      if (v >= MAX_VAR) fail("literal too large");
      lits.push_back(neg ? -(i64)v : (i64)v);
    }
  }
  void textIds(std::vector<u64>& ids) {
    for (;;) {
      u64 v = textId(true);
      if (v == 0) return;
      ids.push_back(v);
    }
  }
  int textType() {
    skipBlanks();
    int c = in_.get();
    if (c != 'c' && c != 't') fail("expected constraint type 'c' or 't'");
    int n = in_.peek();
    if (n >= 0 && n != '\n' && !isBlank(n)) fail("expected constraint type 'c' or 't'");
    return c == 't';
  }
  void expectEol() {
    skipBlanks();
    int c = in_.get();
    if (c == '\n') {
      line_++;
      return;
    }
    if (c >= 0) fail("unexpected trailing characters after step");
  }
  bool nextText(Step& s) {
    s.lits.clear();
    s.ants.clear();
    for (;;) {
      int c = in_.peek();
      if (c < 0) return false;
      if (c == '\n') {
        in_.get();
        line_++;
      } else if (isBlank(c)) {
        in_.get();
      } else if (c == '#') {
        while ((c = in_.peek()) >= 0 && c != '\n') in_.get();
      } else {
        break;
      }
    }
    stepOff_ = in_.offset();
    int c = in_.peek();
    if (c == 'o' || c == 'd') {
      in_.get();
      int n = in_.peek();
      if (n >= 0 && n != '\n' && !isBlank(n)) fail("unknown step type");
      if (c == 'o') {
        s.kind = ORIG;
        s.id = textId();
        s.term = textType();
        s.gate = textId(true);
        textLits(s.lits);
      } else {
        s.kind = DEL;
        s.id = 0;
        textIds(s.ants);
      }
    } else if (c >= '0' && c <= '9') {
      s.kind = DER;
      s.id = textId();
      s.term = textType();
      s.gate = 0;
      textLits(s.lits);
      textIds(s.ants);
      if (s.ants.empty()) fail("derived step without antecedents");
    } else {
      fail("unknown step type (expected 'o', 'd' or a number)");
    }
    expectEol();
    return true;
  }
};

// --------------------------------------------------------------- output ----

class Output {
 public:
  Output(const std::string& path, bool binary) : binary_(binary), buf_(1 << 20) {
    f_ = fopen(path.c_str(), "wb");
    if (!f_) throw std::runtime_error("cannot create '" + path + "': " + strerror(errno));
    if (binary_) write(MAGIC, 8);
  }
  ~Output() {
    if (f_) fclose(f_);
  }
  void close() {
    flush();
    if (fclose(f_) != 0) {
      f_ = nullptr;
      throw std::runtime_error("write error on output file");
    }
    f_ = nullptr;
  }
  u64 bytes() const { return total_ + n_; }

  void step(const Step& s, u64 id, const std::vector<u64>& antIds) {
    // antIds: output identifiers of the antecedents (DER only)
    if (binary_) {
      byte(s.kind == ORIG ? 'o' : 'a');
      varint(id);
      varint((u64)s.term);
      if (s.kind == ORIG) varint(s.gate);
      for (i64 l : s.lits) varint(l < 0 ? (u64(-l) << 1) | 1 : u64(l) << 1);
      varint(0);
      if (s.kind == DER) {
        for (u64 a : antIds) varint(a);
        varint(0);
      }
    } else {
      if (s.kind == ORIG) {
        byte('o');
        byte(' ');
        dec(id);
        byte(' ');
        byte(s.term ? 't' : 'c');
        byte(' ');
        dec(s.gate);
        byte(' ');
      } else {
        dec(id);
        byte(' ');
        byte(s.term ? 't' : 'c');
        byte(' ');
      }
      for (i64 l : s.lits) {
        if (l < 0) {
          byte('-');
          dec(u64(-l));
        } else {
          dec(u64(l));
        }
        byte(' ');
      }
      byte('0');
      if (s.kind == DER) {
        byte(' ');
        for (u64 a : antIds) {
          dec(a);
          byte(' ');
        }
        byte('0');
      }
      byte('\n');
    }
  }
  void deletion(const std::vector<u64>& ids) {
    if (binary_) {
      byte('d');
      for (u64 a : ids) varint(a);
      varint(0);
    } else {
      byte('d');
      byte(' ');
      for (u64 a : ids) {
        dec(a);
        byte(' ');
      }
      byte('0');
      byte('\n');
    }
  }

 private:
  bool binary_;
  FILE* f_ = nullptr;
  std::vector<char> buf_;
  size_t n_ = 0;
  u64 total_ = 0;

  void flush() {
    if (n_ && fwrite(buf_.data(), 1, n_, f_) != n_) throw std::runtime_error("write error on output file");
    total_ += n_;
    n_ = 0;
  }
  void write(const void* p, size_t k) {
    const char* c = (const char*)p;
    for (size_t i = 0; i < k; i++) byte(c[i]);
  }
  void byte(int c) {
    if (n_ + 32 > buf_.size()) flush();
    buf_[n_++] = (char)c;
  }
  void varint(u64 v) {
    if (n_ + 32 > buf_.size()) flush();
    while (v >= 0x80) {
      buf_[n_++] = (char)(v | 0x80);
      v >>= 7;
    }
    buf_[n_++] = (char)v;
  }
  void dec(u64 v) {
    if (n_ + 32 > buf_.size()) flush();
    char tmp[24];
    int k = 0;
    do {
      tmp[k++] = (char)('0' + v % 10);
      v /= 10;
    } while (v);
    while (k) buf_[n_++] = tmp[--k];
  }
};

// ---------------------------------------------------- id -> step index ----

// Open addressing hash table with linear probing and tombstones.
class IdMap {
 public:
  IdMap() { alloc(1 << 12); }
  void set(u64 id, u32 val) {
    if ((used_ + 1) * 2 > cap_) rehash();
    size_t i = find(id);
    if (keys_[i] == id) {
      vals_[i] = val;
      return;
    }
    // find returns the first tombstone or empty slot on a miss
    if (keys_[i] == EMPTY) used_++;
    keys_[i] = id;
    vals_[i] = val;
    live_++;
  }
  bool get(u64 id, u32& val) const {
    size_t i = find(id);
    if (keys_[i] != id) return false;
    val = vals_[i];
    return true;
  }
  void erase(u64 id) {
    size_t i = find(id);
    if (keys_[i] != id) return;
    keys_[i] = TOMB;
    live_--;
  }

 private:
  static constexpr u64 EMPTY = 0, TOMB = UINT64_MAX;
  std::vector<u64> keys_;
  std::vector<u32> vals_;
  size_t cap_ = 0, used_ = 0, live_ = 0;  // used_ = live + tombstones

  void alloc(size_t cap) {
    cap_ = cap;
    keys_.assign(cap, EMPTY);
    vals_.assign(cap, 0);
    used_ = live_ = 0;
  }
  size_t hash(u64 id) const {
    id *= 0x9E3779B97F4A7C15ull;
    return (size_t)(id >> 20) & (cap_ - 1);
  }
  // Slot holding id, else the first tombstone on the probe path, else the empty slot.
  size_t find(u64 id) const {
    size_t i = hash(id);
    size_t tomb = (size_t)-1;
    for (;;) {
      u64 k = keys_[i];
      if (k == id) return i;
      if (k == EMPTY) return tomb != (size_t)-1 ? tomb : i;
      if (k == TOMB && tomb == (size_t)-1) tomb = i;
      i = (i + 1) & (cap_ - 1);
    }
  }
  void rehash() {
    std::vector<u64> ok;
    std::vector<u32> ov;
    ok.swap(keys_);
    ov.swap(vals_);
    size_t ocap = cap_;
    size_t ncap = cap_;
    if (live_ * 4 > cap_) ncap = cap_ * 2;  // grow only when really full of live ids
    alloc(ncap);
    for (size_t i = 0; i < ocap; i++)
      if (ok[i] != EMPTY && ok[i] != TOMB) {
        size_t j = hash(ok[i]);
        while (keys_[j] != EMPTY) j = (j + 1) & (cap_ - 1);
        keys_[j] = ok[i];
        vals_[j] = ov[i];
        used_++;
        live_++;
      }
  }
};

// ----------------------------------------------------------------- main ----

[[noreturn]] void usage(int code) {
  fprintf(stderr,
          "usage: qlrup-trim [--binary|--text] [--keep-ids|--renumber] [--quiet] INPUT OUTPUT\n"
          "  Backward-trims a QLRUP proof: keeps only the steps the first empty derived\n"
          "  constraint depends on and inserts deletion steps after last uses.\n");
  exit(code);
}

bool detectBinary(const std::string& path) {
  FILE* f = fopen(path.c_str(), "rb");
  if (!f) throw std::runtime_error("cannot open '" + path + "': " + strerror(errno));
  char h[8];
  size_t n = fread(h, 1, 8, f);
  fclose(f);
  return n == 8 && memcmp(h, MAGIC, 8) == 0;
}

int run(int argc, char** argv) {
  int outFmt = -1;  // -1 same as input, 0 text, 1 binary
  bool renumber = false, quiet = false;
  std::vector<std::string> files;
  for (int i = 1; i < argc; i++) {
    std::string a = argv[i];
    if (a == "--binary") outFmt = 1;
    else if (a == "--text") outFmt = 0;
    else if (a == "--keep-ids") renumber = false;
    else if (a == "--renumber") renumber = true;
    else if (a == "--quiet") quiet = true;
    else if (a == "-h" || a == "--help") usage(0);
    else if (a.size() > 1 && a[0] == '-') {
      fprintf(stderr, "qlrup-trim: unknown option '%s'\n", a.c_str());
      usage(2);
    } else files.push_back(a);
  }
  if (files.size() != 2) usage(2);
  const std::string& inPath = files[0];
  const std::string& outPath = files[1];

  bool inBinary = detectBinary(inPath);
  bool outBinary = outFmt < 0 ? inBinary : outFmt == 1;

  // ---- pass 1 ----
  std::vector<u64> ids;        // identifier of step i
  std::vector<u8> flags;       // bit0: derived, bit1: marked
  std::vector<u64> antStart;   // antecedents of step i: ants[antStart[i] .. antStart[i+1])
  std::vector<u32> ants;       // antecedents as step indices
  antStart.push_back(0);
  IdMap map;
  u64 nOrig = 0, nDer = 0, nDel = 0, litsRead = 0, antsRead = 0;
  u64 conclusion = UINT64_MAX;
  {
    Parser p(inPath, inBinary);
    Step s;
    while (p.next(s)) {
      if (s.kind == DEL) {
        nDel++;
        for (u64 d : s.ants) map.erase(d);
        continue;
      }
      if (ids.size() >= 0xFFFFFFF0ull) throw std::runtime_error("too many steps (more than 2^32)");
      u32 idx = (u32)ids.size();
      if (s.kind == DER) {
        nDer++;
        for (u64 a : s.ants) {
          u32 r;
          if (!map.get(a, r)) {
            throw ParseError("error at byte offset " + std::to_string(p.offset()) + ": step " + std::to_string(s.id) +
                             " uses antecedent " + std::to_string(a) + " which is not defined (or already deleted)");
          }
          ants.push_back(r);
        }
        antsRead += s.ants.size();
      } else {
        nOrig++;
      }
      litsRead += s.lits.size();
      ids.push_back(s.id);
      flags.push_back(s.kind == DER ? 1 : 0);
      antStart.push_back(ants.size());
      map.set(s.id, idx);
      if (s.kind == DER && s.lits.empty()) {
        conclusion = idx;
        break;
      }
    }
  }
  if (conclusion == UINT64_MAX) {
    fprintf(stderr, "qlrup-trim: error: proof contains no conclusion (no derived constraint without literals)\n");
    return 1;
  }
  u64 nSteps = ids.size();

  // ---- marking ----
  flags[conclusion] |= 2;
  u64 keptOrig = 0, keptDer = 0, litsKept = 0, antsKept = 0;
  for (u64 i = conclusion + 1; i-- > 0;) {
    if (!(flags[i] & 2)) continue;
    if (flags[i] & 1)
      for (u64 k = antStart[i]; k < antStart[i + 1]; k++) flags[ants[k]] |= 2;
  }
  std::vector<u32> lastUse(nSteps, UINT32_MAX);
  for (u64 i = 0; i <= conclusion; i++)
    if ((flags[i] & 3) == 3)
      for (u64 k = antStart[i]; k < antStart[i + 1]; k++) lastUse[ants[k]] = (u32)i;
  std::vector<u32> newId;
  if (renumber) newId.assign(nSteps, 0);

  // ---- pass 2 ----
  std::string tmpPath = outPath + ".tmp" + std::to_string((long)getpid());
  u64 outBytes = 0, nDelWritten = 0, delIdsWritten = 0;
  try {
    Output out(tmpPath, outBinary);
    Parser p(inPath, inBinary);
    Step s;
    std::vector<u64> antIds, delIds;
    u64 idx = 0, counter = 0;
    while (idx <= conclusion && p.next(s)) {
      if (s.kind == DEL) continue;
      if (s.id != ids[idx]) throw std::runtime_error("input file changed between passes");
      u64 i = idx++;
      if (!(flags[i] & 2)) continue;
      u64 oid = renumber ? ++counter : s.id;
      if (renumber) newId[i] = (u32)oid;
      antIds.clear();
      delIds.clear();
      if (s.kind == DER) {
        for (u64 k = antStart[i]; k < antStart[i + 1]; k++) {
          u32 a = ants[k];
          antIds.push_back(renumber ? newId[a] : ids[a]);
          if (lastUse[a] == (u32)i) {
            lastUse[a] = UINT32_MAX;  // list each id once
            delIds.push_back(antIds.back());
          }
        }
        keptDer++;
        antsKept += antIds.size();
      } else {
        keptOrig++;
      }
      litsKept += s.lits.size();
      out.step(s, oid, antIds);
      // No deletion after the conclusion: the proof ends there.
      if (!delIds.empty() && i != conclusion) {
        out.deletion(delIds);
        nDelWritten++;
        delIdsWritten += delIds.size();
      }
    }
    if (idx <= conclusion) throw std::runtime_error("input file changed between passes");
    out.close();
    outBytes = out.bytes();
  } catch (...) {
    unlink(tmpPath.c_str());
    throw;
  }
  if (rename(tmpPath.c_str(), outPath.c_str()) != 0) {
    std::string e = strerror(errno);
    unlink(tmpPath.c_str());
    throw std::runtime_error("cannot rename temporary file to '" + outPath + "': " + e);
  }

  if (!quiet) {
    u64 inBytes = 0;
    try {
      inBytes = std::filesystem::file_size(inPath);
    } catch (...) {
    }
    fprintf(stderr, "qlrup-trim: input  %s, output %s%s\n", inBinary ? "binary" : "text", outBinary ? "binary" : "text",
            renumber ? ", renumbered" : ", ids kept");
    fprintf(stderr, "  steps read (up to conclusion): original %llu, derived %llu (input deletion steps ignored: %llu)\n",
            (unsigned long long)nOrig, (unsigned long long)nDer, (unsigned long long)nDel);
    fprintf(stderr, "  steps kept:                    original %llu, derived %llu (%.2f%% of %llu)\n",
            (unsigned long long)keptOrig, (unsigned long long)keptDer,
            nSteps ? 100.0 * double(keptOrig + keptDer) / double(nSteps) : 0.0, (unsigned long long)nSteps);
    fprintf(stderr, "  literals:       read %llu, written %llu\n", (unsigned long long)litsRead,
            (unsigned long long)litsKept);
    fprintf(stderr, "  antecedent ids: read %llu, written %llu\n", (unsigned long long)antsRead,
            (unsigned long long)antsKept);
    fprintf(stderr, "  deletion steps written: %llu (%llu ids)\n", (unsigned long long)nDelWritten,
            (unsigned long long)delIdsWritten);
    fprintf(stderr, "  size: input %llu bytes, output %llu bytes\n", (unsigned long long)inBytes,
            (unsigned long long)outBytes);
  }
  return 0;
}

}  // namespace

int main(int argc, char** argv) {
  try {
    return run(argc, argv);
  } catch (const std::exception& e) {
    fprintf(stderr, "qlrup-trim: %s\n", e.what());
    return 1;
  }
}
