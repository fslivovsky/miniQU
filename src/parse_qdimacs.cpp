#include "parse.hpp"

#include "file.hpp"
#include "message.hpp"

#include <cinttypes>
#include <climits>
#include <cstdarg>

namespace miniqu {

// QDIMACS parser: comment lines 'c ...', the header 'p cnf VARS CLAUSES',
// quantifier lines 'a ... 0' and 'e ... 0', and clauses '... 0'.  Like the
// old parser it takes whitespace (also newlines) as a separator, accepts
// quantifier lines between clauses, ignores the counts in the header, and
// puts every variable that is used but never quantified into an outermost
// existential block.  (The old parser reads such variables from an
// uninitialised map entry.)

namespace {

class QdimacsParser {
  const std::string &path;
  InputFile in;
  Qdimacs result;
  // Per variable: bit 0 quantified, bit 1 used in a clause.
  std::vector<uint8_t> state;

  [[noreturn]] void error (const char *fmt, ...) MINIQU_PRINTF (2, 3);

  static bool space (int c) { return (c >= 9 && c <= 13) || c == ' '; }

  void skip_space () {
    while (space (in.peek ()))
      in.get ();
  }
  void skip_line () {
    for (int c; (c = in.get ()) >= 0 && c != '\n';)
      ;
  }

  int parse_int () {
    skip_space ();
    bool negative = false;
    int c = in.peek ();
    if (c == '-' || c == '+') {
      negative = c == '-';
      in.get ();
      c = in.peek ();
    }
    if (c < '0' || c > '9')
      error ("number expected");
    int64_t value = 0;
    for (; c >= '0' && c <= '9'; c = in.peek ()) {
      value = 10 * value + (c - '0');
      if (value > INT_MAX)
        error ("number out of range");
      in.get ();
    }
    return static_cast<int> (negative ? -value : value);
  }

  uint8_t &state_of (int variable) {
    const size_t i = static_cast<size_t> (variable);
    if (state.size () <= i)
      state.resize (i + 1, 0);
    return state[i];
  }

  void parse_header () {
    in.get (); // 'p'
    skip_space ();
    for (const char *keyword = "cnf"; *keyword; keyword++)
      if (in.get () != *keyword)
        error ("'p cnf' expected");
    if (parse_int () < 0 || parse_int () < 0)
      error ("negative number in the header");
  }

  void parse_block (Quant quant) {
    in.get (); // 'a' or 'e'
    Qdimacs::Block block{quant, {}};
    while (const int variable = parse_int ()) {
      if (variable < 0)
        error ("negative variable %d in the prefix", variable);
      uint8_t &s = state_of (variable);
      if (s & 1)
        error ("variable %d is quantified more than once", variable);
      s |= 1;
      block.variables.push_back (variable);
    }
    result.blocks.push_back (std::move (block));
  }

  void parse_clause () {
    while (const int literal = parse_int ()) {
      state_of (literal < 0 ? -literal : literal) |= 2;
      result.literals.push_back (literal);
    }
    result.literals.push_back (0);
    result.clauses++;
  }

  void add_free_variables () {
    Qdimacs::Block block{Quant::Exists, {}};
    for (size_t v = 0; v < state.size (); v++)
      if (state[v] == 2)
        block.variables.push_back (static_cast<int> (v));
    if (!block.variables.empty ()) {
      VERBOSE (1, "%zu free variables are existential",
               block.variables.size ());
      result.blocks.insert (result.blocks.begin (), std::move (block));
    }
  }

public:
  explicit QdimacsParser (const std::string &file_path)
      : path (file_path), in (file_path) {
    if (!in.is_open ())
      fatal ("cannot open '%s'", path.c_str ());
  }

  Qdimacs parse () {
    for (;;) {
      skip_space ();
      const int c = in.peek ();
      if (c < 0)
        break;
      if (c == 'c')
        skip_line ();
      else if (c == 'p')
        parse_header ();
      else if (c == 'a')
        parse_block (Quant::Forall);
      else if (c == 'e')
        parse_block (Quant::Exists);
      else
        parse_clause ();
    }
    add_free_variables ();
    VERBOSE (1, "parsed %s: %zu quantifier blocks, %zu clauses",
             path.c_str (), result.blocks.size (), result.clauses);
    return std::move (result);
  }
};

void QdimacsParser::error (const char *fmt, ...) {
  char text[512];
  va_list ap;
  va_start (ap, fmt);
  vsnprintf (text, sizeof text, fmt, ap);
  va_end (ap);
  fatal ("%s:%" PRIu64 ": %s", path.c_str (), in.lineno (), text);
}

} // namespace

Qdimacs parse_qdimacs (const std::string &path) {
  return QdimacsParser (path).parse ();
}

} // namespace miniqu
