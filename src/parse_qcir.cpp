#include "parse.hpp"

#include "file.hpp"
#include "message.hpp"

#include <cctype>
#include <cinttypes>
#include <cstdarg>

namespace miniqu {

// QCIR parser (prenex G14 format).
//
// Statements are lines, as in the old parser: an optional '#' comment line
// (the header "#QCIR-G14" is one), the quantifier statements free, exists
// and forall, 'output (lit)', and gate definitions 'g = and|or|xor|ite
// (lits)'.  Keywords are case-insensitive, identifiers are not, and blanks
// are allowed around every token.  Unlike the old parser, which strips all
// blanks from a line, a blank inside an identifier ends it, and the
// characters '(', ')', ',' and '=' cannot occur in one.
//
// The input is read one character at a time through the buffer of
// 'InputFile', because benchmark files have single lines of many megabytes:
// the only strings that exist are the identifier being read and the keys of
// the hash map in the circuit.  Gates may be used before they are defined
// (the output statement usually is), which the circuit resolves at the end.

namespace {

class QcirParser {
  const std::string &path;
  InputFile in;
  Circuit circuit;
  bool have_output = false;
  std::string token;     // the identifier or keyword being read
  std::string gate_name; // left-hand side of a gate definition
  std::vector<int> literals;

  [[noreturn]] void error (const char *fmt, ...) MINIQU_PRINTF (2, 3);

  static bool blank (int c) {
    return c == ' ' || c == '\t' || c == '\r' || c == '\v' || c == '\f';
  }
  static bool delimiter (int c) {
    return c < 0 || blank (c) || c == '\n' || c == '(' || c == ')' ||
           c == ',' || c == '=';
  }

  void skip_blanks () {
    while (blank (in.peek ()))
      in.get ();
  }
  void skip_line () {
    for (int c; (c = in.get ()) >= 0 && c != '\n';)
      ;
  }

  // Reads a possibly empty run of identifier characters into 'token'.
  void read_token () {
    token.clear ();
    for (int c; !delimiter (c = in.peek ());) {
      token.push_back (static_cast<char> (c));
      in.get ();
    }
  }

  void lowercase_token () {
    for (char &c : token)
      c = static_cast<char> (tolower (static_cast<unsigned char> (c)));
  }

  // The elements of "( e, e, ... )" after the opening parenthesis.  A
  // trailing comma is accepted, as by the old parser.
  template <class F> void parse_list (F element) {
    for (;;) {
      skip_blanks ();
      if (in.peek () == ')') {
        in.get ();
        return;
      }
      element ();
      skip_blanks ();
      const int c = in.peek ();
      if (c == ')') {
        in.get ();
        return;
      }
      if (c != ',')
        error ("expected ',' or ')'");
      in.get ();
    }
  }

  void read_identifier () {
    read_token ();
    if (token.empty ())
      error ("identifier expected");
    if (token[0] == '-')
      error ("identifier '%s' must not start with '-'", token.c_str ());
  }

  int read_literal () {
    const bool negated = in.peek () == '-';
    if (negated)
      in.get ();
    read_identifier ();
    const int number = circuit.reference (token, in.lineno ());
    return negated ? -number : number;
  }

  void parse_quantifier (Quant quant) {
    if (circuit.gates ())
      error ("quantifier statement after a gate definition (only prenex "
             "formulas are supported)");
    parse_list ([&] {
      read_identifier ();
      if (!circuit.add_variable (quant, token))
        error ("variable '%s' is already defined", token.c_str ());
    });
  }

  void parse_output () {
    if (have_output)
      error ("repeated output statement");
    int count = 0;
    parse_list ([&] {
      if (count++)
        error ("output takes exactly one literal");
      circuit.set_output (read_literal ());
    });
    if (count != 1)
      error ("output takes exactly one literal");
    have_output = true;
  }

  void parse_gate () {
    if (gate_name[0] == '-')
      error ("identifier '%s' must not start with '-'", gate_name.c_str ());
    skip_blanks ();
    read_token ();
    lowercase_token ();
    const std::string type = token;
    skip_blanks ();
    if (in.peek () != '(')
      error ("'(' expected after '%s'", type.c_str ());
    in.get ();
    literals.clear ();
    parse_list ([&] { literals.push_back (read_literal ()); });

    int number;
    if (type == "and" || type == "or") {
      number =
          circuit.add_gate (type == "and" ? GateType::And : GateType::Or,
                            gate_name, literals);
    } else if (type == "xor" || type == "ite") {
      const size_t arity = type == "xor" ? 2 : 3;
      if (literals.size () != arity)
        error ("%s takes %zu inputs, not %zu", type.c_str (), arity,
               literals.size ());
      number = type == "xor"
                   ? circuit.add_xor (gate_name, literals[0], literals[1])
                   : circuit.add_ite (gate_name, literals[0], literals[1],
                                      literals[2]);
    } else {
      error ("unknown gate type '%s'", type.c_str ());
    }
    if (!number)
      error ("identifier '%s' is already defined", gate_name.c_str ());
  }

  void parse_statement () {
    read_token ();
    if (token.empty ())
      error ("malformed line");
    skip_blanks ();
    const int c = in.peek ();
    if (c == '=') {
      in.get ();
      gate_name = token;
      parse_gate ();
    } else if (c == '(') {
      in.get ();
      lowercase_token ();
      if (token == "forall")
        parse_quantifier (Quant::Forall);
      else if (token == "exists" || token == "free")
        parse_quantifier (Quant::Exists);
      else if (token == "output")
        parse_output ();
      else
        error ("unknown statement '%s'", token.c_str ());
    } else
      error ("malformed line");
    skip_blanks ();
    if (in.peek () >= 0 && in.peek () != '\n')
      error ("unexpected characters after ')'");
  }

public:
  explicit QcirParser (const std::string &file_path)
      : path (file_path), in (file_path) {
    if (!in.is_open ())
      fatal ("cannot open '%s'", path.c_str ());
  }

  Circuit parse () {
    for (;;) {
      skip_blanks ();
      const int c = in.peek ();
      if (c < 0)
        break;
      if (c == '#')
        skip_line ();
      else if (c == '\n')
        in.get ();
      else
        parse_statement ();
    }
    if (!have_output)
      fatal ("%s: missing output statement", path.c_str ());
    if (auto defect = circuit.resolve ()) {
      if (defect->kind == Circuit::Defect::Kind::Undefined)
        fatal ("%s:%" PRIu64 ": identifier '%s' is neither a quantified "
               "variable nor a gate",
               path.c_str (), defect->line, defect->name.c_str ());
      fatal ("%s: gate '%s' depends on itself", path.c_str (),
             defect->name.c_str ());
    }
    const int removed = circuit.remove_redundant ();
    circuit.compute_polarities ();
    VERBOSE (1, "parsed %s: %d variables, %d gates, %d removed",
             path.c_str (), circuit.variables (), circuit.gates (),
             removed);
    return std::move (circuit);
  }
};

void QcirParser::error (const char *fmt, ...) {
  char text[512];
  va_list ap;
  va_start (ap, fmt);
  vsnprintf (text, sizeof text, fmt, ap);
  va_end (ap);
  fatal ("%s:%" PRIu64 ": %s", path.c_str (), in.lineno (), text);
}

} // namespace

Circuit parse_qcir (const std::string &path) {
  return QcirParser (path).parse ();
}

} // namespace miniqu
