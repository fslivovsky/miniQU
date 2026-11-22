#include "options.hpp"
#include "test.hpp"

#include <string>

using namespace miniqu;

// Parses 'arg' and applies it; returns false if it is not an option.
static bool apply (Options &opts, const char *arg, bool *known = nullptr) {
  std::string name;
  int value;
  if (!parse_option (arg, name, value))
    return false;
  const bool ok = opts.set (name, value);
  if (known)
    *known = ok;
  return true;
}

static void expect_parse (const char *arg, const char *name, int value) {
  std::string n;
  int v = -12345;
  const bool ok = parse_option (arg, n, v);
  if (!ok || n != name || v != value) {
    fprintf (stderr, "parse_option (\"%s\") gave %d, %s, %d\n", arg, ok,
             n.c_str (), v);
    test_failures++;
  }
}

static void expect_reject (const char *arg) {
  std::string n;
  int v;
  if (parse_option (arg, n, v)) {
    fprintf (stderr, "parse_option (\"%s\") accepted\n", arg);
    test_failures++;
  }
}

int main () {
  // Defaults of the M1 table.
  Options o;
  CHECK_EQ (o.mode, 0);
  CHECK_EQ (o.earlytseitin, 1);
  CHECK_EQ (o.verb, 1);
  CHECK_EQ (o.phasesaving, 2);
  CHECK_EQ (o.luby, 1);
  CHECK_EQ (o.rfirst, 100);
  CHECK_EQ (o.rinc, 200);
  CHECK_EQ (o.vardecay, 950);
  CHECK_EQ (o.gcfrac, 20);
  CHECK_EQ (o.tier1glue, 2);
  CHECK_EQ (o.depreset, 20);
  CHECK_EQ (o.reduceint, 0);
  CHECK_EQ (o.seed, 0);

  // The table agrees with the struct, and every option accepts both ends
  // of its range and rejects the values just outside.
  for (const OptionInfo &info : option_table ()) {
    CHECK_EQ (o.get (info.name), info.default_value);
    CHECK (o.set (info.name, info.low));
    CHECK_EQ (o.get (info.name), info.low);
    CHECK (o.set (info.name, info.high));
    CHECK_EQ (o.get (info.name), info.high);
    CHECK (!o.set (info.name, info.low - 1));
    CHECK (!o.set (info.name, info.high + 1));
    CHECK_EQ (o.get (info.name), info.high);
    CHECK (o.set (info.name, info.default_value));
  }
  CHECK (!o.set ("nosuchoption", 1));
  CHECK (!o.set ("arenaorder", 0));
  CHECK (!o.set ("rndseed", 1));

  // Spellings.
  expect_parse ("--dl", "dl", 1);
  expect_parse ("--no-dl", "dl", 0);
  expect_parse ("-dl", "dl", 1);
  expect_parse ("-no-dl", "dl", 0);
  expect_parse ("--mode=2", "mode", 2);
  expect_parse ("-mode=1", "mode", 1);
  expect_parse ("-ccmin-mode=3", "ccminmode", 3);
  expect_parse ("--ccmin-mode=3", "ccminmode", 3);
  expect_parse ("-proof-binary", "proofbinary", 1);
  expect_parse ("-early-tseitin", "earlytseitin", 1);
  expect_parse ("-no-early-tseitin", "earlytseitin", 0);
  expect_parse ("-verb=0", "verb", 0);
  expect_parse ("--no-luby", "luby", 0);
  expect_parse ("--seed=7", "seed", 7);
  expect_parse ("-rnd-seed=5", "rndseed", 5);
  expect_parse ("--seed=-3", "seed", -3);

  // Application arguments are not options.
  expect_reject ("--proof=FILE");
  expect_reject ("-proof=out.qlrup");
  expect_reject ("formula.qcir");
  expect_reject ("/tmp/--dl");
  expect_reject ("-");
  expect_reject ("--");
  expect_reject ("--=3");
  expect_reject ("--no-");
  expect_reject ("--mode=");
  expect_reject ("--mode=1x");
  expect_reject ("--mode=99999999999");
  expect_reject ("");

  // Applying parsed arguments.
  Options p;
  bool known = false;
  CHECK (apply (p, "-ccmin-mode=3", &known) && known);
  CHECK_EQ (p.ccminmode, 3);
  CHECK (apply (p, "--no-luby", &known) && known);
  CHECK_EQ (p.luby, 0);
  CHECK (apply (p, "--gcfrac=0", &known) && known);
  CHECK_EQ (p.gcfrac, 0);
  CHECK (apply (p, "--mode=3", &known) && !known);
  CHECK_EQ (p.mode, 0);
  CHECK (apply (p, "-rnd-seed=5", &known) && !known);
  CHECK (apply (p, "--bogus", &known) && !known);

  return test_result ();
}
