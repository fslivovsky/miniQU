#ifndef MINIQU_OPTIONS_HPP_INCLUDED
#define MINIQU_OPTIONS_HPP_INCLUDED

#include <cstdio>
#include <span>
#include <string>
#include <string_view>

namespace miniqu {

// All options are integers and are declared here and nowhere else
// (ARCHITECTURE 9.1).  Fractions are percent or per mille.  The low end of
// every interval is the smallest value the code can run with, so that
// stress configurations can make every scheduled event fire on small
// instances.
//
//      name         default  low  high  description
#define OPTIONS \
  OPTION (mode, 0, 0, 2, \
          "0=Q-resolution, 1=QU-resolution, 2=long-distance") \
  OPTION (dl, 0, 0, 1, "dependency learning") \
  OPTION (cert, 0, 0, 1, "print the certificate (V line)") \
  OPTION (qcir, 0, 0, 1, "read QCIR even if the file is not recognised") \
  OPTION (earlytseitin, 1, 0, 1, "early Tseitin variable introduction") \
  OPTION (verb, 1, 0, 3, "verbosity level") \
  OPTION (ccminmode, 0, 0, 3, \
          "learnt minimisation: 0=none 1=basic 2=deep 3=deep+reduction") \
  OPTION (legacyanalyze, 0, 0, 1, "analysis as in the old solver") \
  OPTION (phasesaving, 2, 0, 2, "0=none, 1=limited, 2=full") \
  OPTION (luby, 1, 0, 1, "Luby restart sequence (else geometric)") \
  OPTION (rfirst, 100, 1, 1000000000, "first restart interval") \
  OPTION (rinc, 200, 100, 1000000000, "restart increase in percent") \
  OPTION (vardecay, 950, 1, 999, "variable score decay in per mille") \
  OPTION (gcfrac, 20, 0, 100, \
          "wasted arena percent that triggers collection, 0=always") \
  OPTION (minlearnts, 0, 0, 1000000000, "minimum learnt limit") \
  OPTION (proofbinary, 0, 0, 1, "write proofs in binary format") \
  OPTION (cpulim, 0, 0, 1000000000, "CPU time limit in seconds, 0=none") \
  OPTION (memlim, 0, 0, 1000000000, "memory limit in MB, 0=none") \
  OPTION (check, 0, 0, 1, "check every learnt constraint internally") \
  OPTION (log, 0, 0, 1, "print LOG lines (needs MINIQU_LOGGING)") \
  OPTION (seed, 0, 0, 1000000000, "random initial scores if nonzero") \
  OPTION (reduceint, 300, 0, 1000000000, \
          "reduce every n-th (arithmetically growing) conflict " \
          "interval, 0=never") \
  OPTION (reducetarget, 75, 10, 100, \
          "percent of the reduction candidates deleted") \
  OPTION (reducesize, 0, 0, 1, \
          "also reduce when the learnt constraints exceed the MiniSat " \
          "size limit") \
  OPTION (tiers, 1, 0, 1, \
          "recently used learnt constraints survive reduction") \
  OPTION (glueupdate, 1, 0, 1, \
          "recompute the glue of learnt constraints used in analysis") \
  OPTION (tier1glue, 2, 0, 1000000000, \
          "learnt constraints up to this glue are kept") \
  OPTION ( \
      tier2glue, 6, 0, 1000000000, \
      "learnt constraints up to this glue are used for two reductions") \
  OPTION (recomputetier, 0, 0, 1, \
          "tier limits per kind from the usage of learnt constraints") \
  OPTION (tier1limit, 50, 0, 100, \
          "percent of the uses that tier 1 covers, with recomputetier") \
  OPTION (tier2limit, 90, 0, 100, \
          "percent of the uses that tier 2 covers, with recomputetier") \
  OPTION (tier1minglue, 0, 0, 100, \
          "lowest tier 1 limit, with recomputetier") \
  OPTION (tier2minglue, 0, 0, 100, \
          "lowest tier 2 limit, with recomputetier") \
  OPTION (rootsimp, 1, 0, 1, \
          "root-level simplification (modes 0 and 1; off in mode 2)") \
  OPTION (rootsimpdelay, 1, 0, 1, \
          "simplify at the root only after as many propagations as " \
          "stored literals") \
  OPTION (depreset, 20, 1, 1000000000, \
          "reset dependencies every n restarts, with restartmode=0") \
  OPTION (restartmode, 0, 0, 1, \
          "0=Luby/geometric schedule, 1=glue averages per kind") \
  OPTION (restartint, 2, 1, 1000000000, \
          "minimum conflicts between two restarts, with restartmode=1") \
  OPTION (restartmargin, 10, 0, 100, \
          "percent the fast glue average must exceed the slow one by") \
  OPTION (emagluefast, 33, 1, 1000000000, \
          "window of the fast glue average") \
  OPTION (emaglueslow, 100000, 1, 1000000000, \
          "window of the slow glue average") \
  OPTION (depresetint, 5000, 1, 1000000000, \
          "reset dependencies every n conflicts, with restartmode=1") \
  OPTION (reusetrail, 1, 0, 1, \
          "keep the trail prefix whose decisions a restart would redo") \
  OPTION (elim, 0, 0, 1, \
          "bounded variable elimination (QCIR input, modes 0 and 1)") \
  OPTION ( \
      elimclause, 1, 0, 1, \
      "eliminate existential variables by clause resolution, with elim") \
  OPTION (elimcube, 1, 0, 1, \
          "eliminate universal variables by cube resolution, with elim") \
  OPTION (elimpre, 1, 0, 1, "eliminate before the search, with elim") \
  OPTION (eliminp, 1, 0, 1, "eliminate in inprocessing rounds, with elim") \
  OPTION (elimint, 2000, 1, 1000000000, \
          "conflicts between elimination rounds (growing arithmetically)") \
  OPTION (elimbound, 0, 0, 1000000000, \
          "additional constraints an elimination may add") \
  OPTION (elimboundmax, 16, 0, 1000000000, \
          "largest bound on additional constraints, with elim") \
  OPTION ( \
      elimsubsume, 1, 0, 1, \
      "do not add resolvents subsumed by a stored constraint, with elim") \
  OPTION (elimocclim, 100, 1, 1000000000, \
          "occurrence limit per literal of an eliminated variable") \
  OPTION (elimclslim, 100, 2, 1000000000, "size limit of a resolvent") \
  OPTION (elimticks, 100000000, 0, 1000000000, \
          "literal visits one elimination round may spend") \
  OPTION (elimmark, 0, 0, 1, \
          "retry only variables with a deleted constraint, with elim") \
  OPTION ( \
      elimeffort, 0, 0, 1000000000, \
      "inprocessing round budget in per mille of search ticks (0: off)") \
  OPTION (elimmineff, 10000000, 0, 1000000000, \
          "smallest budget of an inprocessing round, with elimeffort") \
  OPTION ( \
      dropwatches, 1, 0, 1, \
      "free the watch lists during elimination and subsumption rounds") \
  OPTION (elimbackward, 1, 0, 1, \
          "subsume and strengthen with resolvents, with elim and subsume") \
  OPTION (subsume, 0, 0, 1, \
          "subsumption and strengthening rounds (modes 0 and 1)") \
  OPTION (subsumestr, 1, 0, 1, \
          "strengthen by self-subsuming resolution, with subsume") \
  OPTION (subsumeint, 2000, 1, 1000000000, \
          "conflicts between subsumption rounds (growing arithmetically)") \
  OPTION (subsumeclslim, 100, 2, 1000000000, \
          "size limit of a constraint in a subsumption round") \
  OPTION (subsumeocclim, 100, 1, 1000000000, \
          "limit on the constraints connected to one literal") \
  OPTION (subsumeticks, 100000000, 0, 1000000000, \
          "literal visits one subsumption round may spend") \
  OPTION ( \
      vivify, 0, 0, 1, \
      "vivify learnt constraints in inprocessing rounds (modes 0 and 1)") \
  OPTION (vivifyclause, 1, 0, 1, "vivify learnt clauses, with vivify") \
  OPTION (vivifycube, 1, 0, 1, "vivify learnt cubes, with vivify") \
  OPTION ( \
      vivifyint, 2000, 1, 1000000000, \
      "conflicts between vivification rounds (growing arithmetically)") \
  OPTION (vivifyticks, 2000000, 0, 1000000000, \
          "propagation ticks one vivification round may spend") \
  OPTION (vivifyonce, 1, 0, 1, \
          "do not retry constraints that vivification left unchanged") \
  OPTION (vivifytier, 2, 1, 3, \
          "vivify learnt constraints of tier 1, up to tier 2, or all") \
  OPTION (profile, 0, 0, 3, "profiling level")

struct Options {
#define OPTION(NAME, DEFAULT, LOW, HIGH, DESCRIPTION) int NAME = DEFAULT;
  OPTIONS
#undef OPTION

  // False if the name is unknown or the value is out of range; the options
  // are left unchanged then.
  bool set (std::string_view name, int value);

  // The value of a known option; unknown names are fatal.
  int get (std::string_view name) const;

  static void print_usage (FILE *);
};

struct OptionInfo {
  const char *name;
  int default_value, low, high;
  const char *description;
};

std::span<const OptionInfo> option_table ();

// Parses one command line argument of the forms '--name=value', '--name'
// (value 1) and '--no-name' (value 0).  One leading dash is accepted too
// and hyphens inside the name are ignored, so '-ccmin-mode=3' sets
// 'ccminmode'. Returns false for anything else, in particular for
// non-integer values such as '--proof=FILE': those are application
// arguments.  The name is not checked against the table; 'Options::set'
// does that.
bool parse_option (const char *arg, std::string &name, int &value);

} // namespace miniqu

#endif
