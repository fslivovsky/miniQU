#include "stats.hpp"
#include "internal_test.hpp"
#include "lit.hpp"
#include "profile.hpp"
#include "test.hpp"

#include <map>
#include <string>

using namespace miniqu;

int main () {
  Stats stats;
  stats.conflicts = 12;
  stats.learned[index (Kind::Cube)] = 3;
  stats.reduced[index (Kind::Clause)] = 4;

  FILE *f = tmpfile ();
  CHECK (f != nullptr);
  stats.print (f, 2.0);
  rewind (f);

  // Every counter has exactly one 'c stat' line with an integer value.
  std::map<std::string, int> seen;
  std::map<std::string, long> value;
  char line[256];
  while (fgets (line, sizeof line, f)) {
    char name[64];
    long v;
    if (sscanf (line, "c stat %63s %ld", name, &v) == 2) {
      seen[name]++;
      value[name] = v;
    }
  }
  fclose (f);

  size_t expected = 0;
#define COUNTER(NAME) \
  expected++; \
  CHECK_EQ (seen[#NAME], 1);
#define KIND_COUNTER(NAME) \
  expected += 2; \
  CHECK_EQ (seen[#NAME ".clause"], 1); \
  CHECK_EQ (seen[#NAME ".cube"], 1);
  STATS
#undef COUNTER
#undef KIND_COUNTER
  CHECK_EQ (seen.size (), expected);
  CHECK_EQ (value["conflicts"], 12L);
  CHECK_EQ (value["learned.cube"], 3L);
  CHECK_EQ (value["learned.clause"], 0L);
  CHECK_EQ (value["reduced.clause"], 4L);

  // Profiles: a level above the option is not timed.
  Profiles profiles (1);
  START (search);
  STOP (search);
  START (propagate);
  STOP (propagate);
  CHECK (profiles.search.total >= 0);
  CHECK_EQ (profiles.propagate.total, 0.0);
  {
    PROFILE_SCOPE (parse);
    CHECK (profiles.parse.active);
  }
  CHECK (!profiles.parse.active);
  FILE *g = tmpfile ();
  profiles.print (g);
  fclose (g);

  // A search at level 3 times the phases that were declared but never
  // started before; level 0 times none of them.
  for (int level : {0, 3}) {
    Internal internal;
    internal.opts.profile = level;
    declare (internal, "ae");
    add (internal, Kind::Clause, {1, 2});
    add (internal, Kind::Clause, {1, -2});
    CHECK (internal.solve () == Status::False);
    const Profiles &p = internal.profiles;
    CHECK_EQ (p.search.total > 0, level == 3);
    CHECK_EQ (p.analyze.total > 0, level == 3);
    CHECK_EQ (p.propagate.total > 0, level == 3);
  }

  return test_result ();
}
