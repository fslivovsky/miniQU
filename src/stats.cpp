#include "stats.hpp"
#include "util.hpp"

#include <cinttypes>

namespace miniqu {

void Stats::print (FILE *file, double seconds) const {
#define COUNTER(NAME) \
  fprintf (file, "c stat " #NAME " %" PRId64 "\n", NAME);
#define KIND_COUNTER(NAME) \
  fprintf (file, "c stat " #NAME ".clause %" PRId64 "\n", NAME[0]); \
  fprintf (file, "c stat " #NAME ".cube %" PRId64 "\n", NAME[1]);
  STATS
#undef COUNTER
#undef KIND_COUNTER

  const auto row = [&] (const char *name, int64_t count) {
    fprintf (file, "c %-16s %12" PRId64 " %12.2f per second\n", name, count,
             relative ((double) count, seconds));
  };
  const auto total = [] (const int64_t (&counter)[2]) {
    return counter[0] + counter[1];
  };
  const int64_t learned_total = total (learned);
  fprintf (file, "c\n");
  row ("conflicts:", conflicts);
  row ("decisions:", decisions);
  row ("propagations:", propagations);
  row ("restarts:", restarts);
  row ("learned:", learned_total);
  fprintf (file, "c %-16s %12.2f literals per learned constraint\n",
           "size:",
           relative ((double) (learnedlits[0] + learnedlits[1]),
                     (double) learned_total));
  row ("reductions:", reductions);
  row ("reduced:", total (reduced));
  row ("used:", total (used));
  row ("glue updates:", total (glueupdates));
  row ("promoted:", total (promoted));
  fprintf (file, "c %-16s %12.2f seconds\n", "time:", seconds);
}

} // namespace miniqu
