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
  const int64_t learned_total = learned[0] + learned[1];
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
  fprintf (file, "c %-16s %12.2f seconds\n", "time:", seconds);
}

} // namespace miniqu
