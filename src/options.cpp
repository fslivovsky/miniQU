#include "options.hpp"
#include "message.hpp"

#include <cerrno>
#include <climits>
#include <cstdlib>
#include <cstring>

namespace miniqu {

namespace {

const OptionInfo infos[] = {
#define OPTION(NAME, DEFAULT, LOW, HIGH, DESCRIPTION) \
  {#NAME, DEFAULT, LOW, HIGH, DESCRIPTION},
    OPTIONS
#undef OPTION
};

// Same order as 'infos'.
int Options::*const members[] = {
#define OPTION(NAME, DEFAULT, LOW, HIGH, DESCRIPTION) &Options::NAME,
    OPTIONS
#undef OPTION
};

constexpr size_t count = sizeof infos / sizeof infos[0];
static_assert (sizeof members / sizeof members[0] == count);

// Index of the option or 'count'.
size_t find (std::string_view name) {
  size_t i = 0;
  while (i < count && name != infos[i].name)
    i++;
  return i;
}

} // namespace

std::span<const OptionInfo> option_table () { return infos; }

bool Options::set (std::string_view name, int value) {
  const size_t i = find (name);
  if (i == count || value < infos[i].low || value > infos[i].high)
    return false;
  this->*members[i] = value;
  return true;
}

int Options::get (std::string_view name) const {
  const size_t i = find (name);
  if (i == count)
    fatal ("unknown option '%.*s'", (int) name.size (), name.data ());
  return this->*members[i];
}

void Options::print_usage (FILE *file) {
  for (const OptionInfo &o : infos)
    fprintf (file, "  --%-15s %10d [%d,%d]  %s\n", o.name, o.default_value,
             o.low, o.high, o.description);
}

bool parse_option (const char *arg, std::string &name, int &value) {
  if (arg[0] != '-')
    return false;
  const char *p = arg + 1;
  if (*p == '-')
    p++;
  const char *equals = strchr (p, '=');
  std::string key (p, equals ? (size_t) (equals - p) : strlen (p));
  std::erase (key, '-');

  // '--no-name' sets 0.  The hyphens inside the name are ignored, so the
  // prefix has to be recognised in the original spelling.
  const bool negated = !equals && strncmp (p, "no-", 3) == 0;
  if (negated)
    key.erase (0, 2);
  if (key.empty ())
    return false;

  int v = 1;
  if (equals) {
    const char *digits = equals + 1;
    char *end;
    errno = 0;
    const long l = strtol (digits, &end, 10);
    if (end == digits || *end || errno || l < INT_MIN || l > INT_MAX)
      return false;
    v = (int) l;
  }
  name = key;
  value = negated ? 0 : v;
  return true;
}

} // namespace miniqu
