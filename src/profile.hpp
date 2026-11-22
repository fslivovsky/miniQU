#ifndef MINIQU_PROFILE_HPP_INCLUDED
#define MINIQU_PROFILE_HPP_INCLUDED

#include <cstdio>

namespace miniqu {

// Built-in profiling by process CPU time, as in CaDiCaL (ARCHITECTURE 9.3).
// A profile is timed when its level is at most the option 'profile'.
// Frequently executed phases get high levels because reading the clock has
// a cost; level 0 profiles are always timed and cost nothing in inner
// loops. Nested profiles are timed independently.
//
//        name       level
#define PROFILES \
  PROFILE (parse, 0) \
  PROFILE (search, 1) \
  PROFILE (reduce, 2) \
  PROFILE (collect, 2) \
  PROFILE (analyze, 3) \
  PROFILE (propagate, 3)

struct Profile {
  const char *name;
  int level;
  bool active = false;
  double started = 0;
  double total = 0;
};

class Profiles {
  int enabled; // timed profiles are those with 'level <= enabled'

public:
#define PROFILE(NAME, LEVEL) Profile NAME{#NAME, LEVEL};
  PROFILES
#undef PROFILE

  explicit Profiles (int level) : enabled (level) {}

  void start (Profile &);
  void stop (Profile &);
  void print (FILE *) const;
};

// Stops the profile when the scope ends.
class ProfileScope {
  Profiles &profiles;
  Profile &profile;

public:
  ProfileScope (Profiles &ps, Profile &p) : profiles (ps), profile (p) {
    profiles.start (profile);
  }
  ~ProfileScope () { profiles.stop (profile); }
  ProfileScope (const ProfileScope &) = delete;
  ProfileScope &operator= (const ProfileScope &) = delete;
};

} // namespace miniqu

// These expect a 'Profiles profiles' in scope, which is a member of the
// solver.
#define START(NAME) profiles.start (profiles.NAME)
#define STOP(NAME) profiles.stop (profiles.NAME)
#define PROFILE_SCOPE(NAME) \
  ::miniqu::ProfileScope profile_scope_##NAME (profiles, profiles.NAME)

#endif
