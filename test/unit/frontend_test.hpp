#ifndef MINIQU_FRONTEND_TEST_HPP_INCLUDED
#define MINIQU_FRONTEND_TEST_HPP_INCLUDED

// Support for the parser tests: input files, and ('child.hpp') a way to
// test that a function ends the process through 'fatal'.

#include "child.hpp"

#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <string>
#include <unistd.h>
#include <zlib.h>

// A directory that is removed when the test ends.  The children of
// 'dies_with' leave through 'exit' and must not remove it.
inline std::string temp_dir () {
  static const std::string dir = [] {
    const char *tmp = getenv ("TMPDIR");
    static std::string pattern =
        std::string (tmp ? tmp : "/tmp") + "/miniqu-frontend-XXXXXX";
    if (!mkdtemp (pattern.data ()))
      abort ();
    static const pid_t owner = getpid ();
    atexit ([] {
      if (getpid () == owner)
        std::filesystem::remove_all (pattern);
    });
    return pattern;
  }();
  return dir;
}

inline std::string write_file (const std::string &name,
                               const std::string &content) {
  const std::string path = temp_dir () + "/" + name;
  FILE *file = fopen (path.c_str (), "wb");
  if (!file)
    abort ();
  fwrite (content.data (), 1, content.size (), file);
  fclose (file);
  return path;
}

inline std::string write_gzip (const std::string &name,
                               const std::string &content) {
  const std::string path = temp_dir () + "/" + name;
  gzFile file = gzopen (path.c_str (), "wb");
  if (!file)
    abort ();
  gzwrite (file, content.data (), static_cast<unsigned> (content.size ()));
  gzclose (file);
  return path;
}

#endif
