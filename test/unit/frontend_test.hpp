#ifndef MINIQU_FRONTEND_TEST_HPP_INCLUDED
#define MINIQU_FRONTEND_TEST_HPP_INCLUDED

// Support for the parser tests: input files, and a way to test that a
// function ends the process through 'fatal'.

#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <string>
#include <sys/wait.h>
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

// Runs 'function' in a child process; true if the child exits with status 1
// and what it wrote to standard error contains 'expected'.
template <class F>
bool dies_with (F function, const std::string &expected) {
  int fds[2];
  if (pipe (fds))
    abort ();
  fflush (nullptr);
  const pid_t pid = fork ();
  if (pid == 0) {
    close (fds[0]);
    dup2 (fds[1], 2);
    function ();
    _exit (0);
  }
  close (fds[1]);
  std::string message;
  char buffer[512];
  for (ssize_t n; (n = read (fds[0], buffer, sizeof buffer)) > 0;)
    message.append (buffer, static_cast<size_t> (n));
  close (fds[0]);
  int status = 0;
  waitpid (pid, &status, 0);
  const bool ok = WIFEXITED (status) && WEXITSTATUS (status) == 1 &&
                  message.find (expected) != std::string::npos;
  if (!ok)
    fprintf (stderr,
             "expected failure containing '%s', got status %d: %s\n",
             expected.c_str (), status, message.c_str ());
  return ok;
}

#endif
