#include "file.hpp"
#include "test.hpp"

#include <cstdlib>
#include <string>
#include <unistd.h>
#include <zlib.h>

using namespace miniqu;

static std::string slurp (InputFile &in) {
  std::string s;
  for (int c; (c = in.get ()) >= 0;)
    s += (char) c;
  return s;
}

int main () {
  const char *tmp = getenv ("TMPDIR");
  std::string dir_template =
      std::string (tmp ? tmp : "/tmp") + "/miniqu-XXXXXX";
  CHECK (mkdtemp (dir_template.data ()) != nullptr);
  const std::string dir = dir_template;
  const std::string plain = dir + "/a.txt", zipped = dir + "/a.txt.gz";

  // Larger than every buffer, with newlines.
  std::string text;
  for (int i = 0; i < 200000; i++)
    text += "line " + std::to_string (i) + "\n";

  {
    OutputFile out (plain);
    CHECK (out.is_open ());
    out.put (text);
    out.put_byte (0);
    out.put_byte (255);
    CHECK_EQ (out.bytes (), text.size () + 2);
  }
  {
    gzFile z = gzopen (zipped.c_str (), "wb");
    CHECK (z != nullptr);
    gzwrite (z, text.data (), (unsigned) text.size ());
    const char tail[2] = {0, (char) 255};
    gzwrite (z, tail, 2);
    gzclose (z);
  }

  InputFile a (plain), b (zipped);
  CHECK (a.is_open () && b.is_open ());
  const std::string from_plain = slurp (a), from_zip = slurp (b);
  CHECK_EQ (from_plain.size (), text.size () + 2);
  CHECK (from_plain == from_zip);
  CHECK (from_plain.compare (0, text.size (), text) == 0);
  CHECK_EQ (a.lineno (), 200001u);
  CHECK_EQ (b.lineno (), 200001u);
  CHECK_EQ (a.get (), -1);
  CHECK_EQ (a.peek (), -1);

  // 'peek' does not consume, and counts lines only on 'get'.
  InputFile c (plain);
  CHECK_EQ (c.peek (), (int) 'l');
  CHECK_EQ (c.get (), (int) 'l');
  CHECK_EQ (c.lineno (), 1u);
  while (c.get () != '\n') {
  }
  CHECK_EQ (c.lineno (), 2u);

  InputFile missing (dir + "/missing");
  CHECK (!missing.is_open ());
  CHECK_EQ (missing.get (), -1);

  unlink (plain.c_str ());
  unlink (zipped.c_str ());
  rmdir (dir.c_str ());
  return test_result ();
}
