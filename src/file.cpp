#include "file.hpp"
#include "message.hpp"

#include <zlib.h>

namespace miniqu {

static constexpr size_t input_buffer_size = 1 << 16;
static constexpr size_t output_buffer_size = 1 << 20;

InputFile::InputFile (const std::string &path)
    : buffer (input_buffer_size) {
  gzFile f = path == "-" ? gzdopen (0, "rb") : gzopen (path.c_str (), "rb");
  handle = f;
  // We do our own buffering; zlib's is only a minimum for decompression.
  if (f)
    gzbuffer (f, (unsigned) input_buffer_size);
}

InputFile::~InputFile () {
  if (handle)
    gzclose (static_cast<gzFile> (handle));
}

bool InputFile::fill () {
  if (!handle)
    return false;
  const int n = gzread (static_cast<gzFile> (handle), buffer.data (),
                        (unsigned) buffer.size ());
  position = 0;
  available = n > 0 ? (size_t) n : 0;
  return available > 0;
}

OutputFile::OutputFile (const std::string &p) : path (p) {
  if (p == "-")
    file = stdout;
  else {
    file = fopen (p.c_str (), "wb");
    owned = file != nullptr;
  }
  buffer.reserve (output_buffer_size);
}

OutputFile::~OutputFile () {
  if (!file)
    return;
  flush ();
  if (owned && fclose (file))
    fatal ("failed to close '%s'", path.c_str ());
}

void OutputFile::put (std::string_view text) {
  for (char c : text)
    put_byte (static_cast<uint8_t> (c));
}

void OutputFile::flush () {
  if (!file)
    return;
  if (!buffer.empty () &&
      fwrite (buffer.data (), 1, buffer.size (), file) != buffer.size ())
    fatal ("failed to write to '%s'", path.c_str ());
  buffer.clear ();
  if (fflush (file))
    fatal ("failed to flush '%s'", path.c_str ());
}

} // namespace miniqu
