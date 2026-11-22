#ifndef MINIQU_FILE_HPP_INCLUDED
#define MINIQU_FILE_HPP_INCLUDED

#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

namespace miniqu {

// Buffered input.  Plain and gzip-compressed files are both read through
// zlib; "-" reads standard input.  'get' and 'peek' return the next byte or
// -1 at the end, and 'lineno' is the number of the line the next byte is
// on, starting at 1.
class InputFile {
  void *handle = nullptr; // zlib 'gzFile'
  std::vector<char> buffer;
  size_t position = 0, available = 0;
  uint64_t line = 1;

  bool fill ();

public:
  explicit InputFile (const std::string &path);
  ~InputFile ();
  InputFile (const InputFile &) = delete;
  InputFile &operator= (const InputFile &) = delete;

  bool is_open () const { return handle != nullptr; }

  int peek () {
    if (position == available && !fill ())
      return -1;
    return (unsigned char) buffer[position];
  }
  int get () {
    const int c = peek ();
    if (c < 0)
      return c;
    position++;
    if (c == '\n')
      line++;
    return c;
  }
  uint64_t lineno () const { return line; }
};

// Buffered output of text and binary data; "-" writes to standard output.
// The destructor flushes and closes.  Write errors are fatal.
class OutputFile {
  FILE *file = nullptr;
  bool owned = false;
  std::string path;
  std::vector<char> buffer;
  uint64_t bytes_ = 0;

public:
  explicit OutputFile (const std::string &path);
  ~OutputFile ();
  OutputFile (const OutputFile &) = delete;
  OutputFile &operator= (const OutputFile &) = delete;

  bool is_open () const { return file != nullptr; }

  void put_byte (uint8_t byte) {
    if (buffer.size () == buffer.capacity ())
      flush ();
    buffer.push_back (static_cast<char> (byte));
    bytes_++;
  }
  void put (std::string_view text);
  void flush ();

  // Bytes written so far, including those still in the buffer.
  uint64_t bytes () const { return bytes_; }
};

} // namespace miniqu

#endif
