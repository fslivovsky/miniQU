#ifndef MINIQU_RESOURCES_HPP_INCLUDED
#define MINIQU_RESOURCES_HPP_INCLUDED

#include <cstdint>

namespace miniqu {

// Process resources (the old 'limitTime', 'limitMemory' and the memory
// statistics).  A limit that cannot be set is reported as a warning.

// Soft limit on CPU time: the kernel sends SIGXCPU when it is reached.
void limit_time (int seconds);

// Limit on the address space: allocations beyond it fail.
void limit_memory (int megabytes);

// Peak resident set size in bytes.
uint64_t maximum_resident_set_size ();

} // namespace miniqu

#endif
