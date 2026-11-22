cmake_minimum_required(VERSION 3.22)

project(miniQU CXX)

#--------------------------------------------------------------------------------------------------
# Configurable options:

option(STATIC_BINARIES "Link binaries statically." OFF)

if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type." FORCE)
endif()

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

find_package(ZLIB REQUIRED)

# GCC's sanitizer runtimes are not found by the dynamic loader: they live in GCC's own directory, and
# on some distributions the packages lack the symlinks named after the soname (libasan.so.6).  Link
# against a directory of such symlinks in the build tree.
if(CMAKE_CXX_FLAGS MATCHES "-fsanitize" AND CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  set(MINIQU_SANITIZER_DIR ${CMAKE_BINARY_DIR}/sanitizer-runtime)
  foreach(runtime asan ubsan)
    execute_process(COMMAND ${CMAKE_CXX_COMPILER} -print-file-name=lib${runtime}.so
                    OUTPUT_VARIABLE runtime_path OUTPUT_STRIP_TRAILING_WHITESPACE)
    if(IS_ABSOLUTE "${runtime_path}")
      get_filename_component(runtime_real "${runtime_path}" REALPATH)
      get_filename_component(runtime_file "${runtime_real}" NAME)
      string(REGEX REPLACE "\\.[0-9]+\\.[0-9]+$" "" runtime_soname "${runtime_file}")
      file(MAKE_DIRECTORY ${MINIQU_SANITIZER_DIR})
      file(CREATE_LINK "${runtime_real}" ${MINIQU_SANITIZER_DIR}/${runtime_soname} SYMBOLIC)
    endif()
  endforeach()
  string(APPEND CMAKE_EXE_LINKER_FLAGS " -Wl,-rpath,${MINIQU_SANITIZER_DIR}")
endif()

#--------------------------------------------------------------------------------------------------
# The new solver (src/): library, tools, unit tests.

set(MINIQU_WARNINGS -Wall -Wextra -Wpedantic -Wshadow -Wconversion -Wsign-conversion -Werror)

file(GLOB MINIQU_SOURCES CONFIGURE_DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp)
file(GLOB MINIQU_HEADERS CONFIGURE_DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/src/*.hpp)
file(GLOB MINIQU_UNIT_TESTS CONFIGURE_DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/test/unit/*.cpp)
file(GLOB MINIQU_UNIT_HEADERS CONFIGURE_DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/test/unit/*.hpp)

add_library(miniqu STATIC ${MINIQU_SOURCES})
target_include_directories(miniqu PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/src)
target_compile_options(miniqu PRIVATE ${MINIQU_WARNINGS})
target_link_libraries(miniqu PUBLIC ZLIB::ZLIB)

# Proof trimmer (see doc/proof-format.md).
add_executable(qlrup-trim tools/qlrup-trim.cc)

if(STATIC_BINARIES)
  target_link_libraries(qlrup-trim -static)
endif()

enable_testing()

# One executable per file in test/unit, each a ctest test of the same name.
add_custom_target(unit-tests)
foreach(test_source ${MINIQU_UNIT_TESTS})
  get_filename_component(test_name ${test_source} NAME_WE)
  add_executable(unit-${test_name} ${test_source})
  target_link_libraries(unit-${test_name} PRIVATE miniqu)
  target_include_directories(unit-${test_name} PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/test/unit)
  target_compile_options(unit-${test_name} PRIVATE ${MINIQU_WARNINGS})
  add_dependencies(unit-tests unit-${test_name})
  add_test(NAME unit-${test_name} COMMAND unit-${test_name})
endforeach()

# Formatting is checked, not applied: .clang-format is the authority.
find_program(CLANG_FORMAT clang-format)
if(CLANG_FORMAT)
  add_test(NAME format
           COMMAND ${CLANG_FORMAT} --dry-run -Werror
                   ${MINIQU_SOURCES} ${MINIQU_HEADERS} ${MINIQU_UNIT_TESTS} ${MINIQU_UNIT_HEADERS}
           WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
else()
  message(WARNING "clang-format not found: the format test is not registered")
endif()

#--------------------------------------------------------------------------------------------------
# The old solver (minisat/), frozen; it is the reference until the parity gate and is removed from
# this file by the last M1 task.  Its flags are untouched and -Werror does not apply to it.

add_library(miniqu-old-lib STATIC
    minisat/utils/Options.cc
    minisat/utils/System.cc
    minisat/core/Solver.cc
    minisat/core/QBFParser.cc
    minisat/core/QCIRParser.cc
    minisat/simp/SimpSolver.cc)

target_include_directories(miniqu-old-lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(miniqu-old-lib PUBLIC __STDC_FORMAT_MACROS __STDC_LIMIT_MACROS)
target_compile_options(miniqu-old-lib PRIVATE -Wall -Wno-parentheses -Wno-class-memaccess)
target_link_libraries(miniqu-old-lib PUBLIC ZLIB::ZLIB)
set_target_properties(miniqu-old-lib PROPERTIES CXX_STANDARD 17 OUTPUT_NAME "miniQU-old")

add_executable(miniQU-old minisat/simp/Main.cc)
set_target_properties(miniQU-old PROPERTIES CXX_STANDARD 17)
target_link_libraries(miniQU-old miniqu-old-lib)

if(STATIC_BINARIES)
  target_link_libraries(miniQU-old -static)
endif()

#--------------------------------------------------------------------------------------------------
# Installation targets:

install(TARGETS qlrup-trim RUNTIME DESTINATION bin)
