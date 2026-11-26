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

# Link-time optimisation (the release presets): GCC's default of a serial link-time
# compilation prints "lto-wrapper: warning: using serial compilation"; "auto" lets it
# use the jobserver or the available cores.  clang keeps CMake's own flags.
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  set(CMAKE_CXX_COMPILE_OPTIONS_IPO -flto=auto -fno-fat-lto-objects)
endif()

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
file(GLOB MINIQU_TOOL_SOURCES CONFIGURE_DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/test/tools/*.cpp)

# The frontend talks to the solver through miniqu.hpp only, so it is a set of
# objects that is linked either with the real solver or with the fake one of
# the unit tests.
set(MINIQU_FRONTEND_SOURCES
    ${CMAKE_CURRENT_SOURCE_DIR}/src/circuit.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/src/parse_qcir.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/src/parse_qdimacs.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/src/encode.cpp)
# The application layer: main, signals, process limits.
set(MINIQU_APP_SOURCES
    ${CMAKE_CURRENT_SOURCE_DIR}/src/app.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/src/signal.cpp
    ${CMAKE_CURRENT_SOURCE_DIR}/src/resources.cpp)
set(MINIQU_LIBRARY_SOURCES ${MINIQU_SOURCES})
list(REMOVE_ITEM MINIQU_LIBRARY_SOURCES ${MINIQU_FRONTEND_SOURCES} ${MINIQU_APP_SOURCES})

add_library(miniqu STATIC ${MINIQU_LIBRARY_SOURCES})
target_include_directories(miniqu PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/src)
target_compile_options(miniqu PRIVATE ${MINIQU_WARNINGS})
target_link_libraries(miniqu PUBLIC ZLIB::ZLIB)

add_library(miniqu-frontend OBJECT ${MINIQU_FRONTEND_SOURCES})
target_compile_options(miniqu-frontend PRIVATE ${MINIQU_WARNINGS})
target_link_libraries(miniqu-frontend PUBLIC miniqu)

add_executable(miniQU ${MINIQU_APP_SOURCES})
target_compile_options(miniQU PRIVATE ${MINIQU_WARNINGS})
target_link_libraries(miniQU PRIVATE miniqu-frontend miniqu)

if(STATIC_BINARIES)
  target_link_libraries(miniQU -static)
endif()

# Proof trimmer (see doc/proof-format.md).
add_executable(qlrup-trim tools/qlrup-trim.cc)

if(STATIC_BINARIES)
  target_link_libraries(qlrup-trim -static)
endif()

enable_testing()

# A link-time substitute for the solver, which records what the frontend
# does.  It is not a unit test of its own.
set(MINIQU_FAKE_SOLVER ${CMAKE_CURRENT_SOURCE_DIR}/test/unit/fake_solver.cpp)
list(REMOVE_ITEM MINIQU_UNIT_TESTS ${MINIQU_FAKE_SOLVER})
add_library(miniqu-fake-solver STATIC ${MINIQU_FAKE_SOLVER})
target_include_directories(miniqu-fake-solver PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/test/unit)
target_compile_options(miniqu-fake-solver PRIVATE ${MINIQU_WARNINGS})
target_link_libraries(miniqu-fake-solver PUBLIC miniqu)

# Unit tests of the frontend run against the fake solver, end-to-end tests
# against the real one.
set(MINIQU_FRONTEND_TESTS circuit parse_qcir parse_qdimacs encode)
set(MINIQU_END_TO_END_TESTS regressions)

# One executable per file in test/unit, each a ctest test of the same name.
add_custom_target(unit-tests)
foreach(test_source ${MINIQU_UNIT_TESTS})
  get_filename_component(test_name ${test_source} NAME_WE)
  add_executable(unit-${test_name} ${test_source})
  if(test_name IN_LIST MINIQU_FRONTEND_TESTS)
    target_link_libraries(unit-${test_name} PRIVATE miniqu-frontend miniqu-fake-solver)
  elseif(test_name IN_LIST MINIQU_END_TO_END_TESTS)
    target_link_libraries(unit-${test_name} PRIVATE miniqu-frontend miniqu)
    target_compile_definitions(unit-${test_name} PRIVATE
                               MINIQU_REGRESSIONS="${CMAKE_CURRENT_SOURCE_DIR}/tests/regressions")
  else()
    target_link_libraries(unit-${test_name} PRIVATE miniqu)
  endif()
  target_include_directories(unit-${test_name} PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/test/unit)
  target_compile_options(unit-${test_name} PRIVATE ${MINIQU_WARNINGS})
  # GCC 12/13 at -O3 without LTO report a spurious -Wfree-nonheap-object on
  # temporary std::vector comparisons in the tests (propagate_ldq.cpp).
  if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
    target_compile_options(unit-${test_name} PRIVATE -Wno-free-nonheap-object)
  endif()
  add_dependencies(unit-tests unit-${test_name})
  add_test(NAME unit-${test_name} COMMAND unit-${test_name})
endforeach()

# Prints the encoding of a file as the fake solver sees it; tests/encoding_diff.sh
# compares it with the original constraints of the baseline's proofs.
add_executable(encoding-dump test/tools/encoding_dump.cpp)
target_link_libraries(encoding-dump PRIVATE miniqu-frontend miniqu-fake-solver)
target_include_directories(encoding-dump PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/test/unit)
target_compile_options(encoding-dump PRIVATE ${MINIQU_WARNINGS})
add_test(NAME encoding-diff
         COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tests/encoding_diff.sh 1 50
         WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
set_tests_properties(encoding-diff PROPERTIES
                     ENVIRONMENT ENCODING_DUMP=$<TARGET_FILE:encoding-dump>)

# End-to-end: 20 fuzz seeds of the default and the dependency-learning
# configuration against the baseline and the brute-force evaluator, and the
# regression instances, with their proofs checked by the Lean checker.
add_test(NAME fuzz
         COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tests/regress.sh -S -s 1:20 -M default,dl -j 8
                 $<TARGET_FILE:miniQU>
         WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
set_tests_properties(fuzz PROPERTIES ENVIRONMENT REGRESS_WORK=${CMAKE_BINARY_DIR}/regress)
add_test(NAME run-regressions
         COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tests/run_regressions.sh $<TARGET_FILE:miniQU>
         WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
# Elimination makes root-cert-elim.sat.qcir decided at the root (B1).
add_test(NAME run-regressions-elim
         COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tests/run_regressions.sh $<TARGET_FILE:miniQU> --elim
         WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})

# The tooling's own tests: paired statistics of bench/compare.py, evaluator.
find_package(Python3 REQUIRED COMPONENTS Interpreter)
add_test(NAME bench-compare
         COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/bench/test_compare.py)
add_test(NAME bench-gate
         COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/bench/test_gate.py)
add_test(NAME bench-load-measure
         COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/bench/test_load_measure.py)
add_test(NAME bench-l3-table
         COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/bench/test_l3_table.py)
add_test(NAME regress-limits
         COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tests/test_regress_limits.sh
         WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
set_tests_properties(regress-limits PROPERTIES ENVIRONMENT REGRESS_WORK=${CMAKE_BINARY_DIR}/regress)
add_test(NAME qcir-eval
         COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/tests/test_qcir_eval.py)

# Formatting is checked, not applied: .clang-format is the authority.
find_program(CLANG_FORMAT clang-format)
if(CLANG_FORMAT)
  add_test(NAME format
           COMMAND ${CLANG_FORMAT} --dry-run -Werror
                   ${MINIQU_SOURCES} ${MINIQU_HEADERS} ${MINIQU_FAKE_SOLVER} ${MINIQU_UNIT_TESTS} ${MINIQU_UNIT_HEADERS}
                   ${MINIQU_TOOL_SOURCES}
           WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
else()
  message(WARNING "clang-format not found: the format test is not registered")
endif()

#--------------------------------------------------------------------------------------------------
# Installation targets:

install(TARGETS miniQU qlrup-trim RUNTIME DESTINATION bin)
