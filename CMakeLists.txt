cmake_minimum_required(VERSION 3.10)

project(miniQU CXX)

#--------------------------------------------------------------------------------------------------
# Configurable options:

option(STATIC_BINARIES "Link binaries statically." OFF)

if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
  set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type." FORCE)
endif()

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

#--------------------------------------------------------------------------------------------------
# Dependencies:

find_package(ZLIB REQUIRED)

#--------------------------------------------------------------------------------------------------
# Build Targets:

add_library(miniqu-lib STATIC
    minisat/utils/Options.cc
    minisat/utils/System.cc
    minisat/core/Solver.cc
    minisat/core/QBFParser.cc
    minisat/core/QCIRParser.cc
    minisat/simp/SimpSolver.cc)

target_include_directories(miniqu-lib PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_definitions(miniqu-lib PUBLIC __STDC_FORMAT_MACROS __STDC_LIMIT_MACROS)
target_compile_options(miniqu-lib PRIVATE -Wall -Wno-parentheses -Wno-class-memaccess)
target_link_libraries(miniqu-lib PUBLIC ZLIB::ZLIB)
set_target_properties(miniqu-lib PROPERTIES OUTPUT_NAME "miniQU")

# The solver for QDIMACS and QCIR input.
add_executable(miniQU minisat/simp/Main.cc)
target_link_libraries(miniQU miniqu-lib)

# Proof trimmer (see doc/proof-format.md).
add_executable(qlrup-trim tools/qlrup-trim.cc)

if(STATIC_BINARIES)
  target_link_libraries(miniQU -static)
endif()

#--------------------------------------------------------------------------------------------------
# Tests:

enable_testing()
add_test(NAME fuzz-dependency-learning
         COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tests/fuzz.sh $<TARGET_FILE:miniQU> 1 20 -dl)
add_test(NAME fuzz-prefix-order
         COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tests/fuzz.sh $<TARGET_FILE:miniQU> 1 20)

#--------------------------------------------------------------------------------------------------
# Installation targets:

install(TARGETS miniQU qlrup-trim miniqu-lib
        RUNTIME DESTINATION bin
        ARCHIVE DESTINATION lib)

install(DIRECTORY minisat/mtl minisat/utils minisat/core minisat/simp
        DESTINATION include/minisat
        FILES_MATCHING PATTERN "*.h")
