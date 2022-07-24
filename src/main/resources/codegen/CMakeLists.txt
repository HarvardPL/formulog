cmake_minimum_required(VERSION 3.21)
project(codegen)

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_CXX_FLAGS "-D__EMBEDDED_SOUFFLE__ -O3 -march=native -Wall -Wno-unused-variable -Wno-unused-but-set-variable -Wno-c++11-narrowing")

add_executable(flg "")

add_custom_command(OUTPUT formulog.cpp
        COMMAND souffle ${CMAKE_CURRENT_SOURCE_DIR}/src/formulog.dl -w -g formulog.cpp
        DEPENDS src/formulog.dl)

target_sources(flg PRIVATE
        src/funcs.hpp
        src/main.cpp
        src/parser.cpp
        src/parser.hpp
        src/rels.hpp
        src/smt.cpp
        src/smt.hpp
        src/Symbol.cpp
        src/Symbol.hpp
        src/Term.cpp
        src/Term.hpp
        src/Tuple.hpp
        src/Type.hpp
        formulog.cpp
        )

find_package(Boost 1.79 REQUIRED COMPONENTS filesystem system program_options)
find_package(TBB REQUIRED)
target_link_libraries(flg PRIVATE ${Boost_LIBRARIES} TBB::tbb)

find_package(OpenMP)
if (OpenMP_CXX_FOUND)
    target_link_libraries(flg PRIVATE OpenMP::OpenMP_CXX)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fopenmp")
endif ()

if (DEFINED ENV{FLG_DEV})
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DFLG_DEV")
endif ()
