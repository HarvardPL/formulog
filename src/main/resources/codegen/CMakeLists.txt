cmake_minimum_required(VERSION 3.21)
project(codegen)

set(CMAKE_CXX_STANDARD 17)

set(CMAKE_CXX_FLAGS "-D__EMBEDDED_SOUFFLE__ -DRAM_DOMAIN_SIZE=64 -Wall -Wno-unused-variable -Wno-unused-but-set-variable -Wno-c++11-narrowing")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -O3 -march=native")

add_executable(flg "")

set(SOUFFLE_FLAGS -w -j 2 -PRamSIPS:strict)

option(FLG_EAGER_EVAL "Generate code performing eager evaluation (requires custom Soufflé)" OFF)
if (FLG_EAGER_EVAL)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DFLG_EAGER_EVAL")
    set(SOUFFLE_FLAGS ${SOUFFLE_FLAGS} --eager-eval)
endif ()

option(FLG_RECORD_WORK "Report amount of work performed during evaluation (requires custom Soufflé)" OFF)
if (FLG_RECORD_WORK)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DFLG_RECORD_WORK")
    set(SOUFFLE_FLAGS ${SOUFFLE_FLAGS} --record-work)
endif ()

add_custom_command(OUTPUT formulog.cpp
        COMMAND souffle ${CMAKE_CURRENT_SOURCE_DIR}/src/formulog.dl ${SOUFFLE_FLAGS} -g formulog.cpp
        DEPENDS src/formulog.dl)

target_sources(flg PRIVATE
        src/time.hpp
        src/ConcurrentHashMap.hpp
        src/funcs.hpp
        src/functors.cpp
        src/functors.h
        src/main.cpp
        src/parser.cpp
        src/parser.hpp
        src/Symbol.cpp
        src/Symbol.hpp
        src/Term.cpp
        src/Term.hpp
        src/Type.hpp
        src/Type.cpp
        src/globals.h
        src/set.cpp
        src/set.hpp
        src/smt_solver.cpp
        src/smt_solver.h
        src/smt_shim.cpp
        src/smt_shim.h
        src/smt_parser.cpp
        src/smt_parser.hpp
        formulog.cpp
        )

find_package(Boost 1.81 REQUIRED COMPONENTS filesystem system program_options)
find_package(TBB REQUIRED)
target_link_libraries(flg PRIVATE ${Boost_LIBRARIES} TBB::tbb)

find_package(OpenMP)
if (OpenMP_CXX_FOUND)
    target_link_libraries(flg PRIVATE OpenMP::OpenMP_CXX)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fopenmp")
endif ()

option(FLG_DEV "Formulog codegen development mode" OFF)
if (FLG_DEV)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DFLG_DEV")
endif ()
