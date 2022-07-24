#!/bin/bash

/* INSERT 0 */

if [ -z "$OUTPUT_EXEC" ] ; then
  >&2 echo '$OUTPUT_EXEC variable is empty'
  exit 1
fi

if [ -z "$SOUFFLE_INCLUDE" ] ; then
  >&2 echo '$SOUFFLE_INCLUDE variable is empty'
  exit 1
fi

if [ -z "$BOOST_INCLUDE" ] ; then
  >&2 echo '$BOOST_INCLUDE variable is empty'
  exit 1
fi

if [ -z "$BOOST_LIB" ] ; then
  >&2 echo '$BOOST_LIB variable is empty'
  exit 1
fi

OUTPUT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd $OUTPUT_DIR
g++ -fopenmp -I $SOUFFLE_INCLUDE -I $BOOST_INCLUDE -L$BOOST_LIB \
  -Wall -Wno-unused-variable -Wno-unused-but-set-variable \
  -std=c++17 -O3 -march=native -o $OUTPUT_EXEC main.cpp \
  -lpthread -lboost_filesystem -lboost_system -lboost_program_options
