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

if [ -z "$ANTLR_INCLUDE" ] ; then
  >&2 echo '$ANTLR_INCLUDE variable is empty'
  exit 1
fi

if [ -z "$BOOST_LIB" ] ; then
  >&2 echo '$BOOST_LIB variable is empty'
  exit 1
fi

OUTPUT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd $OUTPUT_DIR
g++ -fopenmp -I $SOUFFLE_INCLUDE -I $BOOST_INCLUDE -I $ANTLR_INCLUDE -Wall -Wno-trigraphs -std=c++17 \
  -o $OUTPUT_EXEC main.cpp parsing/FormulogParser.cpp parsing/FormulogLexer.cpp \
  -L$BOOST_LIB -lpthread -lboost_filesystem -lboost_system -lboost_program_options -lantlr4-runtime
