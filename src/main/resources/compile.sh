#!/bin/sh

g++ -I ~/souffle/include/ -I ~/boost_1_72_0/ -I /usr/local/include/antlr4-runtime/ -g -Wall -Wno-trigraphs -std=c++11 main.cpp parsing/FormulogParser.cpp parsing/FormulogLexer.cpp -L~/boost_1_72_0/stage/lib/ -lpthread -lboost_filesystem -lboost_system -lboost_program_options -lantlr4-runtime
