#!/bin/sh

g++ -I ~/souffle/include/ -I ~/boost_1_72_0/ -I /usr/local/include/antlr4-runtime/ -g -Wall -std=c++11 main.cpp -L~/boost_1_72_0/stage/lib/ -lpthread -lboost_filesystem -lboost_system
