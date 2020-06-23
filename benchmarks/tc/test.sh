#!/bin/bash

NODES=256
PROBABILITY=0.5

python3 rand_graph.py $NODES $PROBABILITY | tee edge.csv edge.facts > /dev/null

echo "Formulog:"
java -DminIndex=false -DcodeGen -jar $1 tc.flg \
  && ./codegen/compile.sh > /dev/null \
  && time ./codegen/flg > formulog.out

echo "Souffle:"
time souffle tc.dl > souffle.out
