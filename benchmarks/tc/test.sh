#!/bin/bash

NODES=256
PROBABILITY=0.5

python3 rand_graph.py $NODES $PROBABILITY | tee edge.csv edge.facts > /dev/null

echo -n "Formulog:"
java -DminIndex=false -DcodeGen -jar $1 tc.flg \
  && ./codegen/compile.sh 2> /dev/null \
  && time ./codegen/flg --no-dump > formulog.out

echo -n "Souffle:"
souffle -o souffle tc.dl \
  && time ./souffle > souffle.out
