#!/bin/bash

NODES=256
PROBABILITY=0.5

if [ -z "$1" ] ; then
  >&2 echo 'Missing path to formulog.jar'
  exit 1
fi

python3 rand_graph.py $NODES $PROBABILITY | tee edge.csv edge.facts > /dev/null

echo -n "Formulog:"
java -DminIndex=false -DcodeGen -jar $1 tc.flg \
  && make -C codegen > /dev/null \
  && time ./codegen/flg --no-dump > formulog.out

echo -n "Souffle:"
souffle -o sfl tc.dl \
  && time ./sfl > souffle.out
