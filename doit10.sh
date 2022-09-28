#!/bin/bash
time(
for i in {1..10}
do
    dune exec nuscr -- --show-global-type1=$1 examples/presentationExamples/original/$1.scr 2>>log
done
)
