#!/bin/bash
time (
for i in {1..10}
do
    dune exec nuscr -- --graceful-failure=$1 examples/presentationExamples/original/$1.nuscr
done
)