#!/bin/sh

run() {
    cargo test --release --features "heap-profiling,circuit-params" test_mycircuit_full_split -- --nocapture
}

RESULTS=results.txt

for k in `seq 10 2 18`; do
    for wf in `seq 1 6`; do
        echo K=$k WIDTH_FACTOR=$wf
        K=$k WIDTH_FACTOR=$wf run | tee -a $RESULTS
    done
done
