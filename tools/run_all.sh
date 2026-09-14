#!/bin/sh
# Runs every test in the README table and the axiom gate. Fails on the first failure.
set -eu
cd "$(dirname "$0")/.."
: "${ACC_OFFICIAL:?set ACC_OFFICIAL to a checkout of SAIRcompetition/Andrews-Curtis at a0fd6e6}"
python3 tools/diff_table.py
python3 tools/golden.py
python3 tools/fuzz_step.py --n 100000 --seed 20260913
python3 tools/fuzz_step.py --n 100000 --seed 7
python3 tools/gen_paths.py --n 400 --seed 20260913
python3 tools/run_corpus.py --seed 20260913 --mutants-per-path 4
python3 tools/kernel_theorems.py
python3 tools/axiom_gate.py --negative-control
echo "all tests passed"
