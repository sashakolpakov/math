#!/usr/bin/env bash
set -euo pipefail

source_dir=$(CDPATH= cd -- "$(dirname -- "$0")/source" && pwd)
output_dir=${1:-build}
compiler=${CXX:-g++}

if [[ -e "$output_dir" ]]; then
    printf 'Output directory already exists: %s\n' "$output_dir" >&2
    exit 2
fi
mkdir -- "$output_dir"
output_dir=$(CDPATH= cd -- "$output_dir" && pwd)
export LANG=C LC_ALL=C

cd -- "$source_dir"
"$compiler" -O3 -march=native -ffp-contract=off abi-fp-probe.cpp -o "$output_dir/abi-fp-probe-covrun"
"$output_dir/abi-fp-probe-covrun"
"$compiler" -std=gnu++17 -O3 -march=native -ffp-contract=off abi-fp-probe.cpp -o "$output_dir/abi-fp-probe-abc"
"$output_dir/abi-fp-probe-abc"

"$compiler" -O3 -march=native -ffp-contract=off covout.cpp -o "$output_dir/covrun"
"$compiler" -std=gnu++17 -O3 -march=native -ffp-contract=off atlas.cpp -o "$output_dir/arun"
"$compiler" -std=gnu++17 -O3 -march=native -ffp-contract=off stageB.cpp -o "$output_dir/brun"
"$compiler" -std=gnu++17 -O3 -march=native -ffp-contract=off stageC.cpp -o "$output_dir/crun"

nm -D "$output_dir/covrun" > "$output_dir/covrun.dynamic-symbols.txt"
objdump -d -C "$output_dir/covrun" > "$output_dir/covrun.disassembly.txt"
printf 'Built numerical programs in %s\nInspect both cover-square instruction sequences before relying on a fresh run.\n' "$output_dir"
