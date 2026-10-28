# MUB dimension-six verification materials

This directory contains the numerical source code, the saved numerical data,
and the command/result facts needed to check the coverage of the saved run.
It contains no compiled programs, archive inventories, hash checks, raw process
logs, machine/session records, supervision code, or review narratives.
The `.bin` files under `execution/data/` are numerical records, not executable
programs.

## Check the saved numerical record

Run with Python 3.9 or newer:

```sh
python3 execution/check_records.py
```

The checker reads only `execution/data/`, `execution/commands.json`, and
`execution/results/`. It checks complete parsing and end-of-file, valid record
bounds, the four A shards, B parent/output counts, the fine-to-batch partition,
ordered C failure subsequences, the fallback input order, and complete final
modulo-four coverage with no unresolved records. It does not run the numerical
C++ programs.

The command and result files contain only relative program/data names,
mathematical arguments, completion/exit facts, and numerical counters. Timing,
PID, host, absolute-path, resource, and provenance fields are not required.

This is a numerical consistency check, not an authentication of the historical
archive, a proof of the C++ implementation, or a verification of compiler and
hardware behavior. Those are separate questions.

## Build the numerical programs

The seven mathematical C++ files are in `compiled-build/source/`. The small
`abi-fp-probe.cpp` checks part of the required arithmetic and binary-format
contract. Build into a new directory on a compatible x86-64 GNU/Linux system:

```sh
bash compiled-build/build.sh /path/to/new/build-directory
```

The build script uses GCC/g++, Bash, GNU binutils, and no external numerical
library. It does not require an inventory or any hash metadata. It does not run
the full numerical computation.

Required arithmetic conditions include IEEE binary64 with 53 significand bits,
round-to-nearest, correctly rounded binary64 square root, `FLT_EVAL_METHOD == 0`,
gradual underflow, masked floating-point exceptions, and no fast math,
reassociation, or contraction of separate operations. These conditions must
hold at process startup, including global initialization. The record format
requires little-endian eight-bit bytes, 32-bit `int`, and the documented 64-bit
sizes and unsigned-long ABI. The probe tests samples and ABI properties; it is
not a formal proof of all machine behavior.

The build creates disassembly and dynamic-symbol listings for `covrun`. Before
using a fresh run as evidence, inspect the two `pow(..., 2)` expressions in
`coverSeeds::run`: the scale, square, subtraction, square root, addition, and
second square must use the separately rounded binary64 operations assumed by
the manuscript. Merely finding no dynamic `pow` symbol is insufficient.

## Mathematical run schedule

The saved command records specify this schedule using relative filenames:

1. Generate the complete `centers.txt` with `covrun`.
2. Run A parts 0, 1, 2, and 3 modulo 4 on all centers.
3. Run B with target/width `.07 .013` on all four coarse files in part order.
4. Run B with target/width `.016 .005` on the complete mid output, producing
   consecutive batches of at most 256 records.
5. Run C on every batch with `12 4 1 .042 1 1 5000000 0 1`.
6. If initial C failures exist, run B with `.011 .0038` on every nonempty C bad
   file in ASCII filename order.
7. Run final C parts 0, 1, 2, and 3 modulo 4 on the complete fallback output,
   using `12 4 1 .042 1 1 5000000`.

An initial C exit of 1 denotes unresolved records and is valid only when every
such record enters the fallback. A final unresolved record is not a negative
certificate. The empty and zero-count bad files in `execution/data/` are
therefore part of the numerical evidence, not disposable notes.
