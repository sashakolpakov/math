#!/usr/bin/env python3
"""Numerically audit the finite estimates in the stick-knot manuscript.

The upper calculation uses the same unsliced, redundantly indexed family as
the Lean certificate: ``m = 3N`` variables and ``S = N + N^2`` polynomial
slots. Keeping the binomial denominator visible changes the crude quadratic
base into a linear base.

The lower calculation uses the explicit quarter-family
``(k!)^4 <= |G_{4k}|`` at

    q = floor(log N),
    k = floor((2N+15)/(12(q+9))).

It checks the exact stick budget and compares the factorial lower count with
the factorial-free Stirling envelope used by Lean. This script is a numerical
audit, not a substitute for the cited real-algebraic, braid-theoretic, or
knot-theoretic inputs.
"""

from __future__ import annotations

import argparse
import itertools
import math


def log_choose(n: int, j: int) -> float:
    return math.lgamma(n + 1) - math.lgamma(j + 1) - math.lgamma(n - j + 1)


def logsumexp(values: list[float]) -> float:
    pivot = max(values)
    return pivot + math.log(sum(math.exp(value - pivot) for value in values))


def descent_set(permutation: tuple[int, ...]) -> frozenset[int]:
    return frozenset(
        i + 1
        for i in range(len(permutation) - 1)
        if permutation[i] > permutation[i + 1]
    )


def report_doubly_alternating(limit: int = 9) -> None:
    """Enumerate small doubly down--up sets and check the quarter bound."""
    print("small-n check: n |G_n| explicit-quarter-lower")
    for n in range(3, limit + 1):
        target = frozenset(range(1, n, 2))
        count = 0
        for permutation in itertools.permutations(range(n)):
            if descent_set(permutation) != target:
                continue
            inverse = [0] * n
            for i, value in enumerate(permutation):
                inverse[value] = i
            if descent_set(tuple(inverse)) == target:
                count += 1
        quarter_lower = math.factorial(n // 4) ** 4 if n % 4 == 0 else 0
        if quarter_lower:
            assert quarter_lower <= count
        print(f"n={n:2d} |G_n|={count:7d} quarter={quarter_lower:7d}")


def report(vertex_count: int) -> None:
    if vertex_count < 5:
        raise ValueError("the uniform unsliced calculation starts at N=5")

    dimension = 3 * vertex_count
    slots = vertex_count + vertex_count**2
    binomial_n = slots + 1
    assert dimension <= binomial_n // 2

    log_weighted = logsumexp(
        [j * math.log(4.0) + log_choose(binomial_n, j)
         for j in range(dimension + 1)]
    )
    log_envelope = (
        math.log(dimension + 1)
        + dimension * math.log(12.0 * binomial_n / dimension)
    )
    log_naive = dimension * math.log(binomial_n)
    assert log_weighted <= log_envelope + 1e-8 * max(1.0, log_envelope)

    scale = vertex_count * math.log(vertex_count)
    q = int(math.log(vertex_count))
    k = (2 * vertex_count + 15) // (12 * (q + 9))

    if q >= 2 and k >= 1:
        arc_budget = 4 * k * max(11, q + 9) - 4
        stick_twice = 3 * (arc_budget - 1)
        assert stick_twice <= 2 * vertex_count

        log_lower = (
            4 * q * math.lgamma(k + 1)
            - math.lgamma(4 * k + 1)
            - math.log(2.0)
        )
        stirling_envelope = (
            (q - 1) * (4 * k * math.log(4 * k) - 4 * k)
            - 9 * q * k * math.log(2.0)
            - math.log(2.0)
        )
        assert stirling_envelope <= log_lower + 1e-8 * max(1.0, abs(log_lower))
        lower_text = f"{log_lower / scale:8.5f}"
        stirling_text = f"{stirling_envelope / scale:8.5f}"
        stick_text = f"{stick_twice // 2:6d}"
    else:
        lower_text = stirling_text = "     n/a"
        stick_text = "   n/a"

    print(
        f"N={vertex_count:6d} S={slots:12d} m={dimension:7d} "
        f"weighted={log_weighted / scale:8.5f} "
        f"envelope={log_envelope / scale:8.5f} "
        f"naive={log_naive / scale:8.5f} "
        f"lower={lower_text} stirling={stirling_text} "
        f"q={q:3d} k={k:5d} stick-cap={stick_text}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "N",
        nargs="*",
        type=int,
        default=[6, 10, 20, 50, 100, 500, 2000],
    )
    parser.add_argument(
        "--check-doubly-alternating",
        action="store_true",
        help="enumerate the doubly down--up sets for 3 <= n <= 9",
    )
    args = parser.parse_args()
    if args.check_doubly_alternating:
        report_doubly_alternating()
    for vertex_count in args.N:
        report(vertex_count)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
