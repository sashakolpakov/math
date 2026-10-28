#!/usr/bin/env python3
"""Check the numerical consistency of the curated MUB d=6 execution subset.

This is a derived checker, not the original audit. It reads data, cleaned
numerical result lines, and a minimal command record. It does not execute any
archived program or verify source, binary, or original execution provenance.
"""

import argparse
import json
import math
from pathlib import Path
import re
import struct
import sys


C_ARGS = ["12", "4", "1", ".042", "1", "1", "5000000"]
CHILD_FIELDS = {
    "stage", "argv", "inputs", "outputs", "returncode", "completed", "stderr_empty"
}
B_STATS = (
    r"parent(\d+) base(\d+) inside(\d+) live(\d+) split(\d+) "
    r"snaps(\d+) bad(\d+) fail(\d+) pair(\d+)/(\d+) marks(\d+)"
)
C_COUNTS = r"done(\d+) bad(\d+) \(graph(\d+) cap(\d+) over(\d+) cluster(\d+)\)"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def read_lines(path):
    raw = path.read_bytes()
    need(not raw or raw.endswith(b"\n"), f"unterminated text: {path}")
    return raw.decode("ascii").splitlines()


def check_tree_membership(root, expected_files, label):
    expected_directories = {
        Path(*Path(name).parts[:index]).as_posix()
        for name in expected_files
        for index in range(1, len(Path(name).parts))
    }
    actual_files = set()
    actual_directories = set()
    for path in root.rglob("*"):
        name = path.relative_to(root).as_posix()
        if path.is_dir():
            actual_directories.add(name)
        elif path.is_file():
            actual_files.add(name)
        else:
            raise ValueError(f"unsupported entry in {label}: {name}")
    need(actual_files == expected_files,
         f"{label} file membership differs; missing={sorted(expected_files - actual_files)}, "
         f"extra={sorted(actual_files - expected_files)}")
    need(actual_directories == expected_directories,
         f"{label} directory membership differs; "
         f"missing={sorted(expected_directories - actual_directories)}, "
         f"extra={sorted(actual_directories - expected_directories)}")


class Records:
    """Stream the little-endian record format and enforce its numerical bounds."""

    def __init__(self, path, radius):
        self.path = path
        self.radius = radius
        with path.open("rb") as stream:
            header = stream.read(8)
        need(len(header) == 8, f"missing count header: {path}")
        self.count = struct.unpack("<Q", header)[0]
        need(self.count <= 2_000_000, f"record count exceeds native cap: {path}")

    def __iter__(self):
        with self.path.open("rb") as stream:
            header = stream.read(8)
            need(len(header) == 8 and struct.unpack("<Q", header)[0] == self.count,
                 f"count header differs: {self.path}")
            for index in range(self.count):
                lead = stream.read(4)
                need(len(lead) == 4, f"truncated dimension: {self.path}/{index}")
                dimension = struct.unpack("<i", lead)[0]
                need(0 <= dimension <= 10, f"invalid dimension: {self.path}/{index}")
                length = 8 * (36 + 36 * dimension + 8)
                body = stream.read(length)
                need(len(body) == length, f"truncated record: {self.path}/{index}")
                values = struct.unpack("<" + "d" * (length // 8), body)
                need(all(math.isfinite(value) for value in values),
                     f"nonfinite record: {self.path}/{index}")
                need(all(abs(value) <= 4 for value in values[:36])
                     and all(abs(value) <= 1.01 for value in values[36:-8]),
                     f"phase/tangent bounds: {self.path}/{index}")
                c, n, ident, ort, hor, norm, root, radius = values[-8:]
                need(0 <= c < 20 and 0 <= n < 1e-6 and 0 <= root < 1e-6
                     and 0 <= ident < 1e-4 and 0 <= ort < 1e-5
                     and 0 <= hor < 1e-5 and 0 <= norm < 2
                     and 0 <= radius <= self.radius,
                     f"scalar/radius bounds: {self.path}/{index}")
                yield lead + body
            need(stream.read(1) == b"", f"trailing bytes: {self.path}")

    def verify(self):
        for _ in self:
            pass
        return self


class NumericalCheck:
    def __init__(self, execution_directory):
        self.root = execution_directory
        self.data = self.root / "data"
        self.results = self.root / "results"
        need(self.data.is_dir() and self.results.is_dir(),
             "execution directory must contain data/ and results/")
        document = json.loads((self.root / "commands.json").read_text(encoding="utf-8"))
        need(type(document) is dict and set(document) == {"children"}
             and type(document["children"]) is dict, "invalid commands.json structure")
        self.commands = document["children"]
        need(all(type(key) is str for key in self.commands), "child identifiers must be strings")
        self.seen_children = set()
        self.expected_data = set()

    def data_path(self, name):
        self.expected_data.add(name)
        return self.data / name

    def records(self, name, radius, empty=False):
        records = Records(self.data_path(name), radius).verify()
        if empty:
            need(records.count == 0, f"nonempty terminal bad file: {name}")
        return records

    def child(self, key, stage, argv, inputs, outputs, returncode):
        need(key not in self.seen_children, f"duplicate child: {key}")
        need(key in self.commands, f"missing child: {key}")
        row = self.commands[key]
        need(type(row) is dict and set(row) == CHILD_FIELDS,
             f"unexpected child fields: {key}")
        need(row["stage"] == stage and row["argv"] == argv,
             f"stage or command arguments differ: {key}")
        need(row["inputs"] == inputs and row["outputs"] == outputs,
             f"command operands differ: {key}")
        need(type(row["returncode"]) is int and row["returncode"] == returncode,
             f"unexpected return code: {key}")
        need(row["completed"] is True and row["stderr_empty"] is True,
             f"child is incomplete or has nonempty stderr: {key}")
        self.seen_children.add(key)
        return read_lines(self.results / f"{key}.txt")

    def stage_b(self, key, stage, target, width, output, bad, prefix, inputs, parent_count):
        out = self.records(output, float(target))
        self.records(bad, .126, empty=True)
        lines = self.child(
            key, stage, ["./build/brun", target, width, output, bad, prefix, *inputs],
            inputs, [output, bad], 0
        )
        need(len(lines) == parent_count // 50 + 1,
             f"B progress lines omitted or extra: {key}")
        previous_stats = [0] * 11
        previous_output = 0
        for index, line in enumerate(lines[:-1]):
            match = re.fullmatch(r"done(\d+)/(\d+) ->(\d+) bad(\d+) " + B_STATS, line)
            need(match is not None, f"unexpected B progress line: {key}/{index}")
            done, parents, current_output, failed, *stats = map(int, match.groups())
            need(done == stats[0] == 50 * (index + 1) and parents == parent_count,
                 f"B parent coverage differs: {key}/{index}")
            need(failed == 0 and stats[7] == 0, f"B failed parent: {key}/{index}")
            need(previous_output <= current_output <= out.count,
                 f"B output count decreases or exceeds output: {key}/{index}")
            need(all(left <= right for left, right in zip(previous_stats, stats)),
                 f"B counters decrease: {key}/{index}")
            previous_output = current_output
            previous_stats = stats
        terminal = re.fullmatch(r"result (\d+) bad (\d+) " + B_STATS, lines[-1])
        need(terminal is not None, f"B terminal summary missing or malformed: {key}")
        output_count, failed, *stats = map(int, terminal.groups())
        need((output_count, failed, stats[0], stats[7]) == (out.count, 0, parent_count, 0),
             f"B terminal counts or failures differ: {key}")
        need(all(left <= right for left, right in zip(previous_stats, stats)),
             f"B terminal counters decrease: {key}")
        return out

    def stage_c(self, key, stage, input_name, bad, radius, part=0, parts=1, final=False):
        source = self.records(input_name, radius)
        failures = self.records(bad, radius, empty=final)
        lines = self.child(
            key, stage,
            ["./build/crun", *C_ARGS, str(part), str(parts), bad, input_name],
            [input_name], [bad], int(failures.count > 0)
        )
        need(bool(lines), f"C result is empty: {key}")
        previous = [0] * 6
        for index, line in enumerate(lines):
            terminal = index == len(lines) - 1
            match = re.fullmatch((r"result " if terminal else "") + C_COUNTS, line)
            need(match is not None, f"unexpected C result line: {key}/{index}")
            values = list(map(int, match.groups()))
            done, bad_count, *categories = values
            need(bad_count == sum(categories) <= done,
                 f"C category sum differs: {key}/{index}")
            need(all(left <= right for left, right in zip(previous, values)),
                 f"C counters decrease: {key}/{index}")
            need(all(right - left <= done - previous[0]
                     for left, right in zip(previous[1:], values[1:])),
                 f"C failure counts advance too far: {key}/{index}")
            if not terminal:
                need(done == 100 * (index + 1), f"C progress coverage differs: {key}/{index}")
            previous = values
        need(len(lines) - 1 == previous[0] // 100, f"C progress lines omitted or extra: {key}")
        need(previous[0] == len(range(part, source.count, parts))
             and previous[1] == failures.count, f"C done/bad counts differ: {key}")
        failed_records = iter(failures)
        pending = next(failed_records, None)
        for index, record in enumerate(source):
            if index % parts == part and pending is not None and pending == record:
                pending = next(failed_records, None)
        need(pending is None, f"C failures are not an ordered assigned-input subsequence: {key}")
        return dict(zip(("done", "bad", "graph", "cap", "over", "cluster"), previous))

    def execute(self):
        centers = read_lines(self.data_path("centers.txt"))
        need(bool(centers) and re.fullmatch(r"112 [1-9][0-9]*", centers[0]),
             "invalid centers header")
        center_count = int(centers[0].split()[1])
        need(center_count <= 2_000_000 and len(centers) == center_count + 1,
             "centers count or EOF mismatch")
        for index, line in enumerate(centers[1:]):
            fields = line.split()
            need(len(fields) == 10 and all(re.fullmatch(r"[0-9]+", value) for value in fields),
                 f"invalid center row: {index}")
            values = list(map(int, fields))
            need(all(0 <= value < 112 for column, value in enumerate(values) if column != 5)
                 and 0 <= values[5] < 5, f"center bounds differ: {index}")
        cover_lines = self.child(
            "covrun", "cov", ["./build/covrun", "centers.txt"], [], ["centers.txt"], 0
        )
        need(len(cover_lines) == 3 and re.fullmatch(r"xs [1-9][0-9]*", cover_lines[0]),
             "cover seed completion is absent or malformed")
        cover = re.fullmatch(r"N112 r0\.0320 dual2 checked(\d+) centers(\d+)", cover_lines[1])
        need(cover is not None and int(cover[2]) == center_count,
             "cover terminal center count differs")
        need(cover_lines[2] == "completed_write", "cover completed-write marker absent")

        coarse = []
        for part in range(4):
            output, bad, key = f"coarse{part}.bin", f"bad{part}.txt", f"A{part}"
            out = self.records(output, .126)
            need(self.data_path(bad).read_bytes() == b"", f"A terminal bad file is nonempty: {bad}")
            lines = self.child(
                key, "A", ["./build/arun", "centers.txt", str(part), "4", output, bad],
                ["centers.txt"], [output, bad], 0
            )
            assigned = len(range(part, center_count, 4))
            need(len(lines) == assigned // 1000 + 1, f"A progress lines omitted or extra: {key}")
            previous_global = 0
            for index, line in enumerate(lines[:-1]):
                match = re.fullmatch(r"done (\d+) G(\d+) failedBalls(\d+)", line)
                need(match is not None, f"unexpected A progress line: {key}/{index}")
                done, global_count, failed = map(int, match.groups())
                need(done == 1000 * (index + 1) and failed == 0,
                     f"A progress coverage or failure differs: {key}/{index}")
                need(previous_global <= global_count <= out.count,
                     f"A global count decreases or exceeds output: {key}/{index}")
                previous_global = global_count
            terminal = re.fullmatch(r"total done(\d+) global(\d+) failedBalls(\d+)", lines[-1])
            need(terminal is not None and tuple(map(int, terminal.groups())) == (assigned, out.count, 0),
                 f"A terminal coverage or failures differ: {key}")
            coarse.append(out)

        coarse_count = sum(records.count for records in coarse)
        need(0 < coarse_count <= 8_000_000, "Bmid parent total is outside native cap")
        mid = self.stage_b(
            "Bmid", "Bmid", ".07", ".013", "mid.bin", "midbad.bin", "-",
            [f"coarse{part}.bin" for part in range(4)], coarse_count
        )
        need(mid.count > 0, "Bfine has no parents")
        fine = self.stage_b(
            "Bfine", "Bfine", ".016", ".005", "fine.bin", "finebad.bin", "batches/f",
            ["mid.bin"], mid.count
        )
        marker = read_lines(self.data_path("batches/fdone.txt"))
        need(len(marker) == 1 and re.fullmatch(r"[0-9]+ [0-9]+", marker[0]),
             "invalid batch completion marker")
        batch_count, total = map(int, marker[0].split())
        need(total == fine.count and batch_count == (total + 255) // 256 and total > 0,
             "batch marker does not completely cover nonempty fine output")
        fine_records = iter(fine)
        for index in range(batch_count):
            batch = self.records(f"batches/f{index}.bin", .016)
            need(batch.count == min(256, total - 256 * index), f"batch partition differs: {index}")
            for record in batch:
                original = next(fine_records, None)
                need(original is not None and record[:-8] == original[:-8]
                     and record[-8:] == struct.pack("<d", .016),
                     f"batch differs beyond radius or insertion order: {index}")
        need(next(fine_records, None) is None, "fine records omitted from batches")

        initial = dict.fromkeys(("done", "bad", "graph", "cap", "over", "cluster"), 0)
        fallback_inputs = []
        for index in range(batch_count):
            row = self.stage_c(
                f"C.batch{index}", "C.initial", f"batches/f{index}.bin",
                f"batches/bad{index}.bin", .016
            )
            for name, value in row.items():
                initial[name] += value
            if row["bad"]:
                fallback_inputs.append(f"batches/bad{index}.bin")
        need(initial["done"] == total, "initial C omits fine records")
        fallback_inputs.sort(key=lambda name: name.encode("ascii"))

        fallback_count = 0
        final = []
        if fallback_inputs:
            fallback = self.stage_b(
                "C.Bfallback", "C.fallback", ".011", ".0038", "fb1.bin", "fb1bad.bin", "-",
                fallback_inputs, initial["bad"]
            )
            fallback_count = fallback.count
            final = [
                self.stage_c(
                    f"C.final{part}", "C.final", "fb1.bin", f"fb1cbad{part}.bin", .011,
                    part, 4, final=True
                )
                for part in range(4)
            ]
            need(sum(row["done"] for row in final) == fallback.count
                 and all(row["bad"] == 0 for row in final),
                 "final C partition or failures differ")

        need(set(self.commands) == self.seen_children,
             f"child membership differs; extra={sorted(set(self.commands) - self.seen_children)}")
        check_tree_membership(self.data, self.expected_data, "data")
        expected_results = {f"{key}.txt" for key in self.seen_children}
        check_tree_membership(self.results, expected_results, "results")
        return {
            "result": "PASS within numerical consistency scope",
            "cover": {"centers": center_count, "checked_pairs": int(cover[1])},
            "coarse_records": [records.count for records in coarse],
            "mid_records": mid.count,
            "fine_records": fine.count,
            "batches": batch_count,
            "initial_C": initial,
            "fallback_inputs": fallback_inputs,
            "fallback_records": fallback_count,
            "final_C": final,
            "children": len(self.seen_children),
            "data_files": len(self.expected_data),
            "result_files": len(expected_results),
            "scope": "Derived numerical consistency check only; no source, binary, or original execution provenance verification."
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("execution_directory", type=Path, nargs="?",
                        default=Path(__file__).resolve().parent,
                        help="directory containing data/, results/, and commands.json")
    args = parser.parse_args()
    try:
        result = NumericalCheck(args.execution_directory).execute()
    except (OSError, ValueError, KeyError, TypeError, struct.error) as error:
        print(json.dumps({"result": "NOT ESTABLISHED", "error": str(error)}, indent=2))
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
