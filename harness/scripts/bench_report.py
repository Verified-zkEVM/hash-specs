#!/usr/bin/env python3
"""Summarise criterion results into BENCHMARKS.md.

Reads target/criterion/<hash>/<implementation>/<size>/new/estimates.json, as written by
`cargo bench --bench throughput`, and writes a Markdown table of throughput per hash, message size
and implementation, with each implementation's speed relative to the Lean fast specification.

This is a record of relative efficiency only; nothing is checked against it.
"""

import datetime
import json
import pathlib
import platform
import subprocess
import sys

HARNESS = pathlib.Path(__file__).resolve().parent.parent
CRITERION = HARNESS / "target" / "criterion"
OUT = HARNESS / "BENCHMARKS.md"


def human_size(n: int) -> str:
    for unit, scale in (("MiB", 1 << 20), ("KiB", 1 << 10)):
        if n >= scale and n % scale == 0:
            return f"{n // scale} {unit}"
    return f"{n} B"


def human_rate(bytes_per_s: float) -> str:
    for unit, scale in (("GiB/s", 1 << 30), ("MiB/s", 1 << 20), ("KiB/s", 1 << 10)):
        if bytes_per_s >= scale:
            return f"{bytes_per_s / scale:.1f} {unit}"
    return f"{bytes_per_s:.0f} B/s"


def cpu_name() -> str:
    try:
        if sys.platform == "darwin":
            return subprocess.check_output(["sysctl", "-n", "machdep.cpu.brand_string"], text=True).strip()
        for line in pathlib.Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                return line.split(":", 1)[1].strip()
    except Exception:
        pass
    return platform.processor() or "unknown"


def main() -> None:
    if not CRITERION.is_dir():
        sys.exit("no criterion results; run `cargo bench --bench throughput` first")
    results: dict[str, dict[int, dict[str, float]]] = {}
    for est in CRITERION.glob("*/*/*/new/estimates.json"):
        size_dir = est.parent.parent
        impl_dir = size_dir.parent
        group_dir = impl_dir.parent
        try:
            size = int(size_dir.name)
        except ValueError:
            continue
        group = json.loads((group_dir / impl_dir.name / size_dir.name / "new" / "benchmark.json").read_text())["group_id"]
        mean_ns = json.loads(est.read_text())["mean"]["point_estimate"]
        results.setdefault(group, {}).setdefault(size, {})[impl_dir.name] = size / (mean_ns * 1e-9)

    lines = [
        "# Benchmarks",
        "",
        "Throughput of the Lean fast specifications next to the implementations they are",
        "differentially tested against. **This is a record of relative efficiency, not a",
        "requirement.** The Lean code is a specification: it is written to be proved equal to the",
        "reference specification, not to compete with optimised libraries.",
        "",
        f"- Recorded: {datetime.date.today().isoformat()}",
        f"- Machine: {cpu_name()}, {platform.system()} {platform.machine()}",
        "- Command: `cargo bench --bench throughput` in `harness/hash-lean`, then",
        "  `python3 harness/scripts/bench_report.py`",
        "- Lean is called in-process through the C exports in `HashFFI/Export.lean`, so the",
        "  numbers include copying the message into a Lean `ByteArray`.",
        "- \"× Lean\" is how many times faster than the Lean fast specification each",
        "  implementation is.",
        "",
    ]
    for group in sorted(results):
        impls = sorted({i for per_size in results[group].values() for i in per_size}, key=lambda i: (i != "lean", i))
        lines += [f"## {group}", "", "| Message | " + " | ".join(impls) + " |",
                  "|---|" + "---|" * len(impls)]
        for size in sorted(results[group]):
            row = results[group][size]
            cells = []
            for i in impls:
                if i not in row:
                    cells.append("–")
                elif i == "lean" or "lean" not in row:
                    cells.append(human_rate(row[i]))
                else:
                    cells.append(f"{human_rate(row[i])} ({row[i] / row['lean']:.1f}× Lean)")
            lines.append(f"| {human_size(size)} | " + " | ".join(cells) + " |")
        lines.append("")
    OUT.write_text("\n".join(lines))
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
