#!/usr/bin/env python3
"""Merge the per-instance results of a job array into one run that compare.py and gate.py read.

    python3 bench/cluster/merge.py [--results-dir DIR] [--list instances.txt] [--allow-missing] TAG [TAG ...]

bench/cluster/array.sbatch runs bench/run.py once per instance and writes
DIR/TAG.parts/<index>/{results.csv,stats.csv,meta.json}.  This script writes DIR/TAG/ with the
three files of an ordinary run:

* results.csv and stats.csv are the rows of all parts, sorted by instance;
* meta.json is that of the first part with `jobs` 1, `cores` "array", the number of instances
  and the hash of the instance list as run.py computes it, the hosts of all parts and the
  earliest date.

It refuses (exit 1) when the parts disagree in a parameter that defines the run (solver hash,
arguments, seed, timeout, memory limit, proof limits), when an instance occurs twice, or when an
instance of --list has no row (--allow-missing writes the run anyway; compare.py then compares
only the instances present in every run, and compare.py --paired refuses two run sets whose
instance lists differ).
"""
import argparse
import csv
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_RESULTS = os.path.join(os.path.dirname(HERE), "results")
SAME = ("solver_sha256", "args", "seed_args", "seed", "proof_args", "timeout", "mem_gb", "proof_check",
        "proof_max_solve_sec", "proof_timeout", "proof_mem_gb", "proof_max_gb")


def read_csv(path):
    try:
        with open(path, newline="") as f:
            reader = csv.DictReader(f)
            return reader.fieldnames, list(reader)
    except OSError:
        return None, []


def merge(results_dir, tag, wanted, allow_missing):
    parts_dir = os.path.join(results_dir, tag + ".parts")
    try:
        parts = sorted(os.listdir(parts_dir))
    except OSError:
        sys.exit("merge.py: no directory %s" % parts_dir)
    meta, hosts, dates, header, stats_header = None, set(), [], None, None
    rows, stats = {}, []
    for part in parts:
        d = os.path.join(parts_dir, part)
        try:
            with open(os.path.join(d, "meta.json")) as f:
                m = json.load(f)
        except OSError:
            print("merge.py: %s: part %s has no meta.json (job did not start?)" % (tag, part), file=sys.stderr)
            continue
        if meta is None:
            meta = m
        for key in SAME:
            if m.get(key) != meta.get(key):
                sys.exit("merge.py: %s: part %s differs in %s: %r, first part has %r" %
                         (tag, part, key, m.get(key), meta.get(key)))
        hosts.add(m.get("host"))
        dates.append(m.get("date"))
        fields, part_rows = read_csv(os.path.join(d, "results.csv"))
        header = header or fields
        for r in part_rows:
            if r["instance"] in rows:
                sys.exit("merge.py: %s: instance %s occurs in two parts" % (tag, r["instance"]))
            rows[r["instance"]] = r
        fields, part_stats = read_csv(os.path.join(d, "stats.csv"))
        stats_header = stats_header or fields
        stats += part_stats
    if meta is None or not rows:
        sys.exit("merge.py: %s: no finished part in %s" % (tag, parts_dir))
    missing = sorted(set(wanted) - set(rows)) if wanted else []
    extra = sorted(set(rows) - set(wanted)) if wanted else []
    if extra:
        sys.exit("merge.py: %s: instances not in the list: %s" % (tag, ", ".join(extra[:10])))
    if missing:
        print("merge.py: %s: %d instances without a row: %s%s" %
              (tag, len(missing), ", ".join(missing[:10]), " ..." if len(missing) > 10 else ""), file=sys.stderr)
        if not allow_missing:
            sys.exit(1)
    names = sorted(rows)
    meta.update({"jobs": 1, "cores": "array", "instances": len(names),
                 "instances_sha256": hashlib.sha256("\n".join(names).encode()).hexdigest(),
                 "host": ",".join(sorted(h for h in hosts if h)), "date": min(d for d in dates if d),
                 "merged_parts": len(parts), "cmdline": "merge.py of " + meta.get("cmdline", "")})
    out = os.path.join(results_dir, tag)
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "results.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=header, lineterminator="\n")
        w.writeheader()
        w.writerows(rows[n] for n in names)
    if stats_header:
        with open(os.path.join(out, "stats.csv"), "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=stats_header, lineterminator="\n")
            w.writeheader()
            w.writerows(sorted(stats, key=lambda r: (r["instance"], r["counter"])))
    with open(os.path.join(out, "meta.json"), "w") as f:
        json.dump(meta, f, indent=2)
    print("%s: %d instances from %d parts, %d hosts -> %s" % (tag, len(names), len(parts), len(hosts), out))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("tags", nargs="+")
    ap.add_argument("--results-dir", default=DEFAULT_RESULTS)
    ap.add_argument("--list", help="file with one instance name per line (the list of the array)")
    ap.add_argument("--allow-missing", action="store_true")
    args = ap.parse_args()
    wanted = []
    if args.list:
        with open(args.list) as f:
            wanted = [os.path.basename(line.strip()) for line in f if line.strip() and not line.startswith("#")]
    for tag in args.tags:
        merge(args.results_dir, tag, wanted, args.allow_missing)


if __name__ == "__main__":
    main()
