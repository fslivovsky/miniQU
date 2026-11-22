"""Shared helpers of the benchmark scripts: reading the files run.py writes
(results.csv, stats.csv, meta.json) and the proof coverage table."""
import csv
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_RESULTS = os.path.join(HERE, "results")
SOLVED = ("SAT", "UNSAT")
# Proof statuses that are not an acceptance: a rejected proof is a bug, the others are coverage gaps.
REJECTED = ("rejected", "wrong_verdict")


class Run:
    """The files of one tag: rows by instance, counters by instance, metadata."""

    def __init__(self, results_dir, tag):
        self.tag = tag
        d = os.path.join(results_dir, tag)
        try:
            with open(os.path.join(d, "results.csv"), newline="") as f:
                self.rows = {r["instance"]: r for r in csv.DictReader(f)}
        except OSError:
            sys.exit("no results for tag %r in %s" % (tag, d))
        for r in self.rows.values():  # files of older runs lack some columns
            for c in ("proof_status", "proof_check_sec", "proof_bytes", "proof_trim_bytes"):
                r[c] = r.get(c) or ""
        self.stats = {}
        try:
            with open(os.path.join(d, "stats.csv"), newline="") as f:
                for r in csv.DictReader(f):
                    self.stats.setdefault(r["instance"], {})[r["counter"]] = int(r["value"])
        except OSError:
            pass
        try:
            with open(os.path.join(d, "meta.json")) as f:
                self.meta = json.load(f)
        except OSError:
            self.meta = {}

    def solved(self, instance):
        return self.rows[instance]["result"] in SOLVED

    def wall(self, instance):
        return float(self.rows[instance]["wall"])

    def timeout(self):
        t = self.meta.get("timeout")
        return float(t) if t else max([float(r["wall"]) for r in self.rows.values()] or [0.0])

    def par2(self, instance):
        return self.wall(instance) if self.solved(instance) else 2 * self.timeout()


def table(header, rows):
    out = ["| " + " | ".join(header) + " |",
           "|" + "|".join(["---"] + ["---:"] * (len(header) - 1)) + "|"]
    out += ["| " + " | ".join(str(c) for c in row) + " |" for row in rows]
    return out


def proof_category(run, instance):
    """Coverage category of a solved instance (see ROADMAP 0.3)."""
    status = run.rows[instance]["proof_status"]
    if status in ("", "n/a"):
        return "not attempted"
    if status in REJECTED:
        return "rejected"
    if status.startswith("solve_"):
        return "proof run unfinished"
    return {"ok": "accepted", "check_timeout": "checker timeout", "check_memout": "checker memout",
            "too_large": "too large", "check_error": "checker error"}[status]


COVERAGE_COLUMNS = ["accepted", "rejected", "checker timeout", "checker memout", "too large",
                    "checker error", "proof run unfinished", "not attempted"]


def coverage_table(runs, max_names=60):
    """Markdown proof coverage table of the runs (one row each) and, below it, every
    category except 'accepted' with the instances in it, by name."""
    rows, lists = [], []
    for run in runs:
        solved = [i for i in sorted(run.rows) if run.solved(i)]
        cats = {c: [i for i in solved if proof_category(run, i) == c] for c in COVERAGE_COLUMNS}
        attempted = sum(len(v) for c, v in cats.items() if c != "not attempted")
        trimmed = sum(1 for i in cats["accepted"] if run.rows[i]["proof_trim_bytes"])
        accepted = "%d (%d after trimming)" % (len(cats["accepted"]), trimmed) if trimmed \
            else str(len(cats["accepted"]))
        rows.append([run.tag, len(solved), attempted, accepted] + [len(cats[c]) for c in COVERAGE_COLUMNS[1:]])
        for c in COVERAGE_COLUMNS[1:]:
            if cats[c]:
                reason = ""
                if c == "not attempted":
                    limit = run.meta.get("proof_max_solve_sec")
                    reason = " (proofs not requested)" if not run.meta.get("proof_check") else \
                        " (solved in more than %s s)" % limit
                names = ", ".join("`%s`" % i for i in cats[c][:max_names])
                lists.append("- `%s`, %s%s (%d): %s%s" % (run.tag, c, reason, len(cats[c]), names,
                                                          " ..." if len(cats[c]) > max_names else ""))
    out = table(["run", "solved", "attempted", "accepted"] + COVERAGE_COLUMNS[1:], rows) + [""]
    return out + lists + ([""] if lists else [])
