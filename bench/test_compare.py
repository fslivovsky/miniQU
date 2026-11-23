#!/usr/bin/env python3
"""Tests of the paired statistics of compare.py on synthetic results (run by ctest)."""
import csv
import json
import os
import random
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import paired  # noqa: E402

COLUMNS = ["instance", "family", "result", "exit", "wall", "cpu", "rss_mb",
           "proof_status", "proof_check_sec", "proof_bytes", "proof_trim_bytes"]
TIMEOUT = 600
INSTANCES = ["fam%d-%03d.qcir" % (i % 4, i) for i in range(60)]


def base_times():
    """Solve times of 60 instances between 10 s and 300 s, 10 of them unsolved."""
    rng = random.Random(7)
    return {n: (None if i % 6 == 5 else rng.uniform(10, 300)) for i, n in enumerate(INSTANCES)}


def write_run(results, tag, seed, times, factor=1.0, timeout=TIMEOUT, verdicts=None, proofs=None,
              noise_seed=0, conflicts=None, cpus=None, date=None):
    """A run with the times scaled by factor and a little noise (the same for every arm).
    conflicts and cpus map instances to a conflict counter (stats.csv) and a CPU time."""
    rng = random.Random(1000 * seed + noise_seed)
    d = os.path.join(results, tag)
    os.makedirs(d)
    with open(os.path.join(d, "results.csv"), "w", newline="") as f:
        w = csv.DictWriter(f, COLUMNS)
        w.writeheader()
        for name, t in times.items():
            noise = rng.uniform(0.97, 1.03)
            solved = t is not None
            row = dict.fromkeys(COLUMNS, "")
            row.update(instance=name, family=name.split("-")[0], rss_mb="100",
                       result=(verdicts or {}).get(name, "UNSAT") if solved else "TIMEOUT",
                       exit=20 if solved else -9, wall="%.3f" % (t * factor * noise if solved else timeout),
                       cpu=str((cpus or {}).get(name, 1)), proof_status=(proofs or {}).get(name, ""))
            w.writerow(row)
    if conflicts:
        with open(os.path.join(d, "stats.csv"), "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["instance", "counter", "value"])
            w.writerows([name, "conflicts", c] for name, c in conflicts.items())
    with open(os.path.join(d, "meta.json"), "w") as f:
        json.dump({"date": date or "2026-01-01T00:00:00", "jobs": 48, "mem_gb": 16, "cores": "64-127", "timeout": timeout, "seed": seed,
                   "instances_sha256": "x", "args": "", "proof_check": bool(proofs)}, f)


def compare(results, a, b, *extra):
    cmd = [sys.executable, os.path.join(HERE, "compare.py"), "--results-dir", results, "--paired"]
    cmd += a + list(extra) + ["--"] + b
    return subprocess.run(cmd, capture_output=True, text=True)


class PairedTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.results = self.dir.name
        self.times = base_times()

    def tearDown(self):
        self.dir.cleanup()

    def arms(self, factor_b=1.0, **kwargs_b):
        for seed in (1, 2, 3):
            write_run(self.results, "a-s%d" % seed, seed, self.times)
            write_run(self.results, "b-s%d" % seed, seed, self.times, factor_b, **kwargs_b)
        return ["a-s1", "a-s2", "a-s3"], ["b-s1", "b-s2", "b-s3"]

    def test_identical_arms(self):
        r = compare(self.results, *self.arms())
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("no measurable difference", r.stdout)
        self.assertIn("B is not worse than A: **yes**", r.stdout)
        self.assertNotIn("NOT COMPARABLE", r.stdout)

    def test_faster_arm_is_better(self):
        r = compare(self.results, *self.arms(factor_b=0.8))
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("Verdict: B is better than A", r.stdout)
        self.assertIn("B is not worse than A: **yes**", r.stdout)

    def test_slower_arm_is_worse(self):
        r = compare(self.results, *self.arms(factor_b=1.25))
        self.assertIn("Verdict: B is worse than A", r.stdout)
        self.assertIn("B is not worse than A: **no**", r.stdout)

    def test_mismatched_limits_refused(self):
        a, b = self.arms(timeout=300)
        r = compare(self.results, a, b)
        self.assertEqual(r.returncode, 3)
        self.assertIn("timeout differs", r.stderr)
        self.assertEqual(r.stdout, "")
        forced = compare(self.results, a, b, "--force")
        self.assertTrue(forced.stdout.startswith("# NOT COMPARABLE"), forced.stdout[:80])

    def test_mismatched_seeds_refused(self):
        a, b = self.arms()
        r = compare(self.results, a, b[:2])
        self.assertEqual(r.returncode, 3)
        self.assertIn("seed lists differ", r.stderr)

    def test_discrepancy_listed_first(self):
        a, b = self.arms()
        flipped = INSTANCES[0]
        for seed in (1, 2, 3):  # replace one run of B by a run that disagrees on one instance
            os.system("rm -r %s" % os.path.join(self.results, "b-s%d" % seed))
            write_run(self.results, "b-s%d" % seed, seed, self.times, verdicts={flipped: "SAT"})
        r = compare(self.results, a, b)
        self.assertEqual(r.returncode, 2)
        body = r.stdout
        self.assertLess(body.index("BLOCKING PROBLEMS"), body.index("## Parameters"))
        self.assertIn("RESULT DISCREPANCY on `%s`" % flipped, body)

    def test_coverage_table_names_failures(self):
        proofs = {n: "ok" for n, t in self.times.items() if t is not None}
        proofs[INSTANCES[0]] = "check_timeout"
        proofs[INSTANCES[1]] = "too_large"
        proofs[INSTANCES[2]] = ""
        a, b = self.arms(proofs=proofs)
        r = compare(self.results, a, b)
        self.assertIn("## Proof coverage", r.stdout)
        self.assertIn("checker timeout (1): `%s`" % INSTANCES[0], r.stdout)
        self.assertIn("too large (1): `%s`" % INSTANCES[1], r.stdout)
        self.assertIn("not attempted", r.stdout)


class IdenticalSearchTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.results = self.dir.name
        solved = [n for n, t in base_times().items() if t is not None]
        self.times = {n: 10.0 for n in solved}
        self.conflicts = {n: 100 for n in solved}
        self.cpu_a = dict.fromkeys(solved, 2.0)
        self.cpu_b = dict.fromkeys(solved, 3.0)

    def tearDown(self):
        self.dir.cleanup()

    def report(self, conflicts_b=None, cpu_a=None, cpu_b=None, with_stats=True):
        for seed in (1, 2):
            write_run(self.results, "a-s%d" % seed, seed, self.times, cpus=cpu_a or self.cpu_a,
                      conflicts=self.conflicts if with_stats else None, date="2026-01-0%dT10:00:00" % seed)
            write_run(self.results, "b-s%d" % seed, seed, self.times, cpus=cpu_b or self.cpu_b,
                      conflicts=(conflicts_b or self.conflicts) if with_stats else None,
                      date="2026-01-0%dT09:00:00" % seed)
        r = compare(self.results, ["a-s1", "a-s2"], ["b-s1", "b-s2"])
        self.assertEqual(r.returncode, 0, r.stderr)
        return r.stdout

    def test_geometric_mean_and_counts(self):
        out = self.report()
        section = out[out.index("## Identical searches"):]
        self.assertIn("| 1 | 50 | 1.500 | 50 | 0 |", section)
        self.assertIn("| all (per instance) | 50 | 1.500 | 50 | 0 |", section)
        self.assertLess(out.index("## Result"), out.index("## Identical searches"))

    def test_excluded_instances(self):
        different = dict(self.conflicts)
        different[INSTANCES[0]] = 101
        cpu_a = dict(self.cpu_a)
        cpu_a[INSTANCES[1]] = 0.5
        out = self.report(conflicts_b=different, cpu_a=cpu_a)
        self.assertIn("| 1 | 48 | 1.500 | 48 | 0 |", out)
        self.assertNotIn("| %s | 1.500" % INSTANCES[0], out)

    def test_family_mark(self):
        fam1 = [n for n in self.cpu_a if n.startswith("fam1-")]
        cpu_a = dict(self.cpu_a)
        cpu_b = dict(self.cpu_b)
        for n in fam1[3:]:
            cpu_a[n] = 0.5  # below the CPU limit: not an identical search
        for n in fam1[:3]:
            cpu_b[n] = 2.4  # ratio 1.2
        out = self.report(cpu_a=cpu_a, cpu_b=cpu_b)
        self.assertIn("| fam1 | 3 | 1.200 | > 1.10 |", out)
        self.assertNotIn("| fam1 | 2 |", out)

    def test_order_of_runs(self):
        out = self.report()
        lines = out[out.index("Order in which the runs started:"):].splitlines()[2:6]
        self.assertEqual(lines, ["- 2026-01-01T09:00:00 `b-s1`", "- 2026-01-01T10:00:00 `a-s1`",
                                 "- 2026-01-02T09:00:00 `b-s2`", "- 2026-01-02T10:00:00 `a-s2`"])

    def test_no_stats(self):
        self.assertIn("no instance with equal conflict counts", self.report(with_stats=False))


class StatisticsTest(unittest.TestCase):
    def test_binomial(self):
        self.assertEqual(paired.binomial_two_sided(0, 0), 1.0)
        self.assertAlmostEqual(paired.binomial_two_sided(0, 10), 2 / 1024)
        self.assertAlmostEqual(paired.binomial_two_sided(5, 10), 1.0)
        self.assertAlmostEqual(paired.binomial_two_sided(8, 10), paired.binomial_two_sided(2, 10))

    def test_bootstrap_is_deterministic_and_brackets_the_mean(self):
        rng = random.Random(3)
        values = [rng.uniform(-5, 5) + 1 for _ in range(80)]
        low, high = paired.bootstrap_interval(values)
        self.assertEqual((low, high), paired.bootstrap_interval(values))
        self.assertLess(low, sum(values) / len(values))
        self.assertGreater(high, sum(values) / len(values))


if __name__ == "__main__":
    unittest.main()
