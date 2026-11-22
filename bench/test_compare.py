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
              noise_seed=0):
    """A run with the times scaled by factor and a little noise (the same for every arm)."""
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
                       cpu="1", proof_status=(proofs or {}).get(name, ""))
            w.writerow(row)
    with open(os.path.join(d, "meta.json"), "w") as f:
        json.dump({"jobs": 48, "mem_gb": 16, "cores": "64-127", "timeout": timeout, "seed": seed,
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
