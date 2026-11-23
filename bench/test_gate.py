#!/usr/bin/env python3
"""Tests of gate.py on synthetic result directories (run by ctest)."""
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from test_compare import write_run  # noqa: E402

SEEDS = (1, 2, 3)
# Per family, instance names and (CPU time of A, conflicts) for a search both arms run identically.
FAMILIES = {"fa": 4, "fb": 3, "fc": 2, "fd": 4}


def instances():
    return ["%s-%03d.qcir" % (f, k) for f, n in FAMILIES.items() for k in range(n)]


class GateTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.results = self.dir.name

    def tearDown(self):
        self.dir.cleanup()

    def arms(self, tag, factor=None, verdicts_b=None, times_b=None):
        """Runs tag-a-s<n> and tag-b-s<n>: B's CPU time is A's times factor[family]."""
        factor = factor or {}
        times = {n: 10.0 for n in instances()}
        conflicts = {n: 1000 for n in instances()}
        for seed in SEEDS:
            cpu_a = {n: 5.0 for n in times}
            cpu_b = {n: 5.0 * factor.get(n.split("-")[0], 1.0) for n in times}
            write_run(self.results, "%s-a-s%d" % (tag, seed), seed, times, conflicts=conflicts, cpus=cpu_a)
            write_run(self.results, "%s-b-s%d" % (tag, seed), seed, times_b or times, conflicts=conflicts,
                      cpus=cpu_b, verdicts=verdicts_b)
        return ["%s-%s-s%d" % (tag, arm, s) for arm in "ab" for s in SEEDS]

    def gate(self, *configs, extra=()):
        cmd = [sys.executable, os.path.join(HERE, "gate.py"), "--results-dir", self.results]
        for kind, name, tag in configs:
            cmd += ["--" + kind, "%s:%s:%s" % (name, ",".join("%s-a-s%d" % (tag, s) for s in SEEDS),
                                               ",".join("%s-b-s%d" % (tag, s) for s in SEEDS))]
        return subprocess.run(cmd + list(extra), capture_output=True, text=True)

    def test_passing_set(self):
        self.arms("x", {"fa": 1.02})
        r = self.gate(("pair", "x", "x"))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("limit 1.04: PASS", r.stdout)
        self.assertIn("GATE: PASS", r.stdout)
        for fam in FAMILIES:  # the family table is complete
            self.assertIn("| %s |" % fam, r.stdout)
        self.assertIn("memory-limit hits (MEMOUT): none", r.stdout)

    def test_family_of_three_above_limit_fails(self):
        self.arms("x", {"fb": 1.12})
        r = self.gate(("pair", "x", "x"))
        self.assertEqual(r.returncode, 1)
        self.assertIn("| fb | 3 | 1.120 | FAIL |", r.stdout)
        self.assertIn("GATE: FAIL (1 lines)", r.stdout)

    def test_family_of_two_is_not_gated(self):
        self.arms("x", {"fc": 1.2})
        r = self.gate(("pair", "x", "x"))
        self.assertEqual(r.returncode, 0, r.stdout)
        self.assertIn("| fc | 2 | 1.200 | n < 3 |", r.stdout)

    def test_pooled_above_limit_fails(self):
        self.arms("x", {f: 1.08 for f in FAMILIES} | {"fa": 1.09})
        r = self.gate(("pair", "x", "x"), extra=["--family-limit", "2"])
        self.assertEqual(r.returncode, 1)
        self.assertIn("limit 1.04: FAIL", r.stdout)
        self.assertNotIn("| FAIL |", r.stdout.split("## Summary")[0].split("Per family")[1])

    def test_report_configuration_does_not_fail(self):
        self.arms("x")
        self.arms("m", {"fa": 1.3})
        r = self.gate(("pair", "x", "x"), ("report", "m", "m"))
        self.assertEqual(r.returncode, 0, r.stdout)
        self.assertIn("REPORT (above, to be explained)", r.stdout)
        self.assertIn("GATE: PASS", r.stdout)

    def test_memout_listed(self):
        self.arms("x")
        victim = instances()[0]
        # B's runs hit the memory limit on one instance, A's do not
        times = {n: (10.0 if n != victim else None) for n in instances()}
        self.arms("y", times_b=times)
        for s in SEEDS:  # rewrite the TIMEOUT row of B as the harness writes a memory-limit hit
            path = os.path.join(self.results, "y-b-s%d" % s, "results.csv")
            with open(path) as f:
                text = f.read().replace("TIMEOUT", "MEMOUT")
            with open(path, "w") as f:
                f.write(text)
        r = self.gate(("pair", "y", "y"))
        self.assertIn("`%s` (A 0/3 runs, B 3/3 runs)" % victim, r.stdout)

    def test_failure_that_does_not_repeat_is_noise(self):
        self.arms("x", {"fb": 1.12})
        self.arms("c")
        r = self.gate(("pair", "n", "x"), ("confirm", "n", "c"))
        self.assertEqual(r.returncode, 0, r.stdout)
        self.assertIn("| fb | 3 | 1.120 | NOISE (first 1.120, repeat 1.000) |", r.stdout)
        self.assertIn("GATE: PASS", r.stdout)
        self.assertNotIn("Hint:", r.stdout)

    def test_failure_that_repeats_fails(self):
        self.arms("x", {"fb": 1.12})
        self.arms("c", {"fb": 1.15})
        r = self.gate(("pair", "n", "x"), ("confirm", "n", "c"))
        self.assertEqual(r.returncode, 1)
        self.assertIn("| fb | 3 | 1.120 | FAIL (repeated) |", r.stdout)
        self.assertIn("GATE: FAIL (1 lines)", r.stdout)

    def test_confirm_does_not_excuse_the_pooled_line(self):
        self.arms("x", {f: 1.08 for f in FAMILIES} | {"fa": 1.09})
        self.arms("c")
        r = self.gate(("pair", "n", "x"), ("confirm", "n", "c"), extra=["--family-limit", "2"])
        self.assertEqual(r.returncode, 1)
        self.assertIn("limit 1.04: FAIL", r.stdout)

    def test_without_confirm_failure_stands_with_hint(self):
        self.arms("x", {"fb": 1.12})
        r = self.gate(("pair", "n", "x"))
        self.assertEqual(r.returncode, 1)
        self.assertIn("| fb | 3 | 1.120 | FAIL |", r.stdout)
        self.assertTrue(r.stdout.rstrip().splitlines()[-1].startswith("Hint: rerun the configuration back to back "
                                                                      "and pass --confirm"), r.stdout)

    def test_confirm_needs_a_pair_of_that_name(self):
        self.arms("x")
        r = self.gate(("pair", "n", "x"), ("confirm", "other", "x"))
        self.assertEqual(r.returncode, 2)
        self.assertIn("no --pair of that name", r.stderr)

    def test_self_table_is_information(self):
        self.arms("x")
        self.arms("s", {"fa": 1.3})
        r = self.gate(("pair", "x", "x"), ("self", "twice", "s"))
        self.assertEqual(r.returncode, 0, r.stdout)
        self.assertIn("twice (same binary twice, information only)", r.stdout)
        self.assertIn("| fa | 4 | 1.300 |", r.stdout.split("same binary twice")[1])

    def test_incomparable_refused(self):
        self.arms("x")
        os.system("rm -r %s" % os.path.join(self.results, "x-b-s3"))
        write_run(self.results, "x-b-s3", 3, {n: 10.0 for n in instances()}, timeout=300,
                  conflicts={n: 1000 for n in instances()})
        r = self.gate(("pair", "x", "x"))
        self.assertEqual(r.returncode, 3)
        self.assertIn("timeout differs", r.stderr)


if __name__ == "__main__":
    unittest.main()
