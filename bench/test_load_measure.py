#!/usr/bin/env python3
"""Test of load_measure.py with fake solvers (run by ctest): the script's own bookkeeping,
not any solver's speed."""
import csv
import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
CORES = [0, 1, 2, 3]


def fake_solver(path, conflicts):
    """A shell script that prints a conflict count, burns about 0.1 s of CPU time and says SAT."""
    with open(path, "w") as f:
        f.write("#!/bin/sh\necho 'c stat conflicts %d'\n"
                "python3 -c 'import time; t = time.process_time()\nwhile time.process_time() - t < 0.1: pass'\n"
                "exit 10\n" % conflicts)
    os.chmod(path, 0o755)


class LoadMeasureTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.path = lambda name: os.path.join(self.dir.name, name)
        for name in ("one.qcir", "two.qcir"):
            open(self.path(name), "w").close()
        with open(self.path("list.txt"), "w") as f:
            f.write("one.qcir\ntwo.qcir\n")

    def tearDown(self):
        self.dir.cleanup()

    def measure(self, conflicts_b):
        fake_solver(self.path("a.sh"), 7)
        fake_solver(self.path("b.sh"), conflicts_b)
        cmd = [sys.executable, os.path.join(HERE, "load_measure.py"), "--a", self.path("a.sh"),
               "--b", self.path("b.sh"), "--tag", "t", "--instances", self.path("list.txt"),
               "--bench-dir", self.dir.name, "--copies", "2", "--rounds", "2", "--cores", "0-3",
               "--force", "--results-dir", self.path("results")]
        r = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        return os.path.join(self.path("results"), "t")

    def test_identical_searches(self):
        out = self.measure(7)
        with open(os.path.join(out, "load.csv"), newline="") as f:
            rows = list(csv.DictReader(f))
        self.assertEqual(len(rows), 16)  # 2 arms x 2 rounds x 2 instances x 2 copies
        for r in rows:
            index = int(r["copy"]) * 2 + ["one.qcir", "two.qcir"].index(r["instance"])
            self.assertEqual(int(r["core"]), CORES[index])
            self.assertEqual((r["result"], r["conflicts"]), ("SAT", "7"))
            self.assertGreater(float(r["user"]) + float(r["sys"]), 0.05)
        with open(os.path.join(out, "meta.json")) as f:
            meta = json.load(f)
        self.assertEqual([o["arm"] for o in meta["order"]], ["A", "B", "A", "B"])
        with open(os.path.join(out, "load.md")) as f:
            text = f.read()
        self.assertIn("geometric mean** (n=2 identical searches)", text)
        self.assertNotIn("different search", text)

    def test_different_conflicts_are_marked(self):
        with open(os.path.join(self.measure(8), "load.md")) as f:
            text = f.read()
        self.assertIn("different search", text)
        self.assertIn("(n=0 identical searches)", text)


if __name__ == "__main__":
    unittest.main()
