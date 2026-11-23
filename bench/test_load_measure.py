"""Test of load_measure.py with fake solvers and a fake sysfs tree (run by ctest): the script's
own bookkeeping, not any solver's speed."""
import csv
import json
import os
import subprocess
import sys
import tempfile
import unittest

import load_measure

HERE = os.path.dirname(os.path.abspath(__file__))
INSTANCES = ["a-fast.qcir", "b-slow.qcir", "c-fast.qcir", "d-fast.qcir"]


def fake_solver(path, conflicts):
    """A shell script that prints a conflict count, burns CPU time (0.6 s for an instance with
    "slow" in its name, else 0.05 s) and says SAT."""
    with open(path, "w") as f:
        f.write("#!/bin/sh\nfor last; do :; done\necho 'c stat conflicts %d'\n"
                "case $last in *slow*) t=0.6;; *) t=0.05;; esac\n"
                "python3 -c \"import sys, time; t = time.process_time()\n"
                "while time.process_time() - t < float(sys.argv[1]): pass\" $t\n"
                "exit 10\n" % conflicts)
    os.chmod(path, 0o755)


def fake_sysfs(root, l3_groups):
    """A sysfs tree whose cores share an L3 cache as given, e.g. [[0, 1], [2, 3]]."""
    for group in l3_groups:
        for core in group:
            d = os.path.join(root, "cpu%d" % core, "cache", "index3")
            os.makedirs(d)
            with open(os.path.join(d, "shared_cpu_list"), "w") as f:
                f.write("%d-%d\n" % (group[0], group[-1]))


class IsBusyTest(unittest.TestCase):
    def test_processes_that_disturb(self):
        for argv in (["/x/build/release/miniQU", "a.qcir"],
                     ["/home/u/miniqu-work/baseline/miniQU", "-rnd-init", "a.qcir"],
                     ["python3", "bench/run.py", "--tag", "t"],
                     ["python3", "-u", "/r/bench/load_measure.py"]):
            self.assertTrue(load_measure.is_busy(argv), argv)

    def test_words_in_arguments_do_not_count(self):
        for argv in (["bash", "-c", "nohup python3 bench/load_measure.py --a /x/miniQU"],
                     ["SCREEN", "-S", "miniQU"], ["tail", "-f", "/x/miniQU.log"],
                     ["python3", "tests/regress.py"], ["vim", "bench/run.py"], []):
            self.assertFalse(load_measure.is_busy(argv), argv)


class GroupsTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.path = lambda *p: os.path.join(self.dir.name, *p)
        os.makedirs(self.path("bench"))
        for name in INSTANCES:
            open(self.path("bench", name), "w").close()

    def tearDown(self):
        self.dir.cleanup()

    def groups(self, text):
        with open(self.path("list.txt"), "w") as f:
            f.write(text)
        return load_measure.read_groups(self.path("list.txt"), self.path("bench"))

    def test_blocks_and_comments(self):
        groups = self.groups("# header\n\n# first\n# group\na-fast.qcir\nb-slow.qcir\n\n"
                             "# second\nc-fast.qcir\n")
        self.assertEqual(groups, [{"comment": "first group", "instances": ["a-fast.qcir", "b-slow.qcir"]},
                                  {"comment": "second", "instances": ["c-fast.qcir"]}])

    def test_refusals(self):
        with self.assertRaisesRegex(ValueError, "not found"):
            self.groups("missing.qcir\n")
        with self.assertRaisesRegex(ValueError, "consecutive"):
            self.groups("a-fast.qcir\nc-fast.qcir\n")
        with open(self.path("list.txt"), "w") as f:
            f.write("a-fast.qcir\n" * 9)
        with self.assertRaisesRegex(ValueError, "has 9 instances"):
            load_measure.read_groups(self.path("list.txt"), self.path("bench"))

    def test_shipped_file_matches_the_benchmark_placement(self):
        # structure only: at most 6 groups of at most 8 names, each starting a distinct window
        with open(os.path.join(HERE, "load-instances.txt")) as f:
            blocks = [b for b in f.read().split("\n\n") if b.strip() and not b.startswith("# Groups")]
        names = [[l for l in b.splitlines() if not l.startswith("#")] for b in blocks]
        self.assertEqual(len(names), 6)
        self.assertTrue(all(0 < len(n) <= 8 for n in names))
        self.assertEqual(names[0][0], "CM-unsat-07-01-06-2.qcir")
        self.assertEqual(names[0][-1], "DW-unsat-11-26-1.qcir")
        self.assertEqual(len({n for g in names for n in g}), sum(map(len, names)))

    def test_l3_groups(self):
        sysfs = self.path("sys")
        fake_sysfs(sysfs, [[0, 1], [2, 3], [4, 5]])
        self.assertEqual(load_measure.l3_groups([0, 1, 2, 3], sysfs), [[0, 1], [2, 3]])
        with self.assertRaisesRegex(ValueError, "whole L3 groups"):
            load_measure.l3_groups([0, 1, 2], sysfs)
        with self.assertRaisesRegex(ValueError, "cannot read"):
            load_measure.l3_groups([6], sysfs)

    def test_place(self):
        groups = [{"comment": "", "instances": ["x"]}, {"comment": "", "instances": ["y", "z"]}]
        placed, idle = load_measure.place(groups, [[0, 1], [2, 3], [4, 5]])
        self.assertEqual([g["l3_cores"] for g in placed], [[0, 1], [2, 3]])
        self.assertEqual(idle, [[4, 5]])
        with self.assertRaisesRegex(ValueError, "only 1 L3 groups"):
            load_measure.place(groups, [[0, 1]])
        with self.assertRaisesRegex(ValueError, "only 1 cores"):
            load_measure.place(groups, [[0, 1], [2]])

    def test_group_means(self):
        groups = [{"comment": "", "instances": ["x", "y"]}, {"comment": "", "instances": ["z"]}]
        summary = [("x", [1.0], [2.0], "identical"), ("y", [1.0], [8.0], "identical"),
                   ("z", [1.0], [3.0], "different search")]
        means = load_measure.group_means(groups, summary)
        self.assertAlmostEqual(load_measure.geomean(means[0][1]), 4.0)
        self.assertEqual(means[1][1], [])


class LoadMeasureTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.path = lambda *p: os.path.join(self.dir.name, *p)
        os.makedirs(self.path("bench"))
        for name in INSTANCES:
            open(self.path("bench", name), "w").close()
        with open(self.path("list.txt"), "w") as f:
            f.write("# fast next to slow\na-fast.qcir\nb-slow.qcir\n\n# alone\nc-fast.qcir\n")
        fake_sysfs(self.path("sys"), [[0, 1], [2, 3]])

    def tearDown(self):
        self.dir.cleanup()

    def command(self, extra=()):
        return [sys.executable, os.path.join(HERE, "load_measure.py"), "--a", self.path("a.sh"),
                "--b", self.path("b.sh"), "--tag", "t", "--instances", self.path("list.txt"),
                "--bench-dir", self.path("bench"), "--rounds", "2", "--cores", "0-3", "--force",
                "--sysfs-root", self.path("sys"), "--results-dir", self.path("results"), *extra]

    def measure(self, conflicts_b):
        fake_solver(self.path("a.sh"), 7)
        fake_solver(self.path("b.sh"), conflicts_b)
        r = subprocess.run(self.command(), capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stderr)
        return self.path("results", "t")

    def test_placement_and_keep_busy(self):
        out = self.measure(7)
        with open(os.path.join(out, "load.csv"), newline="") as f:
            rows = list(csv.DictReader(f))
        core_of = {"a-fast.qcir": 0, "b-slow.qcir": 1, "c-fast.qcir": 2}  # core 3 stays idle
        for r in rows:
            self.assertEqual(int(r["core"]), core_of[r["instance"]])
            self.assertEqual((r["result"], r["conflicts"]), ("SAT", "7"))
            self.assertGreater(float(r["user"]) + float(r["sys"]), 0.03)
        for arm in "AB":
            for rnd in "12":
                mine = [r for r in rows if r["arm"] == arm and r["round"] == rnd]
                count = lambda name: sorted(int(r["copy"]) for r in mine if r["instance"] == name)
                self.assertEqual(count("b-slow.qcir"), [0])  # the round ends with its first run
                # the fast instance on the neighbouring core kept running meanwhile
                self.assertGreaterEqual(len(count("a-fast.qcir")), 3)
                self.assertEqual(count("a-fast.qcir"), list(range(len(count("a-fast.qcir")))))
                self.assertGreaterEqual(len(count("c-fast.qcir")), 1)
        with open(os.path.join(out, "meta.json")) as f:
            meta = json.load(f)
        self.assertEqual([o["arm"] for o in meta["order"]], ["A", "B", "A", "B"])
        self.assertEqual(meta["idle_l3_groups"], [])
        with open(os.path.join(out, "load.md")) as f:
            text = f.read()
        self.assertIn("L3 groups, cores kept busy", text)
        self.assertIn("group 1 on cores 2,3: 1 instances, cores 3 idle", text)
        self.assertIn("geometric mean** (n=3 identical searches)", text)
        self.assertIn("| 0 | a-fast.qcir | fast next to slow | 2 |", text)
        self.assertNotIn("different search", text)

    def test_different_conflicts_are_marked(self):
        with open(os.path.join(self.measure(8), "load.md")) as f:
            text = f.read()
        self.assertIn("different search", text)
        self.assertIn("(n=0 identical searches)", text)

    def test_refusals(self):
        fake_solver(self.path("a.sh"), 7)
        fake_solver(self.path("b.sh"), 7)
        for option, message in (("--cores=0-2", "whole L3 groups"), ("--cores=0-1", "only 1 L3 groups")):
            r = subprocess.run(self.command([option]), capture_output=True, text=True)
            self.assertEqual(r.returncode, 1)
            self.assertIn(message, r.stderr)


if __name__ == "__main__":
    unittest.main()
