#!/usr/bin/env python3
"""Test of l3_table.py (run by ctest): parsing and the table of a bench/l3.sh output."""
import math
import unittest

import l3_table

OUT = """1 base x 1.0 0.0 10
1 new x 2.0 0.0 10
2 base x 3.0 0.0 10
2 new x 4.0 0.0 20
1 base y 1.0 0.0 10
1 new y 4.0 0.0 10
1 base timeout 40.0 0.0 124
1 new timeout 40.0 0.0 10
1 base z 5.0 0.0 10
1 new z 5.0 0.0 10
bad line
""".splitlines()


class TableTest(unittest.TestCase):
    def test_parse(self):
        arms, times, bad = l3_table.parse(OUT)
        self.assertEqual(arms, ["base", "new"])
        self.assertEqual(times[("x", "base")], [1.0, 3.0])
        self.assertEqual(bad, {"timeout"})

    def test_table(self):
        lines = l3_table.build_table(*l3_table.parse(OUT))
        self.assertEqual(lines[0], "| instance | base | new | new / base |")
        rows = [l.split(" | ") for l in lines[2:]]
        self.assertEqual([r[0] for r in rows], ["| x", "| y", "| z", "| **geometric mean**"])  # timeout left out
        self.assertIn("| x | 2.00 | 3.00 | 1.500 |", lines)
        self.assertIn("| y | 1.00 | 4.00 | 4.000 |", lines)
        self.assertIn("| **geometric mean** |  | n=3 | **%.3f** |" % math.exp(math.log(1.5 * 4.0) / 3), lines)

    def test_three_arms(self):
        lines = l3_table.build_table(["a", "b", "c"], {("i", "a"): [2.0], ("i", "b"): [1.0], ("i", "c"): [4.0]}, set())
        self.assertEqual(lines[0], "| instance | a | b | b / a | c | c / a |")
        self.assertEqual(lines[2], "| i | 2.00 | 1.00 | 0.500 | 4.00 | 2.000 |")


if __name__ == "__main__":
    unittest.main()
