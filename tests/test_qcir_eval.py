#!/usr/bin/env python3
"""Tests of the brute-force evaluator qcir_eval.py on every gate kind (run by ctest)."""
import os
import subprocess
import sys
import tempfile
import unittest

EVAL = os.path.join(os.path.dirname(os.path.abspath(__file__)), "qcir_eval.py")


def evaluate(text):
    with tempfile.NamedTemporaryFile("w", suffix=".qcir") as f:
        f.write(text)
        f.flush()
        return subprocess.run([sys.executable, EVAL, f.name], capture_output=True, text=True,
                              check=True).stdout.strip()


class EvalTest(unittest.TestCase):
    def test_xor_of_a_literal_and_its_negation_is_true(self):
        self.assertEqual(evaluate("forall(x)\noutput(g)\ng = xor(x, -x)\n"), "SAT")

    def test_xor_of_equal_inputs_is_false(self):
        self.assertEqual(evaluate("forall(x)\noutput(g)\nh = xor(x, -x)\ng = xor(h, h)\n"), "UNSAT")

    def test_xor_is_parity(self):
        self.assertEqual(evaluate("exists(x, y, z)\noutput(g)\nh = and(x, y, z)\ng = xor(x, y, z, -h)\n"), "SAT")

    def test_ite(self):
        # ite (c, a, -a) is c <-> a: true for a = c, but no fixed a works for both values of c.
        self.assertEqual(evaluate("forall(c)\nexists(a)\noutput(g)\ng = ite(c, a, -a)\n"), "SAT")
        self.assertEqual(evaluate("exists(a)\nforall(c)\noutput(g)\ng = ite(c, a, -a)\n"), "UNSAT")

    def test_free_variables_are_outermost_existential(self):
        self.assertEqual(evaluate("free(x)\nforall(y)\noutput(g)\ng = or(x, y, -y)\n"), "SAT")
        self.assertEqual(evaluate("free(x)\nforall(y)\noutput(g)\ng = and(x, y)\n"), "UNSAT")


if __name__ == "__main__":
    unittest.main()
