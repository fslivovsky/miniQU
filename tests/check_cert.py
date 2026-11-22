#!/usr/bin/env python3
"""Validate the certificate (V line) that a solver prints with -cert.

Usage: check_cert.py [--reference SOLVER] [--timeout SECONDS] [--max-eval-vars N]
                     [--keep FILE] SOLVER FILE [solver options...]

SOLVER is run on FILE (QCIR or QDIMACS) with -cert.  The certificate lists the
decision variables of the outermost block.  It is substituted into the
formula: the block becomes existential and a conjunct fixes its variables,
so the new formula is the original one with the block set to the certificate.
  * SAT with an outermost existential block: the substituted formula must be SAT.
  * UNSAT with an outermost universal block: it must be UNSAT.
  * Otherwise (SAT with a universal, UNSAT with an existential outermost block)
    nothing can be checked but the shape of the line.
The substituted formula is decided with tests/qcir_eval.py when it has at most
--max-eval-vars quantified variables (default 16), otherwise with the
reference solver (default: the frozen baseline).

Prints one line "STATUS FILE detail" with STATUS one of
  VALID      the certificate was substituted and the result is as required
  WELLFORMED the line lists exactly the block's variables (not checkable)
  INVALID    the result changed under the certificate
  MALFORMED  no V line, or it does not list exactly the variables of the block
  TIMEOUT    the solver ran out of time
  UNDECIDED  the reference solver ran out of time on the substituted formula
  ERROR      the solver crashed or answered neither SAT nor UNSAT
and exits with status 1 for INVALID, MALFORMED and ERROR.
"""
import argparse
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
BASELINE = "/home/ec2-user/miniqu-work/baseline/miniQU"
QUANTIFIERS = ("exists", "forall", "free")


class Formula:
    """A QCIR formula as lines, with the positions of the prefix and the output."""

    def __init__(self, text):
        self.lines = text.splitlines()
        self.blocks = []        # (kind, line index, [variable names])
        self.output_line = None
        for index, line in enumerate(self.lines):
            stripped = re.sub(r"\s", "", line).lower()
            if not stripped or stripped.startswith("#"):
                continue
            head, _, args = stripped.partition("(")
            names = [a for a in args.rstrip(")").split(",") if a]
            if head in QUANTIFIERS:
                if names:
                    self.blocks.append(("forall" if head == "forall" else "exists", index, names))
            elif head == "output":
                self.output_line = index

    def output_literal(self):
        return re.sub(r"\s", "", self.lines[self.output_line]).lower()[len("output("):-1]

    def substituted(self, literals):
        """The formula with the outermost block existential and fixed to literals."""
        kind, index, names = self.blocks[0]
        lines = list(self.lines)
        lines[index] = re.sub(r"^(\s*)\w+", r"\1exists", lines[index], count=1)
        lines[self.output_line] = "output(cert_o)"
        lines += ["cert_u = and(%s)" % ", ".join(literals),
                  "cert_o = and(%s, cert_u)" % self.output_literal()]
        return "\n".join(lines) + "\n"


def qcir_text(path):
    """The formula as QCIR; QDIMACS is converted (variable N becomes vN)."""
    if path.endswith((".qcir", ".QCIR")):
        with open(path) as f:
            return f.read(), False
    converted = subprocess.run([sys.executable, os.path.join(HERE, "qdimacs2qcir.py"), path],
                               capture_output=True, text=True, check=True)
    return converted.stdout, True


def run_solver(solver, path, options, timeout):
    try:
        run = subprocess.run([solver, "-cert", "-verb=0"] + options + [path], capture_output=True,
                             text=True, timeout=timeout, errors="replace")
    except subprocess.TimeoutExpired:
        return None, None, None
    verdict = {10: "SAT", 20: "UNSAT"}.get(run.returncode)
    lines = [l for l in run.stdout.splitlines() if l.startswith("V ")]
    return verdict if verdict else "exit %d" % run.returncode, lines, run.returncode


def decide(text, variables, args):
    """SAT, UNSAT or None (timeout) for a QCIR text."""
    with tempfile.NamedTemporaryFile("w", suffix=".qcir", delete=False) as f:
        f.write(text)
        name = f.name
    if args.keep:
        os.replace(name, args.keep)
        name = args.keep
    try:
        if variables <= args.max_eval_vars:
            out = subprocess.run([sys.executable, os.path.join(HERE, "qcir_eval.py"), name],
                                 capture_output=True, text=True, check=True).stdout.strip()
            return out
        try:
            code = subprocess.run([args.reference, "-verb=0", name], capture_output=True,
                                  timeout=args.timeout).returncode
        except subprocess.TimeoutExpired:
            return None
        return {10: "SAT", 20: "UNSAT"}.get(code, "exit %d" % code)
    finally:
        if not args.keep:
            os.unlink(name)


def check(args):
    path = args.file
    solver_verdict, lines, _ = run_solver(args.solver, path, args.options, args.timeout)
    if solver_verdict is None:
        return "TIMEOUT", "solver timed out"
    if solver_verdict not in ("SAT", "UNSAT"):
        return "ERROR", "solver: " + solver_verdict
    text, converted = qcir_text(path)
    formula = Formula(text)
    if not formula.blocks:
        return ("WELLFORMED" if not lines else "MALFORMED"), "no quantified variable; V lines: %d" % len(lines)
    if len(lines) != 1 or not re.fullmatch(r"V( -?\w+)* 0", lines[0]):
        return "MALFORMED", "expected exactly one 'V ... 0' line, got %r" % lines
    kind, _, block = formula.blocks[0]
    literals = lines[0].split()[1:-1]
    # The certificate names variables as the input does: identifiers for QCIR, numbers for QDIMACS.
    names = [("v" + l.lstrip("-") if converted else l.lstrip("-")).lower() for l in literals]
    named = ["-" + n if l.startswith("-") else n for n, l in zip(names, literals)]
    if sorted(names) != sorted(block):
        missing = sorted(set(block) - set(names))
        extra = sorted(set(names) - set(block))
        duplicates = len(names) - len(set(names))
        return "MALFORMED", "certificate lists %d variables, outermost block has %d (missing %s, extra %s, repeated %d)" % (
            len(names), len(block), missing[:5], extra[:5], duplicates)
    if (solver_verdict, kind) not in (("SAT", "exists"), ("UNSAT", "forall")):
        return "WELLFORMED", "%s with outermost %s block: shape only" % (solver_verdict, kind)
    variables = sum(len(b[2]) for b in formula.blocks)
    result = decide(formula.substituted(named), variables, args)
    if result is None:
        return "UNDECIDED", "reference solver timed out"
    if result == solver_verdict:
        return "VALID", "%s stays %s under %d literals" % ("formula", solver_verdict, len(named))
    return "INVALID", "%s but the formula under the certificate is %s" % (solver_verdict, result)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0], usage=__doc__.split("\n\n")[0].split("\n", 1)[0])
    ap.add_argument("--reference", default=BASELINE, help="solver for large substituted formulas")
    ap.add_argument("--timeout", type=float, default=60, help="per solver run, in seconds")
    ap.add_argument("--max-eval-vars", type=int, default=16, help="largest instance for qcir_eval.py")
    ap.add_argument("--keep", help="save the substituted formula here")
    ap.add_argument("solver")
    ap.add_argument("file")
    ap.add_argument("options", nargs=argparse.REMAINDER, help="solver options")
    args = ap.parse_args()
    status, detail = check(args)
    print("%s %s %s" % (status, args.file, detail))
    sys.exit(1 if status in ("INVALID", "MALFORMED", "ERROR") else 0)


if __name__ == "__main__":
    main()
