"""Paired comparison of two run sets (ROADMAP 0.3, "What counts as evidence").

A run set is one binary with one configuration over a list of seeds, one tag
per seed.  The per-instance score is the mean PAR2 over the seeds; the
difference B - A is summarised by its mean with a bootstrap interval and by a
sign test.  The verdict words are defined in ROADMAP 0.3 and nowhere else.
"""
import math
import random

from benchlib import SOLVED, coverage_table, table

BOOTSTRAP_RESAMPLES = 10000
BOOTSTRAP_SEED = 20240607  # fixed: the same data gives the same interval
CONFIDENCE = 0.95
SIGN_ALPHA = 0.05
MARGIN_SECONDS = 1.0       # a score difference below this is a tie ...
MARGIN_FRACTION = 0.10     # ... as is one below this fraction of the smaller score
MEMORY_FACTOR = 1.10
MIN_CPU = 1.0              # identical searches: A must have used more CPU time than this (s)
FAMILY_MIN_N = 3           # identical searches: families need this many instances to be marked ...
FAMILY_LIMIT = 1.10        # ... when their geometric mean exceeds this
LIMIT_KEYS = ("jobs", "mem_gb", "cores", "timeout", "instances_sha256")


def incomparable_reasons(set_a, set_b):
    """Why the two run sets cannot be compared (empty if they can)."""
    reasons = []
    runs = set_a + set_b
    for key in LIMIT_KEYS:
        values = {str(r.meta.get(key)) for r in runs}
        if len(values) > 1:
            label = "instance list" if key == "instances_sha256" else key
            reasons.append("%s differs between runs: %s" % (label, ", ".join(sorted(values))))
    for name, rs in (("A", set_a), ("B", set_b)):
        seeds = [r.meta.get("seed") for r in rs]
        if len(set(seeds)) < len(seeds):
            reasons.append("run set %s repeats a seed: %s" % (name, seeds))
    seeds_a = sorted(str(r.meta.get("seed")) for r in set_a)
    seeds_b = sorted(str(r.meta.get("seed")) for r in set_b)
    if seeds_a != seeds_b:
        reasons.append("seed lists differ: A %s, B %s" % (seeds_a, seeds_b))
    return reasons


def binomial_two_sided(k, n):
    """Two-sided exact binomial p-value of k successes in n fair trials, k <= n/2 or not."""
    if n == 0:
        return 1.0
    k = min(k, n - k)
    tail = sum(math.comb(n, i) for i in range(k + 1)) / 2.0 ** n
    return min(1.0, 2 * tail)


def bootstrap_interval(values):
    """Percentile interval of the mean of values, resampling them with replacement."""
    rng = random.Random(BOOTSTRAP_SEED)
    n = len(values)
    means = sorted(sum(rng.choices(values, k=n)) / n for _ in range(BOOTSTRAP_RESAMPLES))
    tail = (1 - CONFIDENCE) / 2
    return means[int(tail * BOOTSTRAP_RESAMPLES)], means[int((1 - tail) * BOOTSTRAP_RESAMPLES) - 1]


class Comparison:
    """Everything the report needs, computed once from two run sets."""

    def __init__(self, set_a, set_b):
        self.set_a, self.set_b = set_a, set_b
        common = set.intersection(*(set(r.rows) for r in set_a + set_b))
        self.instances = sorted(common)
        self.score_a = {i: sum(r.par2(i) for r in set_a) / len(set_a) for i in self.instances}
        self.score_b = {i: sum(r.par2(i) for r in set_b) / len(set_b) for i in self.instances}
        self.diff = {i: self.score_b[i] - self.score_a[i] for i in self.instances}
        values = [self.diff[i] for i in self.instances]
        self.delta = sum(values) / len(values) if values else 0.0
        self.low, self.high = bootstrap_interval(values) if values else (0.0, 0.0)
        margin = {i: max(MARGIN_SECONDS, MARGIN_FRACTION * min(self.score_a[i], self.score_b[i]))
                  for i in self.instances}
        self.wins = [i for i in self.instances if self.diff[i] < -margin[i]]
        self.losses = [i for i in self.instances if self.diff[i] > margin[i]]
        self.p_value = binomial_two_sided(len(self.wins), len(self.wins) + len(self.losses))
        sign_worse = len(self.losses) > len(self.wins) and self.p_value < SIGN_ALPHA
        sign_better = len(self.wins) > len(self.losses) and self.p_value < SIGN_ALPHA
        self.better = self.high < 0 and not sign_worse
        self.not_worse = not (self.low > 0) and not sign_worse
        if self.better:
            self.verdict = "better"
        elif not self.not_worse:
            self.verdict = "worse"
        else:
            self.verdict = "no measurable difference"
        self.sign_better = sign_better

    def per_seed_rows(self):
        rows = []
        for ra, rb in zip(sorted(self.set_a, key=lambda r: r.meta.get("seed", 0)),
                          sorted(self.set_b, key=lambda r: r.meta.get("seed", 0))):
            row = [ra.meta.get("seed")]
            for r in (ra, rb):
                sat = sum(r.rows[i]["result"] == "SAT" for i in self.instances)
                unsat = sum(r.rows[i]["result"] == "UNSAT" for i in self.instances)
                par2 = sum(r.par2(i) for i in self.instances) / max(1, len(self.instances))
                row += ["%d/%d/%d" % (sat, unsat, sat + unsat), "%.1f" % par2]
            rows.append(row)
        return rows

    def noise_band(self, runs):
        solved = [sum(r.solved(i) for i in self.instances) for r in runs]
        par2 = [sum(r.par2(i) for i in self.instances) / max(1, len(self.instances)) for r in runs]
        return min(solved), max(solved), min(par2), max(par2)

    def majority_changes(self):
        """Instances solved by B and not by A in more than half of the seeds, and the reverse."""
        n = len(self.set_a)
        gained, lost = [], []
        for i in self.instances:
            a = sum(r.solved(i) for r in self.set_a)
            b = sum(r.solved(i) for r in self.set_b)
            both = sum(ra.solved(i) and rb.solved(i) for ra, rb in zip(self.set_a, self.set_b))
            if 2 * (b - both) > n and 2 * (a - both) <= n:
                gained.append(i)
            if 2 * (a - both) > n and 2 * (b - both) <= n:
                lost.append(i)
        return gained, lost

    def family_rows(self):
        family = {i: self.set_a[0].rows[i]["family"] for i in self.instances}
        rows = []
        for fam in sorted(set(family.values())):
            members = [i for i in self.instances if family[i] == fam]
            a = sum(self.score_a[i] for i in members) / len(members)
            b = sum(self.score_b[i] for i in members) / len(members)
            rows.append([fam, len(members), "%.1f" % a, "%.1f" % b, "%+.1f" % (b - a),
                         sum(i in self.wins for i in members), sum(i in self.losses for i in members)])
        return rows

    def memory_rows(self):
        """Instances solved by both arms in every seed where B's peak exceeds A's by more than 10%."""
        rows = []
        for i in self.instances:
            if not all(r.solved(i) for r in self.set_a + self.set_b):
                continue
            a = max(float(r.rows[i]["rss_mb"]) for r in self.set_a)
            b = max(float(r.rows[i]["rss_mb"]) for r in self.set_b)
            if b > MEMORY_FACTOR * a:
                rows.append([i, "%.0f" % a, "%.0f" % b, "%.2fx" % (b / a)])
        return sorted(rows, key=lambda r: -float(r[3][:-1]))


def geomean(values):
    return math.exp(sum(math.log(v) for v in values) / len(values))


class IdenticalSearches:
    """CPU-time ratios B / A of the instances on which both arms ran the same search.

    Per seed, an instance qualifies if both arms solved it with the same result, both
    have a conflict counter that is equal, and A used more than MIN_CPU seconds.
    """

    def __init__(self, set_a, set_b):
        self.per_seed = {}   # seed -> {instance: (cpu_a, cpu_b)}
        for ra, rb in zip(sorted(set_a, key=lambda r: r.meta.get("seed", 0)),
                          sorted(set_b, key=lambda r: r.meta.get("seed", 0))):
            found = {}
            for i in sorted(set(ra.rows) & set(rb.rows)):
                a, b = ra.rows[i], rb.rows[i]
                ca, cb = ra.stats.get(i, {}).get("conflicts"), rb.stats.get(i, {}).get("conflicts")
                if (ra.solved(i) and rb.solved(i) and a["result"] == b["result"]
                        and ca is not None and ca == cb and float(a["cpu"]) > MIN_CPU):
                    found[i] = (float(a["cpu"]), float(b["cpu"]))
            self.per_seed[ra.meta.get("seed")] = found
        self.family = {i: ra.rows[i]["family"] for ra in set_a for i in ra.rows}
        by_instance = {}
        for found in self.per_seed.values():
            for i, (a, b) in found.items():
                by_instance.setdefault(i, []).append((a, b))
        # ratio of an instance: geometric mean over its seeds; cpu: arithmetic mean over its seeds
        self.instances = {i: (geomean([b / a for a, b in v]), sum(a for a, _ in v) / len(v),
                              sum(b for _, b in v) / len(v)) for i, v in by_instance.items()}

    def seed_rows(self):
        rows = []
        for seed, found in sorted(self.per_seed.items(), key=lambda kv: str(kv[0])):
            ratios = [b / a for a, b in found.values()]
            rows.append([seed, len(ratios)] + (
                ["%.3f" % geomean(ratios), sum(r > 1 for r in ratios), sum(r < 1 for r in ratios)]
                if ratios else ["-", 0, 0]))
        ratios = [r for r, _, _ in self.instances.values()]
        rows.append(["all (per instance)", len(ratios)] + (
            ["%.3f" % geomean(ratios), sum(r > 1 for r in ratios), sum(r < 1 for r in ratios)]
            if ratios else ["-", 0, 0]))
        return rows

    def family_rows(self):
        rows = []
        for fam in sorted({self.family[i] for i in self.instances}):
            ratios = [self.instances[i][0] for i in self.instances if self.family[i] == fam]
            g = geomean(ratios)
            mark = "> 1.10" if len(ratios) >= FAMILY_MIN_N and g > FAMILY_LIMIT else ""
            rows.append([fam, len(ratios), "%.3f" % g, mark])
        return rows


def identical_section(set_a, set_b, top=15, bottom=5):
    ident = IdenticalSearches(set_a, set_b)
    out = ["## Identical searches", "",
           "Instances that both arms solved with the same result and the same number of "
           "conflicts (A used more than %g s of CPU time) ran the same search, so the CPU-time "
           "ratio B / A measures engine speed alone." % MIN_CPU, ""]
    if not ident.instances:
        return out + ["no instance with equal conflict counts", ""]
    out += table(["seed", "n", "geometric mean", "slower", "faster"], ident.seed_rows()) + [""]
    out += ["Per family (instances pooled over the seeds; `> 1.10` marks families of at least "
            "%d instances with a geometric mean above %.2f):" % (FAMILY_MIN_N, FAMILY_LIMIT), ""]
    out += table(["family", "n", "geometric mean", "mark"], ident.family_rows()) + [""]
    ordered = sorted(ident.instances.items(), key=lambda kv: -kv[1][0])
    row = lambda kv: [kv[0], "%.3f" % kv[1][0], "%.2f" % kv[1][1], "%.2f" % kv[1][2]]
    hdr = ["instance", "ratio", "A cpu s", "B cpu s"]
    out += ["Largest ratios:", ""] + table(hdr, [row(kv) for kv in ordered[:top]]) + [""]
    out += ["Smallest ratios:", ""] + table(hdr, [row(kv) for kv in reversed(ordered[-bottom:])]) + [""]
    return out


def problems(runs):
    """Blocking problems of a list of runs: verdict discrepancies, solver errors, rejected proofs."""
    out = []
    common = set.intersection(*(set(r.rows) for r in runs))
    for i in sorted(common):
        verdicts = {r.tag: r.rows[i]["result"] for r in runs if r.rows[i]["result"] in SOLVED}
        if len(set(verdicts.values())) > 1:
            out.append("RESULT DISCREPANCY on `%s`: %s" % (i, ", ".join(
                "%s=%s" % kv for kv in sorted(verdicts.items()))))
    for r in runs:
        for i, row in sorted(r.rows.items()):
            if row["result"] in ("ERROR", "MISMATCH"):
                out.append("SOLVER ERROR in `%s` on `%s`: %s (exit %s)" % (r.tag, i, row["result"], row["exit"]))
            if row["proof_status"] in ("rejected", "wrong_verdict", "check_error"):
                out.append("PROOF PROBLEM in `%s` on `%s`: %s" % (r.tag, i, row["proof_status"]))
    return out


def names(instances, limit=40):
    return ", ".join("`%s`" % i for i in instances[:limit]) + (" ..." if len(instances) > limit else "") \
        if instances else "none"


def report(set_a, set_b, reasons, top=30):
    """Markdown report of the paired comparison B against A."""
    cmp = Comparison(set_a, set_b)
    tags_a = ", ".join(r.tag for r in set_a)
    tags_b = ", ".join(r.tag for r in set_b)
    out = []
    if reasons:
        out += ["# NOT COMPARABLE", ""] + ["- " + r for r in reasons] + [""]
    out += ["# Paired comparison: B (%s) against A (%s)" % (tags_b, tags_a), ""]
    found = problems(set_a + set_b)
    if found:
        out += ["## !!! BLOCKING PROBLEMS (%d) !!!" % len(found), ""] + ["- **%s**" % p for p in found] + [""]
    else:
        out += ["No result discrepancies, solver errors or proof problems.", ""]

    meta = set_a[0].meta
    out += ["## Parameters", "",
            "jobs %s, mem_gb %s, cores %s, timeout %s s, %d instances compared, seeds %s." % (
                meta.get("jobs"), meta.get("mem_gb"), meta.get("cores"), meta.get("timeout"),
                len(cmp.instances), sorted(r.meta.get("seed") for r in set_a)), ""]
    table_rows = []
    for name, rs in (("A", set_a), ("B", set_b)):
        m = rs[0].meta
        table_rows.append([name, "`%s`" % m.get("args", ""), m.get("solver_git", "?"),
                           (m.get("solver_sha256") or "?")[:12], m.get("date", "?")])
    out += table(["arm", "args", "git", "sha256", "date"], table_rows) + [""]
    started = sorted((r.meta.get("date", "?"), r.tag) for r in set_a + set_b)
    out += ["Order in which the runs started:", ""]
    out += ["- %s `%s`" % kv for kv in started] + [""]

    out += ["## Result", "",
            "PAR2 difference (B - A, mean over %d instances, scores are means over %d seeds): "
            "**%+.2f s**, 95%% bootstrap interval [%+.2f, %+.2f] (%d resamples)." % (
                len(cmp.instances), len(set_a), cmp.delta, cmp.low, cmp.high, BOOTSTRAP_RESAMPLES), "",
            "Sign test: B wins on %d instances, loses on %d, ties on %d; two-sided p = %.4f "
            "(margin max(%g s, %d%% of the smaller score))." % (
                len(cmp.wins), len(cmp.losses), len(cmp.instances) - len(cmp.wins) - len(cmp.losses),
                cmp.p_value, MARGIN_SECONDS, round(100 * MARGIN_FRACTION)), "",
            "**Verdict: B is %s than A.**" % cmp.verdict if cmp.verdict in ("better", "worse") else
            "**Verdict: %s.**" % cmp.verdict, "",
            "B is not worse than A: **%s**." % ("yes" if cmp.not_worse else "no"), ""]

    out += identical_section(set_a, set_b)

    out += ["## Per seed (SAT/UNSAT/total solved, PAR2 in s)", ""]
    out += table(["seed", "A solved", "A PAR2", "B solved", "B PAR2"], cmp.per_seed_rows()) + [""]
    band = []
    for name, rs in (("A", set_a), ("B", set_b)):
        lo, hi, plo, phi = cmp.noise_band(rs)
        band.append([name, "%d-%d" % (lo, hi), "%.1f-%.1f" % (plo, phi)])
    out += ["Noise band (spread over the seeds of one arm):", ""]
    out += table(["arm", "solved", "PAR2"], band) + [""]

    gained, lost = cmp.majority_changes()
    out += ["## Instances gained and lost in a majority of seeds", "",
            "- gained by B (%d): %s" % (len(gained), names(gained)),
            "- lost by B (%d): %s" % (len(lost), names(lost)), ""]

    out += ["## Per family (mean score in s)", ""]
    out += table(["family", "n", "A", "B", "B - A", "wins", "losses"], cmp.family_rows()) + [""]

    ordered = sorted(cmp.instances, key=lambda i: cmp.diff[i])
    row = lambda i: [i, "%.1f" % cmp.score_a[i], "%.1f" % cmp.score_b[i], "%+.1f" % cmp.diff[i]]
    hdr = ["instance", "A score", "B score", "B - A"]
    faster = [i for i in ordered if cmp.diff[i] < 0][:top // 3]
    slower = [i for i in reversed(ordered) if cmp.diff[i] > 0][:top // 3]
    out += ["## Largest differences", "", "B faster:", ""] + table(hdr, [row(i) for i in faster]) + [""]
    out += ["B slower:", ""] + table(hdr, [row(i) for i in slower]) + [""]

    memory = cmp.memory_rows()
    out += ["## Peak memory", "",
            "%d instances solved by both arms in every seed where B's peak RSS exceeds A's by more than %d%%." % (
                len(memory), round(100 * (MEMORY_FACTOR - 1))), ""]
    if memory:
        out += table(["instance", "A MB", "B MB", "ratio"], memory[:top]) + [""]

    if any(r.rows[i]["proof_status"] not in ("", "n/a") or r.meta.get("proof_check")
           for r in set_a + set_b for i in cmp.instances):
        out += ["## Proof coverage", ""] + coverage_table(set_a + set_b)
    return "\n".join(out) + "\n", cmp
