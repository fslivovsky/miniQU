#!/usr/bin/env python3
"""Engine of tests/regress.sh: run configurations over both corpus tiers.

Not meant to be called directly; see the usage text of tests/regress.sh.

For every configuration and seed the solver's verdict is compared with the
truth (tiny tier: brute force or the "# expected:" line; search tier: the
baseline solver) and with the other configurations; proofs are checked by the
Lean checker; "c stat NAME VALUE" counters are summed and the coverage
assertion of doc/rewrite/ROADMAP.md 0.1 is applied; timeouts are counted.
"""
import argparse
import atexit
import csv
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import tempfile
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
VERDICTS = {10: 'SAT', 20: 'UNSAT'}
STAT_LINE = re.compile(r'^c stat (\S+) (-?\d+)$', re.M)
MIN_COVERAGE = 0.10   # a required counter must be nonzero on this fraction of search instances
DEFAULT_STRESS_LIMIT = 2.0   # percent of search instances; a stress row may set its own


LIVE = set()          # process groups of running children, killed on exit
LIVE_LOCK = threading.Lock()


def kill_group(pid):
    try:
        os.killpg(pid, signal.SIGKILL)
    except ProcessLookupError:
        pass


def run_group(cmd, timeout=None, stdout=subprocess.PIPE):
    """subprocess.run in its own process group, killed as a whole on timeout or exit.

    Wrapper scripts and sanitizer runs start grandchildren that a plain
    kill of the child would leave running. Raises subprocess.TimeoutExpired.
    Returns (returncode, output text).
    """
    with subprocess.Popen(cmd, stdout=stdout, stderr=subprocess.STDOUT,
                          text=True, start_new_session=True) as p:
        with LIVE_LOCK:
            LIVE.add(p.pid)
        try:
            out, _ = p.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            kill_group(p.pid)
            p.communicate()
            raise
        finally:
            kill_group(p.pid)   # stray grandchildren of a finished child
            with LIVE_LOCK:
                LIVE.discard(p.pid)
        return p.returncode, out


def kill_all_children(*_):
    with LIVE_LOCK:
        for pid in LIVE:
            kill_group(pid)
    if _:
        sys.exit(130)


atexit.register(kill_all_children)
signal.signal(signal.SIGTERM, kill_all_children)
signal.signal(signal.SIGINT, kill_all_children)


class Config:
    def __init__(self, name, options, proofs, required, stress, from_matrix, limit=DEFAULT_STRESS_LIMIT):
        self.name, self.options, self.proofs = name, shlex.split(options), proofs
        self.required, self.stress, self.from_matrix = required, stress, from_matrix
        self.limit = limit   # percent of search timeouts that fails a stress row


def read_matrix(path, rows):
    configs = OrderedDict()
    for number, line in enumerate(open(path), 1):
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        fields = [f.strip() for f in line.split('|')]
        if len(fields) not in (5, 6) or fields[2] not in ('yes', 'no') or fields[4] not in ('normal', 'stress'):
            sys.exit('regress.py: %s:%d: expected "name | options | yes/no | counters | normal/stress [| limit]"' %
                     (path, number))
        limit = DEFAULT_STRESS_LIMIT
        if len(fields) == 6:
            try:
                limit = float(fields[5])
            except ValueError:
                limit = -1.0
            if fields[4] != 'stress' or not 0 <= limit <= 100:
                sys.exit('regress.py: %s:%d: the limit "%s" must be a percentage and is only allowed on stress rows' %
                         (path, number, fields[5]))
        configs[fields[0]] = Config(fields[0], fields[1], fields[2] == 'yes', fields[3].split(),
                                    fields[4] == 'stress', True, limit)
    if rows == ['all']:
        return list(configs.values())
    unknown = [r for r in rows if r not in configs]
    if unknown:
        sys.exit('regress.py: unknown matrix rows: %s (known: %s)' % (', '.join(unknown), ', '.join(configs)))
    return [configs[r] for r in rows]


class Run:
    """The outcome of one solver invocation."""
    def __init__(self, verdict, stats):
        self.verdict, self.stats = verdict, stats
        self.proof = None   # set by Context.process: ok, skipped, timeout or failed


def run_solver(solver, path, options, timeout, verbose=False, extra=()):
    cmd = [solver, '-verb=1' if verbose else '-verb=0'] + list(options) + list(extra) + [path]
    try:
        code, out = run_group(cmd, timeout)
    except subprocess.TimeoutExpired:
        return Run('TIMEOUT', {})
    verdict = VERDICTS.get(code, 'exit code %d' % code)
    stats = {name: int(value) for name, value in STAT_LINE.findall(out)}
    return Run(verdict, stats)


class Context:
    def __init__(self, args, configs):
        self.args, self.configs = args, configs

    def reference(self, tier, path):
        """Truth for an instance: the expected line or brute force (tiny), the baseline (search)."""
        if tier == 'tiny':
            expected = re.search(r'^# expected: (\w+)', open(path).read(), re.M)
            if expected:
                return expected.group(1)
            return subprocess.run([sys.executable, os.path.join(HERE, 'qcir_eval.py'), path],
                                  capture_output=True, text=True).stdout.strip()
        for options in ([], ['-dl']):  # the second run only if the first times out
            verdict = run_solver(self.args.baseline, path, options, self.args.timeout).verdict
            if verdict != 'TIMEOUT':
                return verdict
        return None

    def check_proof(self, config, path, expected, tmp):
        """Returns (status, detail): status is ok, skipped, timeout or failed."""
        proof = os.path.join(tmp, 'f.proof')
        extra = shlex.split(self.args.proof_opts) + ['-proof=' + proof]
        run = run_solver(self.args.solver, path, config.options, self.args.timeout, extra=extra)
        if run.verdict == 'TIMEOUT' or not os.path.exists(proof) or os.path.getsize(proof) == 0:
            # Proof logging makes a run slower, and a killed solver leaves a truncated file that is no proof.
            if os.path.exists(proof):
                os.remove(proof)
            return 'skipped', ''
        try:
            _, out = run_group([self.args.checker, path, proof], self.args.check_timeout)
        except subprocess.TimeoutExpired:
            return 'timeout', ''
        finally:
            os.remove(proof)
        want = 'VERIFIED TRUE' if expected == 'SAT' else 'VERIFIED FALSE'
        said = re.search(r'^s (.*)$', out, re.M)
        if said is None or said.group(1) != want:
            return 'failed', "expected '%s', checker said '%s'" % (want, said.group(1) if said else 'nothing')
        return 'ok', ''

    def process(self, tier, seed):
        """Run all configurations on one instance. Returns per-configuration records and failures."""
        records, failures = {}, []
        with tempfile.TemporaryDirectory(dir=self.args.work) as tmp:
            path = os.path.join(tmp, 'f.qcir')
            gen = [sys.executable, os.path.join(HERE, 'corpus.py'), '--tier', tier, '--seed', str(seed), '--out', path]
            subprocess.run(gen, check=True, capture_output=True)
            repro_gen = 'python3 tests/corpus.py --tier %s --seed %d --out f.qcir' % (tier, seed)
            truth = self.reference(tier, path)
            seen = {}   # verdict of the first configuration that finished
            for config in self.configs:
                run = run_solver(self.args.solver, path, config.options, self.args.timeout, verbose=(tier == 'search'))
                records[config.name] = run
                repro = '%s && %s %s f.qcir' % (repro_gen, self.args.solver, shlex.join(config.options))
                problem = None
                if run.verdict not in ('SAT', 'UNSAT', 'TIMEOUT'):
                    problem = 'crashed: %s' % run.verdict
                elif run.verdict != 'TIMEOUT' and truth and run.verdict != truth:
                    problem = 'wrong verdict %s, expected %s' % (run.verdict, truth)
                elif run.verdict != 'TIMEOUT' and seen and run.verdict != next(iter(seen.values())):
                    other = next(iter(seen))
                    problem = 'verdict %s differs from configuration %s' % (run.verdict, other)
                if problem:
                    failures.append('FAIL [%s] %s seed %d: %s\n  repro: %s' % (config.name, tier, seed, problem, repro))
                    self.keep(path, tier, seed)
                    continue
                if run.verdict != 'TIMEOUT':
                    seen.setdefault(config.name, run.verdict)
                    if config.proofs and self.args.proofs:
                        status, detail = self.check_proof(config, path, run.verdict, tmp)
                        run.proof = status
                        if status == 'failed':
                            failures.append('FAIL [%s] %s seed %d: proof rejected: %s\n  repro: %s %s -proof=f.proof && %s f.qcir f.proof' % (
                                config.name, tier, seed, detail, repro.replace(' f.qcir', ''), self.args.proof_opts,
                                self.args.checker))
                            self.keep(path, tier, seed)
        return records, failures

    def keep(self, path, tier, seed):
        os.makedirs(self.args.keep, exist_ok=True)
        with open(path) as src, open(os.path.join(self.args.keep, '%s-%d.qcir' % (tier, seed)), 'w') as dst:
            dst.write(src.read())


def smoke(args, config):
    """Run bench/smoke.txt through bench/run.py and compare with bench/smoke-expected.csv."""
    run_dir = os.path.join(args.work, 'smoke-' + re.sub(r'\W+', '_', config.name))
    shutil.rmtree(run_dir, ignore_errors=True)   # run.py resumes: results of an older binary must not count
    cmd = [sys.executable, os.path.join(REPO, 'bench', 'run.py'), '--solver', args.solver,
           '--args=' + shlex.join(config.options), '--tag', 'regress', '--results-dir', run_dir,
           '--timeout', '120', '--jobs', str(args.jobs), '--cores', '0-%d' % (os.cpu_count() // 2 - 1),
           '--instances', os.path.join(REPO, 'bench', 'smoke.txt'), '--proof-jobs', str(args.jobs),
           '--proof-args=' + args.proof_opts, '--checker', args.checker]
    if config.proofs and args.proofs:
        cmd += ['--proof-check', '--proof-max-solve-sec', '60']
    log = os.path.join(run_dir + '.log')
    with open(log, 'w') as f:
        status, _ = run_group(cmd, stdout=f)
    got = {r['instance']: r for r in csv.DictReader(open(os.path.join(run_dir, 'regress', 'results.csv')))} \
        if status == 0 else {}
    failures, warnings = [], 0
    for r in csv.DictReader(open(os.path.join(REPO, 'bench', 'smoke-expected.csv'))):
        g = got.get(r['instance'])
        if g is None:
            failures.append('smoke: %s missing from results' % r['instance'])
        elif g['result'] in ('SAT', 'UNSAT') and g['result'] != r['result']:
            failures.append('smoke: %s expected %s, got %s' % (r['instance'], r['result'], g['result']))
        elif g['result'] in ('ERROR', 'MISMATCH', 'MEMOUT'):
            failures.append('smoke: %s result %s (exit %s)' % (r['instance'], g['result'], g['exit']))
        elif g['result'] == 'TIMEOUT':
            warnings += 1
        if g and g['proof_status'] not in ('', 'n/a', 'ok'):
            failures.append('smoke: proof of %s: %s' % (r['instance'], g['proof_status']))
    if failures or status != 0:
        failures.append('smoke test of %s failed (log %s); repro: python3 bench/run.py --solver %s --args "%s" '
                        '--tag t --instances bench/smoke.txt --proof-check' %
                        (config.name, log, args.solver, shlex.join(config.options)))
    return failures, warnings


def coverage(config, runs):
    """Coverage table of one configuration. Returns (failures, note)."""
    finished = [r for r in runs if r.verdict in ('SAT', 'UNSAT')]
    names = list(OrderedDict.fromkeys(n for r in finished for n in r.stats))
    if not names and not config.from_matrix:
        return [], 'no "c stat" lines printed (old interface): coverage assertion skipped'
    failures = []
    lines = ['  coverage over %d finished search instances:' % len(finished),
             '    %-18s %12s %9s' % ('counter', 'sum', 'nonzero')]
    for name in names + [n for n in config.required if n not in names]:
        total = sum(r.stats.get(name, 0) for r in finished)
        fraction = sum(1 for r in finished if r.stats.get(name, 0) != 0) / len(finished) if finished else 0.0
        bad = name in config.required and fraction < MIN_COVERAGE
        lines.append('    %-18s %12d %8.0f%%%s' % (name, total, 100 * fraction,
                                                   '  FAIL: required, below %.0f%%' % (100 * MIN_COVERAGE) if bad else
                                                   '  (required)' if name in config.required else ''))
        if bad:
            failures.append('FAIL [%s] counter %s is nonzero on %.0f%% of the finished search instances (need %.0f%%)' %
                            (config.name, name, 100 * fraction, 100 * MIN_COVERAGE))
    return failures, '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--solver', required=True)
    parser.add_argument('--baseline', required=True)
    parser.add_argument('--checker', required=True)
    parser.add_argument('--seeds', required=True, help='FIRST:LAST')
    parser.add_argument('--jobs', type=int, default=16)
    parser.add_argument('--timeout', type=int, default=20)
    parser.add_argument('--check-timeout', type=int, default=120)
    parser.add_argument('--proof-opts', default='-proof-binary')
    parser.add_argument('--no-proofs', dest='proofs', action='store_false')
    parser.add_argument('--no-smoke', dest='smoke', action='store_false')
    parser.add_argument('--no-fuzz', dest='fuzz', action='store_false')
    parser.add_argument('--work', required=True)
    parser.add_argument('--matrix')
    parser.add_argument('--rows', default='all')
    parser.add_argument('--group', action='append', default=[], help='options of one explicit configuration')
    args = parser.parse_args()
    args.keep = os.path.join(args.work, 'failed')
    os.makedirs(args.work, exist_ok=True)

    if args.matrix:
        configs = read_matrix(args.matrix, args.rows.split(','))
    else:
        configs = [Config(re.sub(r'\W+', '_', g.strip()).strip('_') or 'default', g, True, [], False, False)
                   for g in args.group]
    first, last = (int(x) for x in args.seeds.split(':'))
    half = (last - first + 2) // 2   # the first half of the range goes to the tiny tier
    work_items = [('tiny', s) for s in range(first, first + half)] + \
                 [('search', s) for s in range(first + half, last + 1)]
    failures, warnings = [], []

    if args.fuzz:
        ctx = Context(args, configs)
        with ThreadPoolExecutor(args.jobs) as pool:
            results = list(pool.map(lambda item: ctx.process(*item), work_items))
        search_runs = {c.name: [] for c in configs}
        counts = {c.name: {'timeouts': 0, 'proofs': 0, 'proof_timeouts': 0, 'proofs_skipped': 0} for c in configs}  # timeouts: all tiers
        for (tier, seed), (records, instance_failures) in zip(work_items, results):
            failures += instance_failures
            for name, run in records.items():
                if tier == 'search':
                    search_runs[name].append(run)
                counts[name]['timeouts'] += run.verdict == 'TIMEOUT'
                status = run.proof
                counts[name]['proofs'] += status == 'ok'
                counts[name]['proof_timeouts'] += status == 'timeout'
                counts[name]['proofs_skipped'] += status == 'skipped'
        n_search = sum(1 for t, _ in work_items if t == 'search')
        for config in configs:
            c = counts[config.name]
            print('=== configuration %s:%s' % (config.name, ' ' + shlex.join(config.options) if config.options else ' (default options)'))
            print('  tiny seeds %d..%d, search seeds %d..%d: %d timeouts, %d proofs checked, %d proof checks timed out, %d proof runs unfinished (warnings only)' %
                  (first, first + half - 1, first + half, last, c['timeouts'], c['proofs'], c['proof_timeouts'],
                   c['proofs_skipped']))
            search_timeouts = sum(r.verdict == 'TIMEOUT' for r in search_runs[config.name])
            if config.stress:
                print('  stress row: %d of %d search instances timed out (limit %g%%)' %
                      (search_timeouts, n_search, config.limit))
            if config.stress and 100 * search_timeouts > config.limit * n_search:
                failures.append('FAIL [%s] stress configuration: %d of %d search instances timed out (limit %g%%)' %
                                (config.name, search_timeouts, n_search, config.limit))
            elif c['timeouts']:
                warnings.append('WARN [%s] %d solver timeouts' % (config.name, c['timeouts']))
            if n_search:
                cov_failures, text = coverage(config, search_runs[config.name])
                print(text)
                failures += cov_failures

    if args.smoke:
        for config in configs:
            smoke_failures, smoke_timeouts = smoke(args, config)
            print('=== smoke %s: %d failures, %d timeouts' % (config.name, len(smoke_failures), smoke_timeouts))
            failures += ['FAIL [%s] %s' % (config.name, f) for f in smoke_failures]

    print()
    for line in warnings + failures:
        print(line)
    if failures:
        print('REGRESSION TESTS FAILED: %d problem(s)' % len(failures))
        sys.exit(1)
    print('REGRESSION TESTS PASSED (%d warnings)' % len(warnings))


if __name__ == '__main__':
    main()
