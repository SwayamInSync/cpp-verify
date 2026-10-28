#!/usr/bin/env python3
"""Runs the differential cases and exits with 1 when any has a problem.

  run.py --cpp-verify BUILD/bin/cpp-verify [--clang BUILD/bin/clang]
         [--suite NAME]... [--case TEXT]... [--configs z3,cvc5,...]
         [--jobs N] [--timeout MS] [--work DIR] [--report FILE]

A suite is a module of cases/ with CASES and the CONFIGS it runs in.
"""
import argparse
import importlib
import json
import os
import shutil
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
sys.path.insert(0, HERE)
import differential  # noqa: E402

SUITES = ['integers', 'shifts_division', 'contracts', 'loops', 'calls', 'pointers',
          'pointers_bmc', 'expressions', 'loops_bmc', 'bit_int', 'records', 'selftest']
DEFAULT = [s for s in SUITES if s != 'selftest']


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--cpp-verify', required=True)
    parser.add_argument('--clang')
    parser.add_argument('--suite', action='append', choices=SUITES)
    parser.add_argument('--case', action='append')
    parser.add_argument('--configs')
    parser.add_argument('--jobs', type=int, default=os.cpu_count() or 1)
    parser.add_argument('--timeout', type=int, default=30000)
    parser.add_argument('--work')
    parser.add_argument('--report')
    args = parser.parse_args()

    clang = args.clang or os.path.join(os.path.dirname(args.cpp_verify), 'clang')
    work = args.work or tempfile.mkdtemp(prefix='cppverify-differential-')
    os.makedirs(work, exist_ok=True)
    tools = differential.Tools(os.path.abspath(args.cpp_verify), os.path.abspath(clang),
                               os.path.abspath(work), args.timeout)

    jobs = []
    for name in args.suite or DEFAULT:
        suite = importlib.import_module('cases.' + name)
        configs = args.configs.split(',') if args.configs else list(suite.CONFIGS)
        if 'cvc5' in configs and not shutil.which('cvc5'):
            print('note: cvc5 is not on PATH; %s runs without it' % name)
            configs.remove('cvc5')
        for case in suite.CASES:
            if not args.case or any(text in case.name for text in args.case):
                jobs.append((name, case, configs))

    def run(job):
        name, case, configs = job
        suite_tools = differential.Tools(tools.cpp_verify, tools.clang,
                                         os.path.join(tools.workdir, name), tools.timeout_ms)
        os.makedirs(suite_tools.workdir, exist_ok=True)
        try:
            result = differential.run_case(suite_tools, case, configs)
        except Exception as e:  # A case that cannot run is a problem too.
            result = {'case': case.name, 'problems': ['ERROR: %s' % e],
                      'line': '%-40s ERROR' % case.name}
        result['suite'] = name
        return result

    results = []
    with ThreadPoolExecutor(max(1, args.jobs)) as pool:
        for result in pool.map(run, jobs):
            results.append(result)
            print(result['line'])
            for problem in result['problems']:
                print('  problem: ' + problem[:2000])
            sys.stdout.flush()

    problems = [(r['case'], p) for r in results for p in r['problems']]
    print('\n%d cases, %d problems' % (len(results), len(problems)))
    for case, problem in problems:
        print('%s: %s' % (case, problem[:2000]))
    if args.report:
        with open(args.report, 'w') as f:
            json.dump(results, f, indent=1, default=str)
    return 1 if problems else 0


if __name__ == '__main__':
    sys.exit(main())
