#!/usr/bin/env python3
"""Compile the active dependency closure and audit with an installed Lean.

No installation or network access. Linux receipts never certify run.cmd.
Only unchanged, fingerprint-matched successful local compilations are reused.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def atomic_json(path, value):
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(value, indent=2) + '\n')
    temp.replace(path)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean', required=True, type=Path)
    ap.add_argument('--mathlib', required=True, type=Path)
    ap.add_argument('--preload', type=Path)
    ap.add_argument('--jobs', type=int, default=3)
    args = ap.parse_args()
    root = Path(__file__).resolve().parents[1]
    build = root / '.build' / 'local-lean433'
    objects, logs, states = [build / n for n in ('objects', 'logs', 'states')]
    for p in (objects, logs, states):
        p.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    if args.preload:
        env['LD_PRELOAD'] = str(args.preload.resolve())
    lean = args.lean.resolve()
    mathlib = args.mathlib.resolve()
    core = lean.parent.parent / 'lib' / 'lean'
    external = [mathlib / '.lake/build/lib/lean']
    external += sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean'))
    env['LEAN_PATH'] = ':'.join(map(str, [objects, *external, core]))
    env['LEAN_SYSROOT'] = str(lean.parent.parent)
    version = subprocess.check_output([str(lean), '--version'], env=env, text=True).strip()
    if 'version 4.33.0,' not in version:
        raise RuntimeError('Expected exact stable Lean 4.33.0: ' + version)
    mathlib_commit = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
    expected_commit = 'db584cd6d46c92f209a44c0f1c829460d327499d'
    if mathlib_commit != expected_commit:
        raise RuntimeError('Unexpected Mathlib commit: ' + mathlib_commit)
    print('ENVIRONMENT_HASHING', flush=True)
    fingerprints = {}
    suffixes = ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig', '.so')
    for tree in [core, *external]:
        for p in sorted(tree.rglob('*')):
            if p.is_file() and p.name.endswith(suffixes):
                fingerprints[str(p)] = digest(p)
    environment = {'lean_version': version, 'compiler_sha256': digest(lean),
                   'mathlib_commit': mathlib_commit, 'lean_path': env['LEAN_PATH'],
                   'flags': ['-j', '2'], 'binary_tree': fingerprints,
                   'runner_sha256': digest(Path(__file__))}
    if args.preload:
        environment['compatibility_preload_sha256'] = digest(args.preload)
    atomic_json(build / 'environment.json', environment)
    env_sha = digest(build / 'environment.json')
    modules = [x.strip() for x in (root / 'modules.txt').read_text().splitlines() if x.strip() and not x.startswith('#')]
    if len(set(modules)) != len(modules) or modules[-1] != 'LeanPaper.KernelAudit':
        raise RuntimeError('Invalid active module plan')
    paths = {m: root / 'src' / (m.replace('.', '/') + '.lean') for m in modules}
    imports = {m: re.findall(r'^import\s+([A-Za-z0-9_.]+)', p.read_text(), re.M) for m, p in paths.items()}
    deps = {m: [d for d in imports[m] if d in paths] for m in modules}
    for m, ds in imports.items():
        unknown = [d for d in ds if d not in paths and not d.startswith(('Mathlib', 'Lean', 'Std', 'Init'))]
        if unknown:
            raise RuntimeError(f'Unknown imports in {m}: {unknown}')
    results = {}
    def compile_one(module):
        out = objects / (module.replace('.', '/') + '.olean')
        out.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (module + '.log')
        receipt = states / (module + '.json')
        inputs = {'source_sha256': digest(paths[module]), 'environment_sha256': env_sha,
                  'dependencies': {d: results[d]['output_hashes'] for d in deps[module]}}
        previous = json.loads(receipt.read_text()) if receipt.exists() else {}
        previous_outputs = previous.get('output_hashes', {})
        if (previous.get('inputs') == inputs and previous.get('status') == 'PASS'
                and previous_outputs and log.exists() and digest(log) == previous.get('log_sha256')
                and all((objects / f).exists() and digest(objects / f) == h for f, h in previous_outputs.items())):
            previous['action'] = 'REUSED_LOCAL_PASS'
            return previous
        for suffix in ['', '.private', '.server']:
            Path(str(out) + suffix).unlink(missing_ok=True)
        start = time.monotonic()
        cmd = [str(lean), '-j', '2', '-o', str(out), module.replace('.', '/') + '.lean']
        with log.open('w') as stream:
            process = subprocess.run(cmd, cwd=root / 'src', env=env, stdout=stream, stderr=subprocess.STDOUT)
        status = 'PASS' if process.returncode == 0 and out.exists() and digest(paths[module]) == inputs['source_sha256'] else 'FAIL'
        output_hashes = {str(p.relative_to(objects)): digest(p) for p in sorted(out.parent.glob(out.stem + '.*')) if p.is_file()} if status == 'PASS' else {}
        result = {'module': module, 'status': status, 'action': 'COMPILED',
                  'seconds': round(time.monotonic()-start, 3), 'returncode': process.returncode,
                  'inputs': inputs, 'output_hashes': output_hashes, 'log_sha256': digest(log)}
        atomic_json(receipt, result)
        return result
    pending = set(modules)
    running = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            for m in modules:
                if m not in pending:
                    continue
                if any(d in results and results[d]['status'] != 'PASS' for d in deps[m]):
                    results[m] = {'module': m, 'status': 'BLOCKED', 'action': 'DEPENDENCY_FAILURE'}
                    pending.remove(m)
                elif len(running) < args.jobs and all(d in results for d in deps[m]):
                    running[pool.submit(compile_one, m)] = m
                    pending.remove(m)
            if not running:
                if pending:
                    raise RuntimeError('Dependency cycle: ' + ', '.join(sorted(pending)))
                break
            done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                m = running.pop(future)
                results[m] = future.result()
                print(m + ': ' + results[m]['status'] + ' ' + results[m]['action'], flush=True)
    audit_log = logs / 'LeanPaper.KernelAudit.log'
    accepted = (results['LeanPaper.KernelAudit']['status'] == 'PASS' and audit_log.exists()
                and 'AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS' in audit_log.read_text())
    summary = {'platform': 'LINUX_LOCAL', 'lean_version': version, 'mathlib_commit': mathlib_commit,
               'environment_sha256': env_sha, 'total': len(modules),
               'passed': sum(r['status'] == 'PASS' for r in results.values()),
               'failed': [m for m, r in results.items() if r['status'] == 'FAIL'],
               'blocked': [m for m, r in results.items() if r['status'] == 'BLOCKED'],
               'axiom_audit_accepted': accepted, 'windows_native_runner': 'NOT_RUN',
               'full_manuscript_equivalence': 'NOT_CERTIFIED', 'modules': [results[m] for m in modules]}
    atomic_json(build / 'summary.json', summary)
    print(json.dumps({k:v for k,v in summary.items() if k != 'modules'}), flush=True)
    return 0 if summary['passed'] == len(modules) and accepted else 1


if __name__ == '__main__':
    raise SystemExit(main())
