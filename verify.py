#!/usr/bin/env python3
"""Compile the review statements, their proofs, every dependency, and the axiom audit.

Run `lake update` and `lake exe cache get` first. Requires Python 3.11+.
The default is a fresh check; --resume reuses only this script's recorded,
unchanged successful builds and invalidates their transitive dependents.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parent


def lean_sources():
    config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    sources = {}
    for library in config['lean_lib']:
        for name in library['roots']:
            path = ROOT / library.get('srcDir', '.') / (name.replace('.', '/') + '.lean')
            if name in sources or not path.is_file():
                raise ValueError('Duplicate or missing module: ' + name)
            sources[name] = path
    actual = set((ROOT / 'Shared').rglob('*.lean')) | set((ROOT / 'Cases').rglob('*.lean')) | set(ROOT.glob('*.lean'))
    if actual != set(sources.values()):
        raise ValueError('The source tree and Lake roots differ')
    for path in sources.values():
        body = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
        body = re.sub(r'--[^\n]*', '', body)
        if re.search(r'\b(sorry|admit|native_decide|implemented_by|unsafe)\b|(?m:^\s*(axiom|constant)\b)', body):
            raise ValueError('Unsupported proof escape in ' + str(path))
    dependencies = {n: {d for line in p.read_text().splitlines()
                        if line.startswith('import ') for d in line.split()[1:]
                        if d in sources} for n, p in sources.items()}
    used = set()
    def visit(n):
        if n not in used:
            used.add(n)
            for d in dependencies[n]:
                visit(d)
    visit('Audit')
    if used != set(sources):
        raise ValueError('Unused project modules: ' + repr(set(sources) - used))
    return sources


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--resume', action='store_true')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    output = ROOT / '.verification'
    logs = output / 'logs'
    oleans = output / 'olean'
    logs.mkdir(parents=True, exist_ok=True)
    oleans.mkdir(exist_ok=True)
    env = json.loads(subprocess.check_output(
        ['lake', 'env', sys.executable, '-c',
         'import json,os; print(json.dumps(dict(os.environ)))'],
        cwd=ROOT, text=True))
    env['LEAN_PATH'] = str(oleans) + os.pathsep + env.get('LEAN_PATH', '')
    sources = lean_sources()
    deps = {name: {d for line in p.read_text().splitlines()
                   if line.startswith('import ')
                   for d in line.split()[1:] if d in sources}
            for name, p in sources.items()}
    source_hashes = {name: digest(p) for name, p in sources.items()}
    toolchain = {
        'lean': subprocess.check_output(['lean', '--version'], env=env, text=True).strip(),
        'lean_toolchain_sha256': digest(ROOT / 'lean-toolchain'),
        'lakefile_sha256': digest(ROOT / 'lakefile.toml'),
        'lake_manifest_sha256': digest(ROOT / 'lake-manifest.json'),
    }
    checkpoint = output / 'build-state.json'
    prior = json.loads(checkpoint.read_text()) if args.resume and checkpoint.exists() else {}
    done, running, records = set(), {}, {}
    if prior.get('toolchain') == toolchain:
        for name, record in prior.get('compiler_results', {}).items():
            artifact = oleans / (name + '.olean')
            if (name in sources and record['exit_code'] == 0 and artifact.exists()
                    and record.get('source_sha256') == source_hashes[name]
                    and record.get('olean_sha256') == digest(artifact)):
                done.add(name)
                records[name] = record
        while True:
            invalid = {n for n in done if not deps[n] <= done}
            if not invalid:
                break
            done -= invalid
        records = {n: records[n] for n in done}

    def save():
        checkpoint.write_text(json.dumps({'toolchain': toolchain,
                             'compiler_results': records}, indent=2) + '\n')

    def check(name):
        started = time.monotonic()
        path = sources[name]
        artifact = oleans / (name + '.olean')
        with (logs / (name + '.log')).open('w') as log:
            result = subprocess.run(
                ['lean', '-j', '1', '-R', str(path.parent), '-o', str(artifact), str(path)],
                cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        return {'exit_code': result.returncode,
                'seconds': round(time.monotonic() - started, 2),
                'source': str(path.relative_to(ROOT)),
                'source_sha256': source_hashes[name],
                'olean_sha256': digest(artifact) if result.returncode == 0 else None}

    print(f'Checking {len(sources)} modules; {len(done)} reusable completed checks.', flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while len(done) < len(sources):
            for name in sorted(sources):
                if name not in done and name not in running and deps[name] <= done:
                    if len(running) >= args.jobs:
                        break
                    running[name] = pool.submit(check, name)
            if not running:
                raise RuntimeError('Unresolved project import cycle')
            concurrent.futures.wait(running.values(),
                                    return_when=concurrent.futures.FIRST_COMPLETED)
            for name, future in list(running.items()):
                if future.done():
                    record = future.result()
                    records[name] = record
                    del running[name]
                    save()
                    print(f'{name}: exit {record["exit_code"]}, {record["seconds"]} s', flush=True)
                    if record['exit_code']:
                        print((logs / (name + '.log')).read_text())
                        raise SystemExit(1)
                    done.add(name)

    audit = (logs / 'Audit.log').read_text()
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    used = {a.strip() for group in re.findall(
        r'depends on axioms:\s*\[([^]]*)\]', audit, re.S)
            for a in group.split(',') if a.strip()}
    if not used <= allowed:
        raise RuntimeError('Unexpected axioms: ' + repr(used - allowed))
    declarations = len(re.findall(r'^#print axioms ', sources['Audit'].read_text(), re.M))
    reported = len(re.findall(r'depends on axioms:|does not depend on any axioms', audit))
    if reported != declarations:
        raise RuntimeError(f'Incomplete audit output: {reported}/{declarations}')
    result = {'toolchain': toolchain, 'compiler_results': records,
              'audited_declarations': declarations, 'axioms_used': sorted(used),
              'source_sha256': {str(p.relative_to(ROOT)): source_hashes[n]
                                for n, p in sorted(sources.items())}}
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'PASS: {len(sources)} modules; {declarations} audited declarations.', flush=True)


if __name__ == '__main__':
    main()
