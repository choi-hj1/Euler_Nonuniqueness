#!/usr/bin/env python3
"""Fresh, process-isolated execution of every command in the project's Audit.lean."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed, CancelledError
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
AXIOM = re.compile(r'^#print axioms\s+(\S+)\s*$')


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def source_fingerprint(root):
    paths = sorted((root / 'EulerNonuniqueness').rglob('*.lean')) + sorted(root.glob('*.lean'))
    paths += [root / 'scripts/check_audit.py', root / 'scripts/run_axiom_audit.py']
    digest = hashlib.sha256()
    for path in paths:
        digest.update(path.relative_to(root).as_posix().encode() + b'\0')
        digest.update(path.read_bytes() + b'\0')
    return digest.hexdigest()


def load_guards(root):
    specification = importlib.util.spec_from_file_location('project_audit_guards', root / 'scripts/check_audit.py')
    require(specification is not None and specification.loader is not None, 'Cannot load existing audit checker')
    guards = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(guards)
    require(guards.ROOT == root, 'Checker root differs from requested project')
    return guards


def prepare(root, directory, batch_size, guards):
    expected = guards.check_sources()
    raw = (root / 'Audit.lean').read_bytes()
    source = raw.decode('utf-8')
    lines = source.splitlines(keepends=True)
    code_lines = guards.lean_code(source).splitlines(keepends=True)
    require(len(lines) == len(code_lines), 'Audit lexer changed line count')
    commands = [(index, AXIOM.fullmatch(line.strip()).group(1)) for index, line in enumerate(code_lines)
                if AXIOM.fullmatch(line.strip())]
    require(commands and Counter(name for _, name in commands) == Counter(expected), 'Audit command coverage differs')
    first = commands[0][0]
    for line in code_lines[first:]:
        stripped = line.strip()
        require(not stripped or AXIOM.fullmatch(stripped) or re.fullmatch(r'#check\s+\S+', stripped),
                'Unsupported command inside audit ranges; do not split state-changing commands')
    context = []
    for original, code in zip(lines[:first], code_lines[:first]):
        stripped = code.strip()
        if stripped.startswith(('#print ', '#check ')):
            require(re.fullmatch(r'#(?:print|check)\s+\S+', stripped), 'Unsupported multiline header output command')
            continue
        require(not stripped or stripped.startswith(('import ', 'set_option ', 'open ')),
                'Unsupported context command; preserve its semantics explicitly before batching')
        context.append(original)
    # Header commands run once; context-only prefix is repeated without its #print/#check commands.
    header = directory / 'header.lean'
    header.write_bytes(''.join(lines[:first]).encode('utf-8'))
    tasks = [{'index': -1, 'driver': header, 'output': directory / 'header.txt', 'names': []}]
    ranges = []
    for number, offset in enumerate(range(0, len(commands), batch_size)):
        selected = commands[offset:offset + batch_size]
        start = selected[0][0]
        stop = commands[offset + batch_size][0] if offset + batch_size < len(commands) else len(lines)
        # No axiom command is synthesized or dropped: this is an exact source-line range.
        driver = directory / ('batch-%04d.lean' % number)
        driver.write_bytes((''.join(context) + ''.join(lines[start:stop])).encode('utf-8'))
        names = [name for _, name in selected]
        tasks.append({'index': number, 'driver': driver, 'output': directory / ('batch-%04d.txt' % number), 'names': names})
        ranges.append({'batch': number, 'firstAuditLine': start + 1, 'lastAuditLine': stop,
                       'names': names, 'driverSHA256': sha(driver.read_bytes())})
    manifest = {'auditSHA256': sha(raw), 'sourceFingerprint': source_fingerprint(root),
                'expectedReports': len(commands), 'batchSize': batch_size, 'batches': ranges}
    (directory / 'plan.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
    return tasks, expected, manifest


def run_task(task, root, lake, guards):
    started = time.monotonic()
    command = [lake, 'env', 'lean', '-DautoImplicit=false', str(task['driver'])]
    with task['output'].open('wb') as output:
        result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
    require(result.returncode == 0, 'Lean process failed (%s), driver=%s, output=%s' %
            (result.returncode, task['driver'], task['output']))
    text = task['output'].read_text(encoding='utf-8')
    guards.check_output(text, task['names'], False)
    return {'batch': task['index'], 'reports': len(task['names']), 'seconds': round(time.monotonic() - started, 2),
            'sha256': sha(task['output'].read_bytes())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--lake', default=None)
    parser.add_argument('--output', type=Path, default=Path('build/axioms.txt'))
    parser.add_argument('--work-dir', type=Path, default=None)
    parser.add_argument('--batch-size', type=int, default=256)
    parser.add_argument('--jobs', type=int, default=3)
    parser.add_argument('--plan-only', action='store_true', help='Validate all sources and generate drivers; does not certify output')
    arguments = parser.parse_args()
    require(1 <= arguments.batch_size <= 256, 'Batch size must lie in [1,256]')
    require(1 <= arguments.jobs <= 3, 'Worker count must lie in [1,3]')
    root = arguments.root.resolve()
    output = arguments.output if arguments.output.is_absolute() else root / arguments.output
    parent = arguments.work_dir or output.parent / 'audit-batches'
    parent.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix='fresh-', dir=parent))
    lake = arguments.lake or (str(root / '.toolchain/bin/lake') if (root / '.toolchain/bin/lake').is_file() else shutil.which('lake'))
    require(lake, 'Lake executable unavailable')
    if '/' in lake and not Path(lake).is_absolute():
        lake = str((root / lake).resolve())
    guards = load_guards(root)
    tasks, expected, manifest = prepare(root, directory, arguments.batch_size, guards)
    print(json.dumps({'plan': str(directory / 'plan.json'), 'reports': len(expected),
                      'freshProcesses': len(tasks), 'jobs': arguments.jobs}), flush=True)
    if arguments.plan_only:
        print('PLAN ONLY: no Lean output certified; no final axioms file written.', flush=True)
        return
    # Complete/check the printed target and conditional-input header exactly once.
    reports = [run_task(tasks[0], root, lake, guards)]
    sys.stdout.write(tasks[0]['output'].read_text(encoding='utf-8'))
    sys.stdout.flush()
    failures = []
    with ThreadPoolExecutor(max_workers=arguments.jobs) as pool:
        pending = {pool.submit(run_task, task, root, lake, guards): task for task in tasks[1:]}
        for future in as_completed(pending):
            try:
                report = future.result()
                reports.append(report)
                print(json.dumps(report), flush=True)
            except CancelledError:
                pass
            except Exception as error:
                failures.append(str(error))
                for other in pending:
                    other.cancel()
    # The executor context has closed every running child before any output can be published.
    require(not failures, '\n'.join(failures))
    require(len(reports) == len(tasks), 'Not every fresh process completed')
    require(guards.check_sources() == expected, 'Source theorem coverage changed during audit')
    require(source_fingerprint(root) == manifest['sourceFingerprint'], 'Project sources changed during audit')
    require(sha((root / 'Audit.lean').read_bytes()) == manifest['auditSHA256'], 'Audit commands changed during audit')
    combined = directory / 'combined.txt'
    with combined.open('wb') as destination:
        for task in tasks:
            raw = task['output'].read_bytes()
            destination.write(raw)
            if raw and not raw.endswith(b'\n'):
                destination.write(b'\n')
    guards.check_output(combined.read_text(encoding='utf-8'), expected, True)
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(output.name + '.tmp')
    shutil.copyfile(combined, temporary)
    os.replace(temporary, output)
    manifest.update(processReports=sorted(reports, key=lambda item: item['batch']),
                    combinedSHA256=sha(output.read_bytes()), combinedByteLen=output.stat().st_size)
    (directory / 'complete.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
    print('FRESH_BATCHED_AXIOM_AUDIT_COMPLETE reports=%d output=%s sha256=%s' %
          (len(expected), output, manifest['combinedSHA256']), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('BATCHED AUDIT FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
