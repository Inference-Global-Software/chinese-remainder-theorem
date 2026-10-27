#!/usr/bin/env python3
"""Run the native infs project build and record provenance for the proof audit."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--infs', default=os.environ.get('INFS', 'infs'))
    parser.add_argument('--infc', help='Explicit compiler override, equivalent to INFC_PATH')
    parser.add_argument('--project-dir', type=Path, default=ROOT,
                        help='Native project directory (default: repository root)')
    args = parser.parse_args()
    project = args.project_dir.resolve()
    infs = Path(shutil.which(args.infs) or args.infs).resolve()
    source = project / 'src/main.inf'
    output = project / 'out'
    output.mkdir(parents=True, exist_ok=True)
    for name in ('main.wasm', 'main.v', 'manifest.json'):
        (output / name).unlink(missing_ok=True)
    env = dict(os.environ, INFS_VERBOSE='1')
    if args.infc:
        env['INFC_PATH'] = str(Path(shutil.which(args.infc) or args.infc).resolve())
    build = subprocess.run([str(infs), 'build'], cwd=project, env=env, text=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    print(build.stdout, end='')
    print(build.stderr, end='', file=sys.stderr)
    build.check_returncode()
    # Let infs resolve installed, adjacent, PATH, and explicitly selected compilers.
    resolved = re.findall(r'^infs: resolved infc via [^:\n]+: (.+)$', build.stderr, re.M)
    if len(resolved) != 1:
        parser.error('Cannot identify the compiler from infs resolution output.')
    compiler = Path(resolved[0]).resolve()
    if not (output / 'main.v').is_file():
        parser.error('Proof artifacts are missing; use the committed proof-mode Inference.toml.')

    def version(flag):
        return subprocess.check_output([str(compiler), flag], text=True).strip()

    manifest = {
        'mode': 'proof',
        'project': {'path': 'Inference.toml', 'sha256': sha256(project / 'Inference.toml')},
        'infs': {'version': subprocess.check_output([str(infs), '--version'], text=True).strip(),
                 'sha256': sha256(infs)},
        'compiler': {'version': version('--version'), 'commit': version('--commit-hash'),
                     'abi': version('--abi-version'), 'sha256': sha256(compiler)},
        'source': {'path': 'src/main.inf', 'sha256': sha256(source)},
        'artifacts': {name: sha256(output / name) for name in ('main.wasm', 'main.v')},
        'compiled_wasm_proof': 'pending',
    }
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'Built {output / "main.wasm"}; manifest: {output / "manifest.json"}')


if __name__ == '__main__':
    main()
