#!/usr/bin/env python3
"""Compile the implementation in proof mode and record exact input/output hashes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--infc', default=os.environ.get('INFC') or shutil.which('infc'))
    parser.add_argument('--out', type=Path, default=ROOT / 'build/crt')
    args = parser.parse_args()
    if not args.infc:
        parser.error('Set INFC or pass --infc with the path to the Inference compiler.')
    compiler = Path(shutil.which(args.infc) or args.infc).resolve()
    source = ROOT / 'src/crt.inf'
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    subprocess.run([str(compiler), str(source), '--mode', 'proof', '--out-dir', str(output)],
                   check=True)

    def version(flag):
        return subprocess.check_output([str(compiler), flag], text=True).strip()

    manifest = {
        'mode': 'proof',
        'compiler': {'version': version('--version'), 'commit': version('--commit-hash'),
                     'abi': version('--abi-version'), 'sha256': sha256(compiler)},
        'source': {'path': 'src/crt.inf', 'sha256': sha256(source)},
        'artifacts': {name: sha256(output / name) for name in ('crt.wasm', 'crt.v')},
        'compiled_wasm_proof': 'pending',
    }
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'Built {output / "crt.wasm"}; manifest: {output / "manifest.json"}')


if __name__ == '__main__':
    main()
