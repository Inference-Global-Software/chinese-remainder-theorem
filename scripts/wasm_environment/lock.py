#!/usr/bin/env python3
"""Render exact opam dependencies and verify the installed package versions."""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("render", "check"))
    parser.add_argument("opam_file", nargs="?", type=Path)
    args = parser.parse_args()
    recipe_dir = Path(__file__).resolve().parent
    raw_lock = (recipe_dir / "worker-opam.lock.json").read_bytes()
    provenance = json.loads((recipe_dir / "provenance.json").read_text())
    if hashlib.sha256(raw_lock).hexdigest() != provenance["dependencyLock"]["sha256"]:
        parser.error("dependency lock differs from its recorded upstream checksum")
    lock = json.loads(raw_lock)
    if lock["baseImage"] != provenance["baseImage"]:
        parser.error("base image differs between provenance and dependency lock")
    if lock["pins"]["coq-wasm"]["source"].split("#")[-1] != provenance["coqWasmCommit"]:
        parser.error("WasmCert commit differs between provenance and dependency lock")

    if args.command == "render":
        if args.opam_file is None:
            parser.error("render requires the verifier's opam file")
        source = args.opam_file.read_text()
        dependencies = "depends: [\n" + "".join(
            f'  "{name}" {{= "{version}"}}\n'
            for name, version in sorted(lock["dependencies"].items())
        ) + "]\n"
        rendered, count = re.subn(r"^depends:\s*\[.*?^\]\n", dependencies,
                                 source, flags=re.MULTILINE | re.DOTALL)
        if count != 1 or "pin-depends" in source:
            parser.error("expected one depends block and no pin-depends in opam file")
        args.opam_file.with_suffix(args.opam_file.suffix + ".locked").write_text(rendered)
        return

    output = subprocess.check_output(
        ["opam", "list", "--installed", "--columns=name,version", "--color=never"],
        text=True,
    )
    installed = dict(line.split() for line in output.splitlines()
                     if line.strip() and not line.startswith("#"))
    expected = lock["installed"]
    differences = [f"{name}: installed={installed.get(name)!r}, locked={expected.get(name)!r}"
                   for name in sorted(installed.keys() | expected.keys())
                   if installed.get(name) != expected.get(name)]
    if differences:
        parser.error("installed package set differs from lock:\n" + "\n".join(differences))
    print(f"OPAM LOCK: OK ({len(installed)} exact installed package versions)")


if __name__ == "__main__":
    main()
