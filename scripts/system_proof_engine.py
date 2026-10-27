"""Snapshot, compilation, assumption and kernel audit shared by system gates.

The entry points pass their fixed module list and signatures explicitly; this
engine does not weaken or infer the target set from the proofs being checked.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from check_proofs import FORBIDDEN, uncomment
from check_wasm_proofs import audit_assumptions
from check_system_infrastructure import InputSnapshot, legacy_modules

def run_gate(*, root, checker_inputs, modules, math_sources_names, exact_checks,
             declarations, description, default_out, report_metadata,
             target_label, environment_check):
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument('--out', type=Path, default=root / default_out)
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report = out / 'report.json'
    report.unlink(missing_ok=True)
    error = environment_check()
    if error:
        parser.error(error)
    snapshot = InputSnapshot()
    for checker in checker_inputs:
        snapshot.read(checker)
    for name in ('provenance.json', 'worker-opam.lock.json'):
        snapshot.read(root / 'scripts/wasm_environment' / name)
    allowfile = root / 'proofs/wasm/assumptions.allow'
    allowed = set(snapshot.text(allowfile).splitlines())
    manifests = {}
    for project, artifact_dir in [('systems', root / 'systems/out'), ('legacy', root / 'out')]:
        manifest = json.loads(snapshot.text(artifact_dir / 'manifest.json'))
        project_root = root / 'systems' if project == 'systems' else root
        for key, path in [('source', project_root / 'src/main.inf'), ('project', project_root / 'Inference.toml')]:
            if manifest[key]['sha256'] != snapshot.digest(path):
                parser.error(f'Stale {project} {key}: rebuild in proof mode')
        if manifest['mode'] != 'proof':
            parser.error(project + ' artifacts must be built in proof mode')
        for name in ('main.v', 'main.wasm'):
            if manifest['artifacts'][name] != snapshot.digest(artifact_dir / name):
                parser.error(f'Stale or modified {project} artifact: {name}')
        manifests[project] = manifest
    system_sources = [root / 'proofs/systems' / (name + '.v') for name in modules]
    legacy = legacy_modules(system_sources, snapshot)
    legacy_sources = [root / 'proofs/wasm' / (name + '.v') for name in legacy]
    math_sources = [root / name for name in math_sources_names]
    dirs = {name: out / name for name in ['math', 'generated', 'legacy-generated', 'legacy', 'systems']}
    for directory in dirs.values():
        directory.mkdir(exist_ok=True)
        for stale in directory.iterdir():
            if stale.is_file():
                stale.unlink()
    audited, hashes = [], {}
    for namespace, sources, target in [('CRT', math_sources, dirs['math']),
                                       ('CRTWasm', legacy_sources, dirs['legacy']),
                                       ('CRTSystems', system_sources, dirs['systems'])]:
        for source in sources:
            code = uncomment(snapshot.text(source))
            if FORBIDDEN.search(code):
                parser.error('Proof-hole audit failed: ' + str(source))
            audited.extend(declarations(namespace, source, code))
            hashes[str(source.relative_to(root))] = snapshot.digest(source)
            snapshot.stage(source, target / source.name)
    snapshot.stage(root / 'systems/out/main.v', dirs['generated'] / 'main.v')
    snapshot.stage(root / 'out/main.v', dirs['legacy-generated'] / 'main.v')
    flags = ['-w', '-notation-overridden', '-R', '/workspaces/wasm-verifier/_build/default/theories', 'WasmVerifier']
    for folder, namespace in [('math', 'CRT'), ('generated', 'CRTSystemGenerated'),
                              ('legacy-generated', 'CRTGenerated'), ('legacy', 'CRTWasm'), ('systems', 'CRTSystems')]:
        flags += ['-Q', str(dirs[folder]), namespace]

    def run(command, logfile):
        with (out / logfile).open('w') as output:
            result = subprocess.run(command, cwd=out, text=True, stdout=output, stderr=subprocess.STDOUT)
        output = (out / logfile).read_text()
        if result.returncode:
            raise RuntimeError(f'{command[0]} failed; see {out / logfile}\n{output[-6000:]}')
        return output

    for source in [*[dirs['math'] / s.name for s in math_sources],
                   dirs['generated'] / 'main.v', dirs['legacy-generated'] / 'main.v',
                   *[dirs['legacy'] / s.name for s in legacy_sources],
                   *[dirs['systems'] / s.name for s in system_sources]]:
        print('Checking ' + str(source.relative_to(out)), flush=True)
        run(['coqc', *flags, str(source)], source.parent.name + '-' + source.stem + '.log')
    print('Checking fixed execution, realization, and exact contract signatures', flush=True)
    exact, wrappers = exact_checks()
    snapshot.write_staged(out / 'ExactTypes.v', exact.encode())
    run(['coqc', *flags, 'ExactTypes.v'], 'ExactTypes.log')
    audited += ['ExactTypes.' + name for name in wrappers]
    audit = 'Set Printing All.\nSet Printing Width 1000000.\nRequire Import ExactTypes.\n'
    audit += '\n'.join('Require Import CRTSystems.' + name + '.' for name in modules) + '\n'
    audit += '\n'.join('Print Assumptions ' + name + '.' for name in audited) + '\n'
    snapshot.write_staged(out / 'Audit.v', audit.encode())
    print(f'Auditing {len(audited)} handwritten declarations and closed targets', flush=True)
    assumptions = audit_assumptions(run(['coqc', *flags, 'Audit.v'], 'Audit.log'), len(audited), allowed)
    snapshot.write_staged(out / 'RejectedCertificate.v', b'''From Wasm Require Import host.
From WasmVerifier Require Import Verifier.
From CRTSystemGenerated Require main.
Section Host.
Context `{ho : host}.
Theorem false_certificate : ValidModule main.main.
Proof. exact main.valid_main. Qed.
Theorem false_helper_certificate : ValidSpec main.main main.main__HelperContracts_specs.
Proof. exact main.valid_main__HelperContracts. Qed.
Theorem false_public_certificate : ValidSpec main.main main.main__PublicContracts_specs.
Proof. exact main.valid_main__PublicContracts. Qed.
End Host.
Set Printing All.
Set Printing Width 1000000.
Print Assumptions false_certificate.
Print Assumptions false_helper_certificate.
Print Assumptions false_public_certificate.
''')
    rejected = run(['coqc', *flags, 'RejectedCertificate.v'], 'RejectedCertificate.log')
    try:
        audit_assumptions(rejected, 3, allowed)
    except ValueError as error:
        if not all(name in str(error) for name in ('valid_main', 'valid_main__HelperContracts', 'valid_main__PublicContracts')):
            raise
    else:
        raise RuntimeError('Audit accepted generated admitted certificate')
    print('Independent kernel check of ' + target_label + ' proof closure', flush=True)
    run(['coqchk', '-silent', *flags[2:],
         *['CRTSystems.' + name for name in modules], 'ExactTypes', 'Audit'], 'coqchk.log')
    snapshot.verify_unchanged()
    report.write_text(json.dumps({
        **report_metadata,
        'source_contracts': {'helper_assertions': 8, 'public_assertions': 5,
                             'shared_runtime': 'CRTSystems.SystemRuntime.system_initial_runtime'},
        'modules': modules, 'legacy_dependency_modules': legacy,
        'audited_declarations': audited, 'exact_targets': wrappers,
        'transitive_assumptions': assumptions, 'independent_kernel_check': 'passed',
        'generated_admission_negative_control': 'rejected',
        'proof_sources': hashes, 'build_manifests': manifests,
        'assumptions_allowlist_sha256': snapshot.digest(allowfile),
        'checker_dependencies': {str(path.relative_to(root)): snapshot.digest(path) for path in checker_inputs},
        'bound_inputs': snapshot.input_hashes(),
        'staged_sources': {str(path.relative_to(out)): hashlib.sha256(data).hexdigest() for path, data in snapshot.staged.items()},
        'input_and_staged_drift_check': 'passed',
    }, indent=2) + '\n')
    print(f'Checked {len(audited)} declarations and {len(wrappers)} exact {target_label} targets.\n{report}')


