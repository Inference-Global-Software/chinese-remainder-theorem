"""Full system gate reuses the scalar gate's fail-closed controls."""
import subprocess
import tempfile
from unittest import mock
import test_system_scalar_gate as scalar_tests
import check_system_proofs


class SystemProofGateTests(scalar_tests.ScalarGateTests):
    gate = check_system_proofs
    batch_certified = True
    target_count = 21

    def test_shared_engine_and_batch_target_drift_rejects(self):
        for name in ['scripts/system_proof_engine.py', 'proofs/systems/BatchExecutionTargets.v']:
            with self.subTest(input=name), tempfile.TemporaryDirectory() as directory:
                root, out = self.fixture(directory)
                path = root / name
                def edit():
                    path.write_bytes(path.read_bytes() + b'\nchanged\n')
                with self.mocked_run(root, out, after_kernel=edit):
                    with self.assertRaisesRegex(RuntimeError, 'changed during'):
                        self.gate.main()
                self.assertFalse((out / 'report.json').exists())

    def test_missing_batch_module_invalidates_stale_report(self):
        with tempfile.TemporaryDirectory() as directory:
            root, out = self.fixture(directory)
            (root / 'proofs/systems/BatchExecutionTargets.v').unlink()
            with self.mocked_run(root, out) as calls:
                with self.assertRaises(FileNotFoundError):
                    self.gate.main()
            self.assertEqual(calls, [])
            self.assertFalse((out / 'report.json').exists())

    def test_failed_fixed_target_compilation_invalidates_stale_report(self):
        with tempfile.TemporaryDirectory() as directory:
            root, out = self.fixture(directory)
            with self.mocked_run(root, out):
                original = self.gate.exact_checks
                def wrong_targets():
                    code, names = original()
                    return code.replace('exact BatchExecutionTargets.system_batch_concat',
                                        'exact BatchExecutionTargets.missing_concat_target'), names
                with mock.patch.object(self.gate, 'exact_checks', side_effect=wrong_targets):
                    def compiler(command, **kwargs):
                        kwargs['stdout'].write('fixed signature rejected\n')
                        return subprocess.CompletedProcess(command, int(command[-1] == 'ExactTypes.v'))
                    with mock.patch.object(subprocess, 'run', side_effect=compiler):
                        with self.assertRaisesRegex(RuntimeError, 'coqc failed'):
                            self.gate.main()
            self.assertFalse((out / 'report.json').exists())

    def test_exact_batch_targets_have_memory_premises_and_no_refinement_assumptions(self):
        code, names = self.gate.exact_checks()
        for name in ['system_batch_solve_execution', 'system_batch_period_execution', 'batch_export_bindings',
                     'system_batch_permutation', 'system_batch_success_summary', 'system_batch_composition', 'system_batch_concat']:
            self.assertIn('exact_' + name, names)
        self.assertIn('system_input_memory mem rb mb rs ms -> batch_word32 c', code)
        self.assertNotIn('be_refines ', code)
