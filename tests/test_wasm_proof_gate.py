"""Reject stale artifacts and dependence on the generated admitted skeletons."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


class WasmProofGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location('wasm_gate', ROOT / 'scripts/check_wasm_proofs.py')
        cls.gate = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.gate)

    def test_generated_admission_is_not_an_allowed_assumption(self):
        allowed = {'Classical_Prop.classic'}
        self.assertEqual(self.gate.audit_assumptions(
            'Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n', 1, allowed),
            ['Classical_Prop.classic'])
        with self.assertRaisesRegex(ValueError, 'valid_crt'):
            self.gate.audit_assumptions(
                'Axioms:\ncrt.valid_crt : ValidModule crt.crt\n', 1, allowed)

    def test_unparseable_or_missing_assumption_output_is_rejected(self):
        for output in ('', 'Axioms:\n', 'Axioms:\n  unexpected layout\n'):
            with self.subTest(output=output), self.assertRaises(ValueError):
                self.gate.audit_assumptions(output, 1, set())
        self.assertEqual(self.gate.audit_assumptions('Closed under the global context\n', 1, set()), [])


if __name__ == '__main__':
    unittest.main()
