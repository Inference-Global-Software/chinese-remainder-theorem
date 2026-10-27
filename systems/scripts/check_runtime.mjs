// Run independent vectors against the actual proof-mode artifact.
// ABI: complete read-only [i64;16] inputs at byte offsets 0 and 128.
// Decimal strings are checked before any Wasm i64 argument coercion.
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

const MIN = -(1n << 63n);
const MAX = (1n << 63n) - 1n;
function i64(value) {
  assert.equal(typeof value, 'string', 'i64 vector values must be decimal strings');
  assert.match(value, /^[+-]?\d+$/);
  const parsed = BigInt(value);
  assert(parsed >= MIN && parsed <= MAX, 'i64 vector value out of range');
  return parsed;
}

const [wasmPath, vectorsPath] = process.argv.slice(2);
const bytes = readFileSync(wasmPath);
assert(WebAssembly.validate(bytes));
const { instance } = await WebAssembly.instantiate(bytes, {});
const { memory } = instance.exports;
assert(memory instanceof WebAssembly.Memory);
assert(memory.buffer.byteLength >= 256);
const vectors = JSON.parse(readFileSync(vectorsPath, 'utf8'));
const counts = {};
for (const vector of vectors) {
  const { fn, expected } = vector;
  let actual;
  if (fn === 'crt_system_solve' || fn === 'crt_system_period') {
    const { residues, moduli, count } = vector;
    assert(residues.length <= 16 && moduli.length <= 16);
    assert.equal(residues.length, moduli.length);
    assert(Number.isInteger(count) && count >= -(2 ** 31) && count < 2 ** 31);
    assert(count < 0 || count > 16 || count <= residues.length);
    const view = new DataView(memory.buffer);
    for (let i = 0; i < 16; i++) {
      view.setBigInt64(i * 8, i64(residues[i] ?? '0'), true);
      view.setBigInt64(128 + i * 8, i64(moduli[i] ?? '0'), true);
    }
    const before = Buffer.from(memory.buffer.slice(0));
    actual = instance.exports[fn](0, 128, count);
    assert.deepEqual(Buffer.from(memory.buffer), before, `${fn} changed input memory`);
  } else {
    assert(fn === 'crt_merge_solve' || fn === 'crt_merge_period');
    assert.equal(vector.args.length, 4);
    actual = instance.exports[fn](...vector.args.map(i64));
  }
  assert.equal(actual, i64(expected), `${fn}: ${JSON.stringify(vector)}`);
  counts[fn] = (counts[fn] ?? 0) + 1;
}
console.log(JSON.stringify({ passed: vectors.length, by_function: counts }));
