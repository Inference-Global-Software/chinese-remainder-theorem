// Runs the exact proof-mode artifact. All Wasm i64 transport uses BigInt.
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

const [wasmPath, vectorsPath] = process.argv.slice(2);
const bytes = readFileSync(wasmPath);
assert(WebAssembly.validate(bytes));
const { instance } = await WebAssembly.instantiate(bytes, {});
const vectors = JSON.parse(readFileSync(vectorsPath, 'utf8'));
const counts = {};
for (const { fn, args, expected } of vectors) {
  const actual = instance.exports[fn](...args.map(BigInt));
  assert.equal(actual, BigInt(expected), `${fn}(${args.join(', ')})`);
  counts[fn] = (counts[fn] ?? 0) + 1;
}
console.log(JSON.stringify({ passed: vectors.length, by_function: counts }));
