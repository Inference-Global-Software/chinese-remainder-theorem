#!/usr/bin/env node
// Finite CRT CLI: exact signed-i64 decimal transport, capacity 16.
// The source ABI requires two complete readable 128-byte array regions.
// We marshal all 16 slots at offsets 0 and 128 in exported Wasm memory.
// Raw forged pointers are outside this interface; inactive slots are ignored.
import { readFile } from 'node:fs/promises';

const args = process.argv.slice(2);
const json = args[0] === '--json';
if (json) args.shift();
const MIN = -(1n << 63n);
const MAX = (1n << 63n) - 1n;

function emit(payload, code) {
  if (json) console.log(JSON.stringify(payload));
  else if (payload.status === 'solved') {
    console.log(`First coincidence: ${payload.solution}`);
    console.log(`Repeat period: ${payload.period}`);
    console.log(`All integer solutions: ${payload.solution} + ${payload.period} * k`);
  } else if (payload.status === 'incompatible') {
    console.log('No solution: the schedules never coincide.');
  } else if (payload.status === 'overflow') {
    console.log('The solution class period exceeds the signed 64-bit limit.');
  } else console.error(payload.message);
  process.exitCode = code;
}

try {
  if (args.length % 2 !== 0 || args.length > 32) {
    throw new RangeError('Usage: node systems/scripts/demo.mjs [--json] [a m ...] (at most 16 pairs)');
  }
  const values = args.map((arg) => {
    if (!/^[+-]?\d+$/.test(arg)) throw new RangeError('Arguments must be decimal integers.');
    const value = BigInt(arg);
    if (value < MIN || value > MAX) throw new RangeError('Arguments must fit signed 64-bit integers.');
    return value;
  });
  const bytes = await readFile(new URL('../out/main.wasm', import.meta.url));
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const { memory } = instance.exports;
  if (!(memory instanceof WebAssembly.Memory) || memory.buffer.byteLength < 256) {
    throw new Error('Artifact does not provide the complete array ABI memory.');
  }
  const view = new DataView(memory.buffer);
  for (let i = 0; i < 16; i++) {
    view.setBigInt64(i * 8, values[i * 2] ?? 0n, true);
    view.setBigInt64(128 + i * 8, values[i * 2 + 1] ?? 0n, true);
  }
  const count = values.length / 2;
  const x = instance.exports.crt_system_solve(0, 128, count);
  if (x === -2n) {
    emit({ status: 'invalid', message: 'Require positive moduli and normalized residues 0 <= a < m.' }, 2);
  } else if (x === -1n) emit({ status: 'incompatible' }, 1);
  else if (x === -3n) emit({ status: 'overflow' }, 3);
  else if (x >= 0n) {
    const period = instance.exports.crt_system_period(0, 128, count);
    if (period < 1n) throw new Error('Inconsistent solve/period results.');
    emit({ status: 'solved', solution: x.toString(), period: period.toString() }, 0);
  } else throw new Error('Unknown solver result.');
} catch (error) {
  if (error instanceof RangeError) emit({ status: 'invalid', message: error.message }, 2);
  else emit({ status: 'error', message: error.code === 'ENOENT'
    ? 'Build the Wasm artifact first: cd systems && infs build'
    : error.message }, 3);
}
