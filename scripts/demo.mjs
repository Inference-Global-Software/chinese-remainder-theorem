#!/usr/bin/env node
// Exact decimal transport: no CRT integer is converted to a JavaScript Number.
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
    console.log('No solution: the two schedules never coincide.');
  } else console.error(payload.message);
  process.exitCode = code;
}

try {
  if (args.length !== 4) throw new RangeError('Usage: node scripts/demo.mjs [--json] a m b n');
  const values = args.map((arg) => {
    if (!/^[+-]?\d+$/.test(arg)) throw new RangeError('All four arguments must be decimal integers.');
    const value = BigInt(arg);
    if (value < MIN || value > MAX) throw new RangeError('Arguments must fit signed 64-bit integers.');
    return value;
  });
  const [a, m, b, n] = values;
  const bytes = await readFile(new URL('../build/crt/crt.wasm', import.meta.url));
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const x = instance.exports.crt_solve(a, m, b, n);
  if (x === -2n) {
    emit({ status: 'invalid', message: 'Require 1 <= m,n <= 2147483647, 0 <= a < m, and 0 <= b < n.' }, 2);
  } else {
    const period = instance.exports.crt_period(m, n).toString();
    if (x === -1n) emit({ status: 'incompatible', period }, 1);
    else emit({ status: 'solved', solution: x.toString(), period }, 0);
  }
} catch (error) {
  if (error instanceof RangeError) emit({ status: 'invalid', message: error.message }, 2);
  else emit({ status: 'error', message: error.code === 'ENOENT'
    ? 'Build the Wasm artifact first: make build INFC=/path/to/infc'
    : error.message }, 3);
}
