// Browser transport only. CRT arithmetic and classification run in the verified Wasm.
export const CAPACITY = 16;
const MIN = -(1n << 63n);
const MAX = (1n << 63n) - 1n;

export class InputError extends Error {
  constructor(message, row, field) {
    super(message);
    this.name = 'InputError';
    this.row = row;
    this.field = field;
  }
}

function word(text, row, field) {
  const label = field === 0 ? 'Remainder' : 'Modulus';
  if (typeof text !== 'string' || !/^[+-]?\d+$/.test(text.trim()) || text.trim().length > 64) {
    throw new InputError(`${label} in row ${row + 1} must be a whole decimal integer.`, row, field);
  }
  const value = BigInt(text.trim());
  if (value < MIN || value > MAX) {
    throw new InputError(`${label} in row ${row + 1} must fit signed 64-bit: −9223372036854775808 to 9223372036854775807.`, row, field);
  }
  return value;
}

export async function createSolver(bytes, expectedSha256) {
  if (typeof expectedSha256 !== 'string' || !/^[a-f0-9]{64}$/i.test(expectedSha256)) {
    throw new Error('The verification evidence is missing a valid Wasm hash.');
  }
  if (!globalThis.crypto?.subtle) throw new Error('Use a modern browser on localhost or HTTPS to verify the solver.');
  const data = bytes instanceof ArrayBuffer ? bytes.slice(0) : new Uint8Array(bytes);
  const digest = await crypto.subtle.digest('SHA-256', data);
  const actual = [...new Uint8Array(digest)].map((v) => v.toString(16).padStart(2, '0')).join('');
  if (actual !== expectedSha256.toLowerCase()) {
    throw new Error('Wasm integrity check failed: this file does not match the verified artifact.');
  }
  const { instance } = await WebAssembly.instantiate(data, {});
  const { memory, crt_system_solve: solve, crt_system_period: period } = instance.exports;
  if (!(memory instanceof WebAssembly.Memory) || memory.buffer.byteLength < 256 ||
      typeof solve !== 'function' || typeof period !== 'function') {
    throw new Error('The artifact does not provide the finite-system solver ABI.');
  }

  return (rows) => {
    if (!Array.isArray(rows) || rows.length > CAPACITY) throw new InputError('Enter at most 16 congruences.');
    const values = rows.map((pair, i) => {
      if (!Array.isArray(pair) || pair.length !== 2) throw new InputError(`Row ${i + 1} needs a remainder and modulus.`, i);
      return pair.map((text, field) => word(text, i, field));
    });
    const view = new DataView(memory.buffer);
    for (let i = 0; i < CAPACITY; i++) {
      view.setBigInt64(i * 8, values[i]?.[0] ?? 0n, true);
      view.setBigInt64(128 + i * 8, values[i]?.[1] ?? 0n, true);
    }
    const x = solve(0, 128, rows.length);
    const p = period(0, 128, rows.length);
    const errors = new Map([[-2n, 'invalid'], [-1n, 'incompatible'], [-3n, 'overflow']]);
    if (errors.has(x) && p === x) return { status: errors.get(x) };
    if (x >= 0n && p > x && p <= MAX) return { status: 'solved', solution: x, period: p };
    throw new Error('The solver returned inconsistent solution and period values.');
  };
}
