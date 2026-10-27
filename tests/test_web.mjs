import assert from 'node:assert/strict';
import { test } from 'node:test';
import { readFile, mkdtemp, mkdir, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createSolver, InputError } from '../web/solver.mjs';
import { startServer } from '../web/serve.mjs';

const root = new URL('../', import.meta.url);
const bytes = await readFile(new URL('systems/out/main.wasm', root));
const evidence = JSON.parse(await readFile(new URL('docs/evidence/finite-system.json', root)));
const hash = evidence.build_manifests.systems.artifacts['main.wasm'];
const solve = await createSolver(bytes, hash);
const shared = [['2', '6'], ['5', '9'], ['8', '15']];

test('actual batch exports return the complete shared-factor class', () => {
  assert.deepEqual(solve(shared), { status: 'solved', solution: 68n, period: 90n });
  assert.deepEqual(solve([...shared].reverse()), solve(shared));
});
test('word transport retains integers above Number precision', () => {
  assert.deepEqual(solve([['9223372036854775806', '9223372036854775807']]),
    { status: 'solved', solution: 9223372036854775806n, period: 9223372036854775807n });
});
test('classifies incompatibility, overflow and precedence using Wasm', () => {
  assert.deepEqual(solve([['2', '6'], ['4', '9']]), { status: 'incompatible' });
  const large = [['0', '3037000500'], ['0', '3037000501']];
  assert.deepEqual(solve(large), { status: 'overflow' });
  assert.deepEqual(solve([...large, ['1', '2']]), { status: 'incompatible' });
  assert.deepEqual(solve([...large, ['1', '0']]), { status: 'invalid' });
});
test('semantic validation stays distinct from malformed transport', () => {
  for (const pair of [['-1', '3'], ['3', '3'], ['0', '-1'], ['0', '0']]) {
    assert.deepEqual(solve([pair]), { status: 'invalid' });
  }
  for (const value of ['', '1.5', '1e3', '0x10', '9223372036854775808', '-9223372036854775809']) {
    assert.throws(() => solve([[value, '7']]), InputError);
  }
  assert.deepEqual(solve([[' +2 ', ' 3 ']]), { status: 'solved', solution: 2n, period: 3n });
});
test('empty, maximum capacity and repeated calls have no stale array contents', () => {
  assert.deepEqual(solve(Array.from({ length: 16 }, () => ['2', '3'])),
    { status: 'solved', solution: 2n, period: 3n });
  assert.deepEqual(solve([]), { status: 'solved', solution: 0n, period: 1n });
  assert.deepEqual(solve([['0', '1']]), { status: 'solved', solution: 0n, period: 1n });
  assert.throws(() => solve(Array.from({ length: 17 }, () => ['0', '1'])), InputError);
  assert.deepEqual(solve(shared), { status: 'solved', solution: 68n, period: 90n });
});
test('rejects a changed artifact before instantiation', async () => {
  const changed = Buffer.from(bytes); changed[changed.length - 1] ^= 1;
  await assert.rejects(createSolver(changed, hash), /match.*verified|integrity/i);
  await assert.rejects(createSolver(bytes, 'bad'), /hash|evidence/i);
});

async function fixture(t, content = bytes) {
  const dir = await mkdtemp(join(tmpdir(), 'crt-web-test-'));
  t.after(() => rm(dir, { recursive: true, force: true }));
  for (const name of ['web', 'systems/out', 'docs/evidence']) await mkdir(join(dir, name), { recursive: true });
  await writeFile(join(dir, 'web/index.html'), '<title>CRT fixture</title>');
  await writeFile(join(dir, 'systems/out/main.wasm'), content);
  await writeFile(join(dir, 'docs/evidence/finite-system.json'), JSON.stringify(evidence));
  return dir;
}
test('local server exposes named assets, correct Wasm MIME and no arbitrary repo files', async (t) => {
  const dir = await fixture(t);
  const server = await startServer({ root: dir, port: 0 });
  t.after(() => new Promise((resolve) => server.close(resolve)));
  const base = `http://127.0.0.1:${server.address().port}`;
  const home = await fetch(base);
  assert.equal(home.status, 200);
  assert.match(await home.text(), /CRT fixture/);
  const wasm = await fetch(`${base}/solver.wasm`);
  assert.equal(wasm.headers.get('content-type'), 'application/wasm');
  assert.deepEqual(Buffer.from(await wasm.arrayBuffer()), bytes);
  assert.match(wasm.headers.get('content-security-policy'), /wasm-unsafe-eval/);
  assert.equal((await fetch(`${base}/.git/config`)).status, 404);
  assert.equal((await fetch(`${base}/%2e%2e/.git/config`)).status, 404);
  assert.equal((await fetch(`${base}/systems/src/main.inf`)).status, 404);
  assert.equal((await fetch(base, { method: 'POST' })).status, 405);
});
test('server refuses missing or changed artifacts with actionable startup errors', async (t) => {
  const dir = await fixture(t, Buffer.from('wrong artifact'));
  await assert.rejects(startServer({ root: dir, port: 0 }), /match.*verified|integrity/i);
  await rm(join(dir, 'systems/out/main.wasm'));
  await assert.rejects(startServer({ root: dir, port: 0 }), /infs build/i);
});
