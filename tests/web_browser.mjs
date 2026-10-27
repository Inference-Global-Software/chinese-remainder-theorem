// Optional browser QA: point PLAYWRIGHT_MODULE at an installed playwright-core module.
import assert from 'node:assert/strict';
import { test, before, after } from 'node:test';
import { mkdir } from 'node:fs/promises';
import { startServer } from '../web/serve.mjs';

const { chromium } = await import(process.env.PLAYWRIGHT_MODULE || 'playwright-core');
let server, browser, base;
before(async () => {
  server = await startServer({ port: 0 });
  base = `http://127.0.0.1:${server.address().port}`;
  browser = await chromium.launch({ executablePath: process.env.CHROME_PATH, headless: true });
});
after(async () => {
  await browser?.close();
  if (server) await new Promise((resolve) => server.close(resolve));
});
async function pageFor(t, options = {}) {
  const page = await browser.newPage(options);
  t.after(() => page.close());
  page.setDefaultTimeout(5000);
  await page.goto(base);
  await page.locator('#engine-status').filter({ hasText: 'Verified Wasm ready' }).waitFor();
  return page;
}
async function status(page, value) {
  await page.locator(`#result[data-status="${value}"]`).waitFor();
}

test('default result is actual 68/90 and presets expose distinct outcomes', async (t) => {
  const page = await pageFor(t);
  await status(page, 'solved');
  assert.equal(await page.locator('#solution-value').textContent(), '68');
  assert.equal(await page.locator('#period-value').textContent(), '90');
  assert.equal(await page.locator('.check-pass').count(), 3);
  for (const [name, outcome] of [['Classic', 'solved'], ['No solution', 'incompatible'], ['Overflow', 'overflow'], ['Conflict wins', 'incompatible']]) {
    await page.getByRole('button', { name, exact: true }).click();
    await status(page, outcome);
    if (name === 'Classic') assert.equal(await page.locator('#solution-value').textContent(), '23');
  }
});
test('editing invalidates old answers; Enter solves and format errors identify an input', async (t) => {
  const page = await pageFor(t);
  await page.getByLabel('Remainder 1', { exact: true }).fill('1.5');
  await status(page, 'dirty');
  assert.equal(await page.locator('#solution-value').count(), 0);
  await page.getByLabel('Remainder 1', { exact: true }).press('Enter');
  await status(page, 'invalid');
  assert.equal(await page.getByLabel('Remainder 1', { exact: true }).getAttribute('aria-invalid'), 'true');
  await page.getByLabel('Remainder 1', { exact: true }).fill('2');
  await page.getByLabel('Remainder 1', { exact: true }).press('Enter');
  await status(page, 'solved');
});
test('clear, add, remove, reverse and capacity controls preserve semantics', async (t) => {
  const page = await pageFor(t);
  await page.getByRole('button', { name: 'Reverse order', exact: true }).click();
  assert.equal(await page.locator('#solution-value').textContent(), '68');
  assert.equal(await page.getByLabel('Remainder 1', { exact: true }).inputValue(), '8');
  await page.getByRole('button', { name: 'Clear all', exact: true }).click();
  await status(page, 'solved');
  assert.equal(await page.locator('#solution-value').textContent(), '0');
  assert.equal(await page.locator('#period-value').textContent(), '1');
  for (let i = 0; i < 16; i++) await page.getByRole('button', { name: 'Add congruence', exact: true }).click();
  assert.equal(await page.getByRole('button', { name: 'Add congruence', exact: true }).isDisabled(), true);
  assert.equal(await page.locator('.congruence-row').count(), 16);
  await page.getByRole('button', { name: 'Remove congruence 16', exact: true }).click();
  assert.equal(await page.locator('.congruence-row').count(), 15);
  assert.equal(await page.getByRole('button', { name: 'Add congruence', exact: true }).isEnabled(), true);
});
test('full-width values remain exact in inputs, answer, checks and samples', async (t) => {
  const page = await pageFor(t);
  await page.getByRole('button', { name: 'Clear all', exact: true }).click();
  await page.getByRole('button', { name: 'Add congruence', exact: true }).click();
  await page.getByLabel('Remainder 1', { exact: true }).fill('9223372036854775806');
  await page.getByLabel('Modulus 1', { exact: true }).fill('9223372036854775807');
  await page.getByRole('button', { name: 'Solve system', exact: true }).click();
  await status(page, 'solved');
  assert.equal(await page.locator('#solution-value').textContent(), '9223372036854775806');
  assert.equal(await page.locator('#period-value').textContent(), '9223372036854775807');
  assert.match(await page.locator('#samples').textContent(), /18446744073709551613/);
  assert.equal(await page.locator('.check-pass').count(), 1);
  await page.getByLabel('Modulus 1', { exact: true }).fill('9223372036854775808');
  await page.getByRole('button', { name: 'Solve system', exact: true }).click();
  await status(page, 'invalid');
});
test('semantic invalidity and a deleted final row are visible outcomes', async (t) => {
  const page = await pageFor(t);
  await page.getByRole('button', { name: 'Clear all', exact: true }).click();
  await page.getByRole('button', { name: 'Add congruence', exact: true }).click();
  await page.getByLabel('Modulus 1', { exact: true }).fill('0');
  await page.getByRole('button', { name: 'Solve system', exact: true }).click();
  await status(page, 'invalid');
  await page.getByRole('button', { name: 'Remove congruence 1', exact: true }).click();
  await page.getByRole('button', { name: 'Solve system', exact: true }).click();
  await status(page, 'solved');
  assert.equal(await page.locator('#period-value').textContent(), '1');
});
test('artifact load failure disables solving and has a recoverable explanation', async (t) => {
  const page = await browser.newPage(); t.after(() => page.close());
  await page.route('**/solver.wasm', (route) => route.fulfill({ status: 404, body: 'missing' }));
  await page.goto(base);
  await status(page, 'error');
  assert.equal(await page.getByRole('button', { name: 'Solve system', exact: true }).isDisabled(), true);
  assert.match(await page.locator('#result').textContent(), /load|reload|artifact/i);
});
test('artifact tampering cannot enable browser solving', async (t) => {
  const page = await browser.newPage(); t.after(() => page.close());
  await page.route('**/solver.wasm', (route) => route.fulfill({ status: 200, body: 'tampered' }));
  await page.goto(base);
  await status(page, 'error');
  assert.match(await page.locator('#result').textContent(), /integrity|verified artifact/i);
  assert.equal(await page.getByRole('button', { name: 'Solve system', exact: true }).isDisabled(), true);
});
test('copy solution writes the exact current solution family', async (t) => {
  const page = await pageFor(t);
  await page.context().grantPermissions(['clipboard-read', 'clipboard-write'], { origin: base });
  await page.getByRole('button', { name: 'Copy solution', exact: true }).click();
  await page.getByRole('button', { name: 'Copied', exact: true }).waitFor();
  assert.equal(await page.evaluate(() => navigator.clipboard.readText()), 'x = 68 + 90k, for every integer k');
});
test('mobile full-width inputs and answers fit the viewport; desktop has no JS errors', async (t) => {
  const page = await pageFor(t, { viewport: { width: 390, height: 844 } });
  const errors = []; page.on('pageerror', (error) => errors.push(error.message));
  await page.getByRole('button', { name: 'Clear all', exact: true }).click();
  await page.getByRole('button', { name: 'Add congruence', exact: true }).click();
  await page.getByLabel('Remainder 1', { exact: true }).fill('9223372036854775806');
  await page.getByLabel('Modulus 1', { exact: true }).fill('9223372036854775807');
  await page.getByRole('button', { name: 'Solve system', exact: true }).click();
  await status(page, 'solved');
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), true);
  await mkdir('build/web-demo', { recursive: true });
  await page.screenshot({ path: 'build/web-demo/mobile.png', fullPage: true });
  await page.setViewportSize({ width: 1440, height: 1050 });
  await page.getByRole('button', { name: 'Shared factors', exact: true }).click();
  await page.screenshot({ path: 'build/web-demo/desktop.png', fullPage: true });
  assert.deepEqual(errors, []);
});
