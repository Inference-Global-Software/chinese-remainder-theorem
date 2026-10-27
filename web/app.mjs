import { createSolver, CAPACITY, InputError } from './solver.mjs';

const $ = (selector) => document.querySelector(selector);
const checkIcon = '<svg class="inline-icon" viewBox="0 0 16 16" aria-hidden="true"><path d="m3 8 3 3 7-7"/></svg>';
const presets = {
  shared: { rows: [['2', '6'], ['5', '9'], ['8', '15']], description: 'The moduli share factors. A common solution still exists.' },
  classic: { rows: [['2', '3'], ['3', '5'], ['2', '7']], description: 'Pairwise coprime moduli: the classic Chinese Remainder Theorem.' },
  incompatible: { rows: [['2', '6'], ['4', '9']], description: 'These remainders disagree modulo a shared factor. No integer satisfies both.' },
  overflow: { rows: [['0', '3037000500'], ['0', '3037000501']], description: 'Zero is a solution, but the complete solution class has a period beyond i64.' },
  precedence: { rows: [['0', '3037000500'], ['0', '3037000501'], ['1', '2']], description: 'An overflowing prefix meets a contradiction. Incompatibility takes priority.' },
};
let rows = presets.shared.rows.map((pair) => [...pair]);
let solve;

function announce(message) { $('#announcement').textContent = message; }
function clearInputErrors() {
  for (const input of document.querySelectorAll('#rows input')) input.removeAttribute('aria-invalid');
}
function clearPreset() {
  for (const button of document.querySelectorAll('[data-example]')) button.setAttribute('aria-pressed', 'false');
  $('#example-description').textContent = 'Your system. Change the inputs and solve to explore.';
}
function renderRows() {
  $('#rows').replaceChildren();
  rows.forEach((pair, i) => {
    const row = document.createElement('div'); row.className = 'congruence-row';
    row.innerHTML = '<span class="row-symbol" aria-hidden="true">x <span>≡</span></span>';
    pair.forEach((value, field) => {
      const wrap = document.createElement('div'); wrap.className = `input-wrap${field === 1 ? ' modulus' : ''}`;
      if (field === 1) {
        const hint = document.createElement('span'); hint.className = 'mod-label'; hint.textContent = 'mod'; hint.setAttribute('aria-hidden', 'true'); wrap.append(hint);
      }
      const input = document.createElement('input');
      input.type = 'text'; input.inputMode = 'numeric'; input.autocomplete = 'off'; input.spellcheck = false;
      input.value = value; input.maxLength = 64; input.dataset.row = i; input.dataset.field = field;
      input.setAttribute('aria-label', `${field === 0 ? 'Remainder' : 'Modulus'} ${i + 1}`);
      wrap.append(input); row.append(wrap);
    });
    const remove = document.createElement('button'); remove.type = 'button'; remove.className = 'remove-row';
    remove.setAttribute('aria-label', `Remove congruence ${i + 1}`); remove.title = `Remove congruence ${i + 1}`;
    remove.textContent = '×'; remove.dataset.remove = i; row.append(remove); $('#rows').append(row);
  });
  $('#row-count').textContent = `${rows.length} / ${CAPACITY}`;
  $('#add-row').disabled = rows.length >= CAPACITY;
  $('#reverse').disabled = rows.length < 2;
  $('#empty-note').hidden = rows.length !== 0;
}

function message(status, title, description, badge, footnote = '') {
  const result = $('#result'); result.dataset.status = status;
  result.classList.remove('wide-result');
  result.innerHTML = '<div class="result-top"><h2 class="result-heading"><span class="step">02</span> The result</h2><span class="outcome-badge"></span></div><h3 class="status-title"></h3><p class="status-description"></p><p class="status-footnote"></p>';
  result.querySelector('.outcome-badge').textContent = badge;
  result.querySelector('.status-title').textContent = title;
  result.querySelector('.status-description').textContent = description;
  result.querySelector('.status-footnote').textContent = footnote;
  $('#answer-checks').hidden = true;
  announce(`${title} ${description}`);
}
function dirty() {
  clearInputErrors(); clearPreset();
  if (solve) message('dirty', 'A new possibility.', 'Your congruences have changed. Solve the system to see their common answer.', 'INPUTS CHANGED');
}

function showSolved({ solution: x, period: p }) {
  const result = $('#result'); result.dataset.status = 'solved';
  result.classList.toggle('wide-result', x.toString().length > 11 || p.toString().length > 11);
  // x and p come only from signed Wasm results, never from HTML entered by a user.
  result.innerHTML = `<div class="result-top"><h2 class="result-heading"><span class="step">02</span> The result</h2><span class="outcome-badge">${checkIcon} SOLUTION FOUND</span></div>
    <div class="result-equation" aria-label="All integer solutions"><span class="variable">x = </span><span class="solution">${x}</span><span class="operator"> + </span><span class="factor">${p}<i>k</i></span></div>
    <p class="solution-note">${rows.length ? 'One answer, infinitely many solutions.' : 'No constraints. Every integer is a solution.'} For any integer <i>k</i>.</p>
    <div class="result-metrics"><div><div class="metric-label">SMALLEST NONNEGATIVE</div><div class="metric-value" id="solution-value">${x}</div></div><div><div class="metric-label">REPEAT PERIOD</div><div class="metric-value" id="period-value">${p}</div></div></div>
    <div class="result-bottom"><span>Same system. Any order. Same result.</span><button type="button" class="copy-button" id="copy-result">Copy solution</button></div>`;
  $('#copy-result').addEventListener('click', async (event) => {
    const button = event.currentTarget;
    try { await navigator.clipboard.writeText(`x = ${x} + ${p}k, for every integer k`); button.textContent = 'Copied'; announce('Solution copied.'); }
    catch { button.textContent = 'Copy unavailable'; announce('Clipboard access is unavailable. Select the solution text to copy it.'); }
  });
  const checks = $('#answer-checks'); checks.hidden = false;
  checks.innerHTML = '<h3>Check the answer</h3><ul class="checks"></ul><div class="sample-heading"><span>THE SOLUTIONS KEEP GOING</span><span>Equal steps of the period</span></div><div class="samples" id="samples"></div>';
  for (const [a, m] of rows) {
    const li = document.createElement('li');
    const equation = document.createElement('span'); equation.textContent = `${x} mod ${BigInt(m)} = ${x % BigInt(m)}`;
    const check = document.createElement('span'); check.className = 'check-pass'; check.innerHTML = checkIcon; check.append(` ${BigInt(a)}`);
    li.append(equation, check); checks.querySelector('ul').append(li);
  }
  if (!rows.length) checks.querySelector('h3').textContent = 'The empty system has period 1';
  for (let k = 0n; k < 4n; k++) {
    const sample = document.createElement('div'); sample.className = 'sample'; sample.textContent = (x + p * k).toString();
    const index = document.createElement('small'); index.textContent = `k = ${k}`; sample.append(index); $('#samples').append(sample);
  }
  announce(`Solution ${x}, period ${p}. All integer solutions are ${x} plus ${p} times k.`);
}

function run() {
  if (!solve) return;
  clearInputErrors();
  try {
    const result = solve(rows);
    if (result.status === 'solved') showSolved(result);
    else if (result.status === 'incompatible') message('incompatible', 'No common answer.', 'These congruences cannot all hold for the same integer. At least two disagree modulo a shared factor.', 'INCOMPATIBLE', 'Changing the input order will not change this result.');
    else if (result.status === 'overflow') message('overflow', 'The period is too large.', 'A mathematical solution exists, but its full repeat period exceeds 9,223,372,036,854,775,807. The solver reports overflow instead of wrapping the answer.', 'OVERFLOW', 'A small solution can still have a period too large to represent.');
    else {
      let explanation = 'Use positive moduli and normalized remainders: 0 ≤ a < m.';
      rows.forEach(([a, m], i) => {
        const field = BigInt(m) <= 0n ? 1 : (BigInt(a) < 0n || BigInt(a) >= BigInt(m) ? 0 : null);
        if (field !== null) {
          $(`input[data-row="${i}"][data-field="${field}"]`).setAttribute('aria-invalid', 'true');
          explanation += ` Row ${i + 1}: ${field === 1 ? 'the modulus must be positive.' : 'the remainder must be between 0 and modulus − 1.'}`;
        }
      });
      message('invalid', 'Check your congruences.', explanation, 'INVALID INPUT');
    }
  } catch (error) {
    if (error instanceof InputError) {
      message('invalid', 'Check your congruences.', error.message, 'INVALID INPUT');
      const input = $(`input[data-row="${error.row}"][data-field="${error.field}"]`);
      if (input) { input.setAttribute('aria-invalid', 'true'); input.focus(); }
    } else message('error', 'The solver could not run.', error.message, 'EXECUTION ERROR', 'Reload the page to try loading the artifact again.');
  }
}

$('#system-form').addEventListener('submit', (event) => { event.preventDefault(); run(); });
$('#rows').addEventListener('input', (event) => {
  if (!event.target.matches('input')) return;
  rows[Number(event.target.dataset.row)][Number(event.target.dataset.field)] = event.target.value;
  dirty();
});
$('#rows').addEventListener('click', (event) => {
  const button = event.target.closest('[data-remove]'); if (!button) return;
  const i = Number(button.dataset.remove); rows.splice(i, 1); renderRows(); dirty();
  const next = $(`input[data-row="${Math.min(i, rows.length - 1)}"][data-field="0"]`);
  (next || $('#add-row')).focus();
});
$('#add-row').addEventListener('click', () => {
  if (rows.length >= CAPACITY) return;
  rows.push(['0', '1']); renderRows(); dirty();
  $(`input[data-row="${rows.length - 1}"][data-field="0"]`).focus();
});
$('#clear').addEventListener('click', () => { rows = []; renderRows(); clearPreset(); run(); });
$('#reverse').addEventListener('click', () => { rows.reverse(); renderRows(); run(); });
$('#examples').addEventListener('click', (event) => {
  const button = event.target.closest('[data-example]'); if (!button) return;
  const preset = presets[button.dataset.example]; rows = preset.rows.map((pair) => [...pair]);
  renderRows(); clearPreset(); button.setAttribute('aria-pressed', 'true');
  $('#example-description').textContent = preset.description; run();
});

renderRows();
try {
  const [wasm, record] = await Promise.all([fetch('/solver.wasm'), fetch('/evidence.json')]);
  if (!wasm.ok || !record.ok) throw new Error('Could not load the solver artifact or its verification evidence. Check the local server, then reload.');
  const evidence = await record.json();
  solve = await createSolver(await wasm.arrayBuffer(), evidence.build_manifests?.systems?.artifacts?.['main.wasm']);
  $('#engine-status').textContent = 'Verified Wasm ready'; $('#engine-dot').classList.add('ready');
  $('#solve').disabled = false; run();
} catch (error) {
  $('#engine-status').textContent = 'Solver unavailable'; $('#engine-dot').classList.add('failed');
  message('error', 'Unable to load the solver.', error.message, 'LOAD ERROR', 'Start with node web/serve.mjs and reload this page.');
}
