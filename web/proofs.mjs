// The explorer displays recorded proofs; it does not run Rocq or modify the solver.
const root = document.querySelector('#proof-explorer');
const $ = (selector) => root.querySelector(selector);
const tabs = [...root.querySelectorAll('[role="tab"]')];

function selectTab(selected) {
  for (const tab of tabs) {
    const active = tab === selected;
    tab.setAttribute('aria-selected', String(active));
    tab.tabIndex = active ? 0 : -1;
    $(`#${tab.getAttribute('aria-controls')}`).hidden = !active;
  }
}
for (const tab of tabs) {
  tab.addEventListener('click', () => selectTab(tab));
  tab.addEventListener('keydown', (event) => {
    let index = tabs.indexOf(tab);
    if (event.key === 'ArrowRight') index = (index + 1) % tabs.length;
    else if (event.key === 'ArrowLeft') index = (index + tabs.length - 1) % tabs.length;
    else if (event.key === 'Home') index = 0;
    else if (event.key === 'End') index = tabs.length - 1;
    else return;
    event.preventDefault();
    selectTab(tabs[index]); tabs[index].focus();
  });
}

function showTopic(topic) {
  $('#proof-claim').textContent = topic.claim;
  $('#proof-conditions').textContent = topic.conditions;
  $('#proof-key-label').textContent = topic.keyLabel;
  $('#proof-key').textContent = topic.key;
  for (const [kind, panel] of [['statement', 'statement'], ['proof', 'rocq'], ['inference', 'inference']]) {
    const container = $(`#proof-${panel}-panel`); container.replaceChildren();
    for (const part of topic[kind]) {
      const caption = document.createElement('p'); caption.className = 'proof-path';
      caption.textContent = `${part.label} · ${part.path}:${part.start}–${part.end}`;
      const pre = document.createElement('pre'); pre.className = 'proof-code';
      const code = document.createElement('code'); code.textContent = part.text;
      pre.append(code); container.append(caption, pre);
    }
  }
  $('#proof-steps').replaceChildren();
  for (const text of topic.steps) {
    const li = document.createElement('li'); li.textContent = text; $('#proof-steps').append(li);
  }
}

try {
  const response = await fetch('/proof-data.json');
  if (!response.ok) throw new Error('Proof excerpts unavailable.');
  const data = await response.json();
  const { audit } = data;
  $('#proof-math-audit').textContent = `${audit.mathTargets} fixed targets; ${audit.mathAudits} assumption-free audits; independent coqchk passed.`;
  $('#proof-wasm-audit').textContent = `${audit.wasmTargets} fixed targets; ${audit.wasmAudits} declaration/target audits; independent coqchk passed; ${audit.assumptions.length} allowlisted upstream assumptions.`;
  for (const text of audit.assumptions) {
    const li = document.createElement('li'); const code = document.createElement('code');
    code.textContent = text; li.append(code); $('#proof-assumptions').append(li);
  }
  showTopic(data.topics[$('#proof-topic').value]);
  $('#proof-topic').addEventListener('change', () => showTopic(data.topics[$('#proof-topic').value]));
  $('#proof-topic').disabled = false;
  $('#proof-content').hidden = false;
  $('#proof-load-status').hidden = true;
} catch {
  $('#proof-load-status').textContent = 'Unable to load the proof explorer. Reload to try again, or open the proof inventory below. The solver is available independently.';
}
