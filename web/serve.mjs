#!/usr/bin/env node
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { join, resolve } from 'node:path';
import { createSolver } from './solver.mjs';

const defaultRoot = fileURLToPath(new URL('../', import.meta.url));
const routes = new Map([
  ['/', ['web/index.html', 'text/html; charset=utf-8']],
  ['/app.mjs', ['web/app.mjs', 'text/javascript; charset=utf-8']],
  ['/proofs.mjs', ['web/proofs.mjs', 'text/javascript; charset=utf-8']],
  ['/proof-data.json', ['web/proof-data.json', 'application/json; charset=utf-8']],
  ['/solver.mjs', ['web/solver.mjs', 'text/javascript; charset=utf-8']],
  ['/styles.css', ['web/styles.css', 'text/css; charset=utf-8']],
  ['/source.inf', ['systems/src/main.inf', 'text/plain; charset=utf-8']],
  ['/proofs.md', ['proofs/systems/README.md', 'text/plain; charset=utf-8']],
]);

export async function startServer({ root = defaultRoot, port = 4173 } = {}) {
  if (!Number.isInteger(port) || port < 0 || port > 65535) throw new Error('Port must be an integer from 0 to 65535.');
  let wasm;
  try { wasm = await readFile(join(root, 'systems/out/main.wasm')); }
  catch (error) {
    if (error.code === 'ENOENT') throw new Error('Build the solver first: cd systems && infs build');
    throw error;
  }
  const evidenceBytes = await readFile(join(root, 'docs/evidence/finite-system.json'));
  const evidence = JSON.parse(evidenceBytes);
  await createSolver(wasm, evidence.build_manifests?.systems?.artifacts?.['main.wasm']);
  const server = createServer(async (req, res) => {
    res.setHeader('Cache-Control', 'no-store');
    res.setHeader('X-Content-Type-Options', 'nosniff');
    res.setHeader('Content-Security-Policy', "default-src 'self'; script-src 'self' 'wasm-unsafe-eval'; style-src 'self'; img-src 'self' data:; connect-src 'self'; object-src 'none'; base-uri 'none'; frame-ancestors 'none'");
    if (req.method !== 'GET' && req.method !== 'HEAD') {
      res.writeHead(405, { Allow: 'GET, HEAD' }).end('Method not allowed'); return;
    }
    try {
      const path = new URL(req.url, 'http://127.0.0.1').pathname;
      let body, mime;
      if (path === '/solver.wasm') { body = wasm; mime = 'application/wasm'; }
      else if (path === '/evidence.json') { body = evidenceBytes; mime = 'application/json'; }
      else {
        const route = routes.get(path);
        if (!route) { res.writeHead(404).end('Not found'); return; }
        body = await readFile(join(root, route[0])); mime = route[1];
      }
      res.writeHead(200, { 'Content-Type': mime, 'Content-Length': body.length });
      res.end(req.method === 'HEAD' ? undefined : body);
    } catch (error) {
      res.writeHead(error.code === 'ENOENT' ? 404 : 500).end('Unable to load demo asset.');
    }
  });
  await new Promise((accept, reject) => {
    server.once('error', reject);
    server.listen(port, '127.0.0.1', accept);
  });
  return server;
}

if (process.argv[1] && pathToFileURL(resolve(process.argv[1])).href === import.meta.url) {
  try {
    const args = process.argv.slice(2);
    if (args.length && (args.length !== 2 || args[0] !== '--port' || !/^\d+$/.test(args[1]))) {
      throw new Error('Usage: node web/serve.mjs [--port 4173]');
    }
    const server = await startServer({ port: args.length ? Number(args[1]) : 4173 });
    console.log(`CRT demo: http://127.0.0.1:${server.address().port}`);
    console.log('Verified Wasm artifact matched. Press Ctrl+C to stop.');
    for (const signal of ['SIGINT', 'SIGTERM']) process.once(signal, () => server.close());
  } catch (error) {
    console.error(error.message); process.exitCode = 1;
  }
}
