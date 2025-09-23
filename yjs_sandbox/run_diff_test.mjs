#!/usr/bin/env node
import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import * as Y from 'yjs';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const repoRoot = path.resolve(__dirname, '..');
const leanBinary = path.join(repoRoot, '.lake', 'build', 'bin', 'lean-yjs');

const scenario = [
  { type: 'insert', clientId: 1, index: 0, char: 'H' },
  { type: 'insert', clientId: 1, index: 1, char: 'i' },
  { type: 'insert', clientId: 2, index: 0, char: 'Y' },
  { type: 'insert', clientId: 2, index: 1, char: 'o' },
  { type: 'sync', from: 1, to: 2 },
  { type: 'sync', from: 2, to: 1 },
  { type: 'insert', clientId: 1, index: 1, char: '!' },
  { type: 'sync', from: 1, to: 2 }
];

function ensureDoc(map, clientId) {
  if (!map.has(clientId)) {
    const doc = new Y.Doc();
    doc.clientID = clientId;
    const text = doc.getText('text');
    map.set(clientId, { doc, text });
  }
  return map.get(clientId);
}

function runYjs(commands) {
  const docs = new Map();
  for (const command of commands) {
    if (command.type === 'insert') {
      const ctx = ensureDoc(docs, command.clientId);
      ctx.text.insert(command.index, command.char);
    } else if (command.type === 'sync') {
      const fromCtx = ensureDoc(docs, command.from);
      const toCtx = ensureDoc(docs, command.to);
      const stateVector = Y.encodeStateVector(toCtx.doc);
      const update = Y.encodeStateAsUpdate(fromCtx.doc, stateVector);
      if (update.length > 0) {
        Y.applyUpdate(toCtx.doc, update);
      }
    } else {
      throw new Error(`Unknown command type: ${command.type}`);
    }
  }
  const result = {};
  for (const [clientId, { text }] of docs.entries()) {
    result[clientId] = text.toString();
  }
  return result;
}

async function runLean(commands) {
  const child = spawn(leanBinary, { cwd: repoRoot, stdio: ['pipe', 'pipe', 'inherit'] });
  const ndjson = commands.map((cmd) => JSON.stringify(cmd)).join('\n') + '\n';
  child.stdin.write(ndjson);
  child.stdin.end();
  let stdout = '';
  child.stdout.setEncoding('utf8');
  child.stdout.on('data', (chunk) => {
    stdout += chunk;
  });
  const exitCode = await new Promise((resolve, reject) => {
    child.on('error', reject);
    child.on('close', resolve);
  });
  if (exitCode !== 0) {
    throw new Error(`Lean binary exited with code ${exitCode}`);
  }
  const trimmed = stdout.trim();
  if (!trimmed) {
    throw new Error('Lean binary produced no output');
  }
  return JSON.parse(trimmed);
}

function normalize(result) {
  return Object.fromEntries(
    Object.entries(result).sort(([a], [b]) => Number(a) - Number(b))
  );
}

async function main() {
  const yjsResult = normalize(runYjs(scenario));
  const leanResult = normalize(await runLean(scenario));
  console.log('Yjs result  :', yjsResult);
  console.log('Lean result :', leanResult);
  if (JSON.stringify(yjsResult) !== JSON.stringify(leanResult)) {
    console.error('Results differ!');
    process.exitCode = 1;
  } else {
    console.log('Diff test passed.');
  }
}

main().catch((err) => {
  console.error(err);
  process.exitCode = 1;
});
