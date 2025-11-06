import { spawn } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import * as Y from 'yjs';

type ClientDoc = {
  readonly doc: Y.Doc;
  readonly text: Y.Text;
};

export type InsertCommand = {
  readonly type: 'insert';
  readonly clientId: number;
  readonly index: number;
  readonly char: string;
};

export type SyncCommand = {
  readonly type: 'sync';
  readonly from: number;
  readonly to: number;
};

export type Command = InsertCommand | SyncCommand;

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
export const repoRoot = path.resolve(__dirname, '../..');
export const leanBinary = path.join(repoRoot, '.lake', 'build', 'bin', 'diff-test-runner');

let buildPromise: Promise<void> | null = null;

export function ensureDiffTestRunnerBuilt(): Promise<void> {
  if (!buildPromise) {
    buildPromise = new Promise((resolve, reject) => {
      const child = spawn('lake', ['build', 'diff-test-runner'], {
        cwd: repoRoot,
        stdio: 'inherit',
      });
      child.on('error', (error) => {
        buildPromise = null;
        reject(error);
      });
      child.on('exit', (code, signal) => {
        if (code === 0) {
          resolve();
        } else {
          buildPromise = null;
          const detail =
            code !== null
              ? `lake build diff-test-runner exited with code ${code}`
              : `lake build diff-test-runner terminated by signal ${signal ?? 'unknown'}`;
          reject(new Error(detail));
        }
      });
    });
  }
  return buildPromise;
}

function ensureDoc(map: Map<number, ClientDoc>, clientId: number): ClientDoc {
  const existing = map.get(clientId);
  if (existing) {
    return existing;
  }
  const doc = new Y.Doc();
  doc.clientID = clientId;
  const text = doc.getText('text');
  const ctx = { doc, text } as const;
  map.set(clientId, ctx);
  return ctx;
}

export function runYjs(commands: readonly Command[]): Record<string, string> {
  const docs = new Map<number, ClientDoc>();
  for (const command of commands) {
    if (command.type === 'insert') {
      const ctx = ensureDoc(docs, command.clientId);
      ctx.text.insert(command.index, command.char);
    } else {
      const fromCtx = ensureDoc(docs, command.from);
      const toCtx = ensureDoc(docs, command.to);
      const stateVector = Y.encodeStateVector(toCtx.doc);
      const update = Y.encodeStateAsUpdate(fromCtx.doc, stateVector);
      if (update.length > 0) {
        Y.applyUpdate(toCtx.doc, update);
      }
    }
  }
  const result: Record<string, string> = {};
  for (const [clientId, { text }] of docs.entries()) {
    result[String(clientId)] = text.toString();
  }
  return result;
}

export async function runLean(commands: readonly Command[]): Promise<Record<string, string>> {
  const ndjson = commands.map((cmd) => JSON.stringify(cmd)).join('\n') + '\n';
  return await new Promise<Record<string, string>>((resolve, reject) => {
    const child = spawn(leanBinary, { cwd: repoRoot, stdio: ['pipe', 'pipe', 'inherit'] });
    if (!child.stdin || !child.stdout) {
      reject(new Error('Failed to spawn Lean process with pipes.'));
      return;
    }
    child.stdin.write(ndjson);
    child.stdin.end();

    let stdout = '';
    child.stdout.setEncoding('utf8');
    child.stdout.on('data', (chunk: string) => {
      stdout += chunk;
    });

    child.on('error', (error) => {
      reject(error);
    });

    child.on('close', (code) => {
      if (code !== 0) {
        reject(new Error(`Lean binary exited with code ${code ?? 'unknown'}`));
        return;
      }
      const trimmed = stdout.trim();
      if (!trimmed) {
        reject(new Error('Lean binary produced no output.'));
        return;
      }
      try {
        const parsed = JSON.parse(trimmed) as Record<string, string>;
        resolve(parsed);
      } catch (error) {
        reject(error);
      }
    });
  });
}

export function normalize(result: Record<string, string>): Record<string, string> {
  const entries = Object.entries(result)
    .map(([key, value]) => {
      const numeric = Number(key);
      return [Number.isNaN(numeric) ? key : numeric.toString(), value] as const;
    })
    .sort(([a], [b]) => Number(a) - Number(b));
  return Object.fromEntries(entries);
}
