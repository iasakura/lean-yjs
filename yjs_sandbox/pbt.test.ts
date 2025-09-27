import fc from "fast-check";
import { describe, test } from "vitest";
import { expect } from "vitest";

import type { Command, InsertCommand, SyncCommand } from "./testUtils";
import { normalize, runLean, runYjs } from "./testUtils";

type RawInsert = {
  readonly kind: "insert";
  readonly clientId: number;
  readonly indexHint: number;
  readonly char: string;
};

type RawSync = {
  readonly kind: "sync";
  readonly from: number;
  readonly to: number;
};

type RawCommand = RawInsert | RawSync;

const rawInsert = fc.record({
  kind: fc.constant<"insert">("insert"),
  clientId: fc.integer({ min: 0, max: 4 }),
  indexHint: fc.integer({ min: 0, max: 64 }),
  char: fc.char(),
});

const rawSync = fc.record({
  kind: fc.constant<"sync">("sync"),
  from: fc.integer({ min: 0, max: 4 }),
  to: fc.integer({ min: 0, max: 4 }),
});

const rawCommandsArb = fc.array(fc.oneof(rawInsert, rawSync), {
  minLength: 1,
  maxLength: 64,
});

function materialize(rawCommands: readonly RawCommand[]): Command[] {
  const lengths = new Map<number, number>();
  const commands: Command[] = [];

  const recordInsert = (command: RawInsert): InsertCommand => {
    const currentLength = lengths.get(command.clientId) ?? 0;
    const index =
      currentLength === 0 ? 0 : command.indexHint % (currentLength + 1);
    lengths.set(command.clientId, currentLength + 1);
    return {
      type: "insert",
      clientId: command.clientId,
      index,
      char: command.char,
    };
  };

  const recordSync = (command: RawSync): SyncCommand | null => {
    if (command.from === command.to) {
      return null;
    }
    // Ensure both documents are tracked even if they have seen no inserts yet.
    if (!lengths.has(command.from)) {
      lengths.set(command.from, 0);
    }
    if (!lengths.has(command.to)) {
      lengths.set(command.to, 0);
    }
    return {
      type: "sync",
      from: command.from,
      to: command.to,
    };
  };

  for (const raw of rawCommands) {
    if (raw.kind === "insert") {
      commands.push(recordInsert(raw));
    } else {
      const syncCommand = recordSync(raw);
      if (syncCommand) {
        commands.push(syncCommand);
      }
    }
  }

  if (commands.length === 0) {
    commands.push({ type: "insert", clientId: 0, index: 0, char: "A" });
  }

  return commands;
}

describe("Lean ↔︎ Yjs property-based diff", () => {
  test("Lean faithfully reproduces Yjs behaviour", async () => {
    const property = fc.asyncProperty(rawCommandsArb, async (rawCommands) => {
      const commands = materialize(rawCommands);
      const yjsResult = normalize(runYjs(commands));
      const leanResult = normalize(await runLean(commands));
      try {
        expect(leanResult).toEqual(yjsResult);
      } catch (error) {
        const detail = [
          "Lean/Yjs mismatch detected.",
          `Commands: ${JSON.stringify(commands, null, 2)}`,
          `Lean result: ${JSON.stringify(leanResult)}`,
          `Yjs result: ${JSON.stringify(yjsResult)}`
        ].join("\n");
        if (error instanceof Error) {
          throw new Error(detail, { cause: error });
        }
        throw new Error(detail);
      }
    });

    await fc.assert(property, {
      verbose: false,
      numRuns: 200,
    });
  });
});
