import { beforeAll, describe, expect, test } from "vitest";
import type { Command } from "./testUtils";
import { ensureDiffTestRunnerBuilt, normalize, runLean, runYjs } from "./testUtils";

const scenario: Command[] = [
  { type: "insert", clientId: 1, index: 0, char: "H" },
  { type: "insert", clientId: 1, index: 1, char: "i" },
  { type: "insert", clientId: 2, index: 0, char: "Y" },
  { type: "insert", clientId: 2, index: 1, char: "o" },
  { type: "sync", from: 1, to: 2 },
  { type: "sync", from: 2, to: 1 },
  { type: "insert", clientId: 1, index: 1, char: "!" },
  { type: "sync", from: 1, to: 2 },
];

describe("Lean ↔︎ Yjs diff test", () => {
  beforeAll(async () => {
    await ensureDiffTestRunnerBuilt();
  });

  test("replays the sample scenario identically", async () => {
    const yjsResult = normalize(runYjs(scenario));
    const leanResult = normalize(await runLean(scenario));
    expect(leanResult).toEqual(yjsResult);
  });
});
