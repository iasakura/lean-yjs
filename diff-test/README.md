# lean-yjs differential tests

## Overview
- Differential test suite that verifies lean-yjs matches the behavior of the upstream yjs.
- Running `pnpm test` executes the checks and compares the results of both implementations.

## Test details
- Uses `fast-check` to generate scenarios where multiple replicas perform random operations.
- After synchronizing the replicas, the suite asserts that the final states produced by lean-yjs and yjs agree.

## How to run
```bash
pnpm install
pnpm test
```
