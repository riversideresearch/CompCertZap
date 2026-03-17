---
name: rocq-agent-mcp
description: Reference for using rocq-agent via MCP to interactively explore Rocq proofs. Use when working on `.v` files with rocq-agent.
---

# rocq-agent MCP Skill

`rocq-agent` is an MCP server over `rocq-lsp`/`coq-lsp` for interactive proof work. It manages one live LSP/Petanque session, file checking, and proof-state exploration.

## Prerequisites

Build the project before using MCP. The LSP loads dependencies from pre-compiled `.vo` files — it does not compile them from source. If `.vo` files are missing, `Require Import` will fail. Run `make` (or the project's build command) once up front, then use MCP for interactive work.

When editing multiple files, rebuild published `.vo` files with `make` (or the project's build command), then reopen downstream files that depend on them. Do not expect the live LSP session to compile dependency artifacts for you.

## Critical Editing Rule

- For an active/open `.v` file, perform edits only through MCP edit tools: `edit_document`, `replace_range`, `replace_lines`, `insert_before_line`, `insert_after_line`, or `replace_text`. These send LSP `didChange`, keep the live document state synchronized, and write to disk.
- Do not use external filesystem edits (for example `apply_patch`) on an active proof file and then `open_file` again after each change.
- Do not repeatedly reopen the same file after edits. Reopening forces reprocessing from file start and defeats the iterative MCP workflow.
- Reopen a file only when intentionally starting a fresh session, switching files, or recovering from a broken session.

## Quick Start

```
initialize workspaceRoot="/path/to/project"
open_file filePath="src/Proof.v"
get_proof_state uri="file:///..." line=10 character=0 waitUntilReady=true
run_tactic tactic="intros."
run_tactic tactic="apply H."
check_proof_closure
run_query command="Check Nat.add."
```

Most proof and query tools can use the implicit current state during linear exploration. Use `stateId` or `target` when you want to branch, recover after edits, or inspect a different position explicitly.

## Core Tools

### Document

| Tool | Use it for |
|------|------------|
| `initialize` | Start or rebind the workspace and LSP session. Call this first. |
| `open_file` | Open a `.v` file. Returns immediately by default; set `waitForChecking=true` to block for full-file checking. |
| `close_file` | Close an open document and remove it from session tracking. |
| `get_diagnostics` | Re-check document diagnostics after opening or editing a file. Supports `startLine`/`endLine` (1-based inclusive) to filter to a region. |
| `set_view_range` | Restrict checking to a region in a large file. |
| `edit_document` | Replace the full text of an open document via the live LSP session and write it to disk. |
| `replace_range` | Apply a localized edit to an open document via the live LSP session and write it to disk. Range positions are 0-based and end-exclusive. |
| `replace_lines` | Replace whole lines using 1-based inclusive line numbers. |
| `insert_before_line` | Insert text before a 1-based line number. |
| `insert_after_line` | Insert text after a 1-based line number. |
| `replace_text` | Replace an exact text occurrence. Use `requireUnique=true` for safe unique-match edits; use `occurrence=N` when multiple matches exist. |
| `wait_for_position` | Wait until the current document version has been processed up to a target position. |
| `get_current_obligations` | Return a compact obligations summary at the most recently requested proof position for this document. |

The session can track multiple open documents at once. Use `close_file` when you want to remove one and keep implicit context unambiguous.

### Proof Interaction

Most proof and query tools work well with the implicit current state. `stateId` and `target` are mainly for branching, post-edit recovery, or inspecting a specific state/position.

| Tool | Use it for |
|------|------------|
| `get_proof_state` | Inspect the proof state at a source position. Set `waitUntilReady=true` to wait for processing. |
| `run_tactic` | Try one tactic. Uses the current state by default; pass a position `target` after edits. |
| `run_tactics` | Try a short tactic sequence. Same targeting as `run_tactic`. |
| `check_proof_closure` | Check whether the enclosing theorem is closable with `Qed`. |
| `list_goals` | Inspect goals by scope. Returns conclusions only (no hypotheses). |
| `get_goal` | Fetch one goal with full coqc-style text (hypotheses + conclusion). |
| `summarize_goals` | Group large goal sets before drilling down. |
| `save_checkpoint` | Save the current exploration state before branching. |
| `restore_checkpoint` | Return to a saved exploration point. |
| `diff_states` | Compare two states to understand what a tactic changed. |

### Query

| Tool | Use it for |
|------|------------|
| `run_query` | Run `Search`, `Check`, `Print`, `About`, or `Locate` against the current proof context. If there is no active exploration, it can infer context when exactly one tracked proof position or one open document is available. |

## Recommended Workflow

### Default Loop

1. `initialize workspaceRoot="/path/to/project"` once.
2. `open_file` for the file you want to work on (default non-blocking; set `waitForChecking=true` only when you need full-file completion first).
3. `get_proof_state` at the active position with `waitUntilReady=true`.
4. Iterate:
   - **Inspect state first**: Before writing tactics, call `get_proof_state(waitUntilReady=true)` to see exact hypotheses and goals. This is more reliable than predicting state from the proof script.
   - Use `run_tactic` / `run_tactics` for speculative exploration.
   - Edit with MCP edit tools instead of patching the file externally and reopening it. Pass `returnDiagnostics=true` on edits to get error feedback inline without a separate `get_diagnostics` call.
5. After each edit, use a position target on `run_tactic`/`run_tactics` to continue (see "Post-Edit Recovery"), or call `get_proof_state(waitUntilReady=true)` for a fresh `stateId`. Call `check_proof_closure` before assuming the theorem is finished.
6. After writing `Qed.`, verify success with `get_diagnostics` (no errors at the `Qed` line), not `check_proof_closure` (which returns `outside_proof` past `Qed`).

### Post-Edit Recovery

Edit tools invalidate all proof states (`proofStatesCleared: true` in the response). Two patterns for continuing:

**Fastest (edit + check + continue in 2 calls):**
1. Edit with `returnDiagnostics=true` — the edit response includes diagnostics for the edited region, telling you immediately whether the edit introduced errors.
2. If no errors, continue with a position-targeted tactic:
   ```
   run_tactic tactic="intros." target='{"kind":"position","uri":"file:///...","line":10,"character":0,"waitUntilReady":true}'
   ```
   This resolves a fresh state internally — no separate `get_proof_state` call needed.

**Alternative:** Call `get_proof_state(waitUntilReady=true)` at the position to re-inspect hypotheses and goals before deciding the next tactic. This is recommended when you are uncertain about the proof state shape after an edit.

`get_current_obligations` is only safe if the tracked proof position still survives the edit. If you edit directly over the tracked proof sentence, the tool will reject and you should re-run `get_proof_state` near the proof to establish a fresh tracked position.

### Multi-Goal Proofs

Tactics like `split.`, `destruct`, and `induction` generate multiple subgoals. How they appear depends on bullet structure:

- **Without bullets** (pure speculative exploration): all subgoals are **focused**. After solving `focused[0]`, the next auto-advances to `focused[0]`. No goal selection needed.
- **With bullets** (`-`, `+`, `*`, `{}`): the current bullet focuses one subgoal; the rest go to the focus stack and appear as **siblings**. After closing a bullet branch (all focused goals solved), siblings become selectable.

Working with siblings:
- `goal: {scope:"siblings", index:N}` selects a sibling (only works when no focused goals remain).
- If you run a tactic without `goal` and it fails because the focused branch is closed, auto-recovery focuses `siblings[0]` and retries transparently.
- Alternatively, run a bullet tactic (e.g., `- next_tactic.`) to explicitly focus the next branch.

### Inspecting the Current State

After `run_tactic` / `run_tactics`, use these to inspect without running tactics:
- `get_goal index=0 scope="focused"` — full hypotheses + conclusion for one goal
- `list_goals scope="all"` — all conclusions in a scope
- `summarize_goals scope="all"` — group large goal sets before drilling down

### Large Files

For large files, try `set_view_range` before waiting on proof state near the area you care about.

Practical loop:

1. `open_file` (non-blocking, the default).
2. `set_view_range` to the region you plan to inspect.
3. `get_proof_state(waitUntilReady=true)` or `wait_for_position` at the target position.

### Multi-File Rebuilds

When edits cross module boundaries:

1. Edit the dependency module.
2. Rebuild `.vo` files with `make` (or the project's build command).
3. Close and reopen downstream importers before continuing proof work in them.

### Only When Needed

1. `set_view_range` for large files when you want to focus work near one region.
2. `get_current_obligations` for a compact post-edit summary at your last proof position, provided that position was not edited away.
3. `wait_for_position` when you want explicit readiness blocking without pulling full proof state.
4. `run_query` for contextual `Search` / `Check` / `Print` / `About` / `Locate`.
5. `save_checkpoint` and `restore_checkpoint` for branching.

## State Management

Most workflows need little explicit state management — the implicit current state handles linear exploration, and position targets handle post-edit recovery. For **branching** (trying alternative tactics from the same point), use `save_checkpoint` / `restore_checkpoint`.

`stateId` values appear in `get_proof_state` and `run_tactic`/`run_tactics` responses. They are useful for `diff_states` and advanced branching, but you usually do not need to track them for typical proof development.

## Notes

- Edit responses include `editedRange` and `editedLineRange`; use them to drive the next edit without recomputing positions.
- All edit tools accept `returnDiagnostics=true` to wait for checking and return diagnostics for the edited region inline. This eliminates a separate `get_diagnostics` round-trip.
- `replace_text` with `requireUnique=true` errors when the match is not unique — safer than `occurrence` for targeted edits.
- Prefer `safeMode=true` on `replace_range`, `replace_lines`, `insert_before_line`, `insert_after_line`, and `replace_text` unless you intentionally want line concatenation.
