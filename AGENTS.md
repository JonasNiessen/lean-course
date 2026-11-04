# AGENTS.md — AI-assisted formalization

Instructions for coding agents (Claude Code, Codex, …) working in this repository.

## Project

- Lean 4 `v4.35.0` + mathlib `v4.35.0` (see `lean-toolchain`, `lakefile.lean`).
- `CourseNotes/` and `Solutions/`: course material. **Do not modify** unless explicitly asked.
- `Formalization/`: our own AI-assisted formalization projects. One file (or subfolder) per project.
  Every new file must be imported in `Formalization.lean`.

## Tools

- **Lean MCP** (`lean-lsp`, configured in `.mcp.json`): prefer it over guessing.
  - `lean_diagnostic_messages` / `lean_goal` / `lean_hover_info` to check the state of a file.
  - `lean_local_search`, `lean_leansearch`, `lean_loogle`, `lean_leanfinder` to find mathlib lemmas.
    **Never invent lemma names**: verify that a lemma exists before using it.
  - `lean_multi_attempt` to try several tactics on one goal.
- **Lean skills** (`lean4` plugin): `/lean4:draft`, `/lean4:prove`, `/lean4:review`, `/lean4:checkpoint`, …
- Fallback without MCP: `lake build` (or `lake env lean <file>`) from the repo root.

## Workflow

The work is split into two phases with different models and different levels of human supervision.

### Phase 1 — Scaffolding (strong model + careful human supervision and review)

Goal: the *statements* are correct. Proofs are not the goal yet.

1. Start from an informal source (paper, lecture notes, textbook). Record it in the module docstring
   (`/-! … -/`): reference, page/section numbers, and the informal statement.
2. Write **definitions and theorem statements**, every proof `sorry`.
   - Break large theorems into intermediate lemmas, each with a `sorry` proof (a "blueprint").
   - Every declaration gets a docstring (`/-- … -/`) with the informal statement and, for lemmas,
     a short proof sketch that the prover in Phase 2 can follow.
   - Reuse mathlib definitions whenever they exist. Do not redefine standard notions.
3. The file must **compile** (only `declaration uses 'sorry'` warnings allowed).
4. **Stop and ask the human to review** the statements. Point out every modelling choice,
   for example: types (`ℕ` vs `ℤ` vs `ℝ`), implicit hypotheses (nonemptiness, positivity, `0 ∉ …`),
   coercions, `Finset` vs `Set`, junk values (`x / 0 = 0`, `Real.sqrt (-1) = 0`, `Nat` subtraction).
5. Once the human approves, mark the statements as frozen (see "Rules") and commit.

Checklist for a statement review:
- [ ] Does the Lean statement say exactly what the informal one says (not weaker, not trivially true)?
- [ ] Are the hypotheses consistent? (A theorem with contradictory hypotheses is vacuously true.)
- [ ] Do junk values or coercions change the meaning?
- [ ] Is a definition used instead of mathlib's existing one?

### Phase 2 — Proof filling (weaker/cheaper model, little supervision needed)

Goal: replace every `sorry` with a proof, **without touching the statements**.

- Work lemma by lemma, bottom-up. Follow the proof sketch in the docstring.
- After each lemma check with the MCP that the file compiles.
- Allowed: adding new *helper* lemmas (with proofs), adding `import`s.
- If a statement looks false or unprovable: **do not change it**. Stop, explain why
  (ideally with a counterexample), and hand it back to Phase 1.
- Done means: `lake build` succeeds with no `sorry`, and `#print axioms <main theorem>`
  shows only `propext`, `Classical.choice`, `Quot.sound`.

## Rules (both phases)

- **Never change the statement of a theorem that has been reviewed and frozen** (marked with
  a `-- STATEMENT FROZEN` comment on the line directly above its docstring) unless the human explicitly asks.
- Forbidden: `axiom`, `admit`, `native_decide`, `implemented_by`, `@[extern]`, `unsafe`,
  `set_option debug.skipKernelTC`, and other tricks that bypass the kernel.
- Do not weaken a statement just to make it provable. Do not add hypotheses silently.
- Keep proofs readable: prefer structured `have`/`calc` over long tactic chains when the proof is long.
- Do not run `lake update` or change the mathlib version.
