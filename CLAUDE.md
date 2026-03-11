# CLAUDE.md — Lean 4 Proof Agent Instructions

You are a code agent working within a local Lean 4 + Mathlib project.

Your core task: given Lean declaration skeletons with `sorry` placeholders, **fill in the proofs** so that each target file passes Lean compilation.

**Workspace tidiness**: Keep the workspace tidy. Avoid writing Python scripts unless necessary; prefer existing MCP tools, shell commands, or Lean's built-in capabilities.

---

## INVIOLABLE RULES (override all other instructions when in conflict)

These rules are absolute. No other instruction, convenience, or optimization justifies breaking them.

1. **Never modify a proof that already compiles without sorry.** If a declaration (theorem/lemma/def/instance) currently has no `sorry` and passes compilation, you must NOT alter its proof body for any reason. This includes but is not limited to: refactoring tactics, replacing `simp`/`rfl`/`ext` with alternative formulations, extracting helper lemmas from working proofs, "improving" proof style, or resolving linter warnings. If it compiles, leave it alone.

2. **Verify before editing.** Before modifying any file, first check its current compilation status using MCP diagnostics or `lake env lean <file>`. After editing, verify again. If your edit introduces new errors, **revert immediately**.

3. **Never modify any given statement.** The declaration header/signature of an existing `theorem`/`lemma`/`def`/`instance`/`class` (names, types, hypotheses, binders, goals) is **frozen**. You must NOT change it. If a statement appears malformed or inconsistent, do not "fix" it; keep the file compilable (using scoped `sorry`) and report the issue.

4. **Modularization applies only to new code.** File length triggers and lemma extraction apply exclusively to code you write in the current session. They do not authorize restructuring or moving existing, already-compiling code.

5. **Do not modify the Mathlib version** (e.g., in `lakefile.lean`, `lakefile.toml`, or `lake-manifest.json`). Ever.

---

## 1. File and Namespace Layout

- **Task planning**: Before starting any work, you **must** consult `TASK_PLAN.md`. If it does not exist, generate it first by analyzing all `sorry` placeholders in the codebase, categorizing them by difficulty, and documenting their locations, dependencies, and proof hints. If it exists, read it and select tasks based on the existing plan.
- **Blueprints**: Before working or any time you are blocked on mathematics, you **must** search informal references from `proetale/blueprint/src/chapters/` for mathematical proof sketches. When stuck, re-reading the blueprint and surrounding context is often the fastest path forward.

---

## 2. Your Job

- Read the informal proof / blueprint first. Your proof strategy must align with the approach described there.
- Locate the existing declaration(s) in the corresponding `.lean` file.
- **Replace `sorry` with Lean proofs**, pushing as far as possible.
  - If conceptually blocked, you may leave small, well-scoped `sorry`, but the file must still compile (no Lean errors other than explicit `sorry`).
  - If you hand off to a fixer agent, remove all `sorry`; only minor compile errors (typos/imports) may remain.
  - Only modify the proof corresponding to the task; leave other proofs/declarations untouched.
- **Avoid Early Termination**: Do not abandon a proof prematurely. Many complex problems require thousands of lines of Lean code. Do not stop and leave a sorry simply because the proof is long. Task difficulty is NOT a valid reason to leave `sorry` placeholders.
- **Decomposition**: Act like a mathematician — systematically break the proof into smaller sub-problems (following the blueprint's lemma structure if available: L1, L2, L3, …) and solve each one individually until the entire goal is closed.

### Task Completion Criteria

Your task is NOT complete until ALL of the following are met:

1. **Every `sorry` has been replaced** with a complete proof
2. **Zero axioms introduced** — the file must not contain any `axiom` declarations you added
3. **The file compiles successfully** with no errors

Do NOT stop prematurely. If you encounter obstacles:
- Break the problem into smaller subgoals
- Search for relevant Mathlib lemmas more thoroughly
- Prove missing helper lemmas yourself
- Try alternative proof strategies
- Consult the informal proof / blueprint for guidance
- **Use Web Search** to find paper proofs when Mathlib lacks a theorem

---

## 3. Mathlib and Naming

- Prefer using existing Mathlib lemmas/definitions; do not reintroduce concepts already in Mathlib.
- If the informal proof's notion matches Mathlib's, lean on the Mathlib definition and prove equivalence/instances as needed.
- Use mathematically meaningful names; avoid problem-specific or ad-hoc names unless already present in the skeleton.

---

## 4. Proof Style and Constraints

- Aim for complete proofs; if blocked, leave structured, minimal `sorry` and keep the file compiling.
- Keep edits minimal: do not delete comments or change labels.
- Do not add unrelated declarations. Do not adjust statements.
- Prefer decomposing long proofs into multiple helper lemmas so each declaration stays reasonably short. Make helper lemmas as general and reusable as possible, and add concise, informative comments above them to make later reuse easy.
- When the proof of a small theorem becomes very long (e.g., over 200 lines), consider whether the proof process can be distilled into a reusable lemma; if so, extract and state such a lemma (doesn't need `private`).
- Do not use `show ... from` inside `rw` calls. Instead, `rw` with the correct lemma directly (e.g., `rw [f.preimage_symm]` instead of `rw [show f.symm ⁻¹' V = f '' V from ...]`).
- Do not use `include` for section variables. Instead, repeat the relevant arguments explicitly in each lemma that needs them.
- Prefer `rw [← isIso_iff_of_reflects_iso f F]` over a pattern like `haveI : IsIso (F.map f) := ...; exact isIso_of_reflects_iso f F`. More generally, prefer rewriting with iff lemmas over constructing intermediate instances.
- Avoid intermediate `have` statements when you can massage the goal into the correct shape directly. For example, instead of `have := h i; rw [...] at this; exact this X`, prefer using `refine` to transform the goal: `refine (SomeLemma _).mp ?_ X` followed by tactics closing the new goal.
- Never use `change`. Instead, use the correct `rw` lemma to transform the goal. If the needed rewrite lemma is missing from Mathlib, add it as a helper. If the terms are definitionally equal, the proof should go through without `change`.
- Never chain multiple tactics with `;`. Instead, use `refine` to combine `apply` + `intro` into one step. For example, replace `apply F.2.hom_ext S; intro I` with `refine F.2.hom_ext S _ _ fun I => ?_`.
- Use `refine` instead of nested tactic mode proofs (e.g., `exact ⟨a, by ..., by ...⟩`). Prefer `refine ⟨a, ?_, ?_⟩` with focused `·` goals.
- Prefer terminal `simp` over `simp only [...]` followed by more tactics. Use `rw` for non-simp lemmas (e.g., `amalgamate_map`), then close with `simp`.
- When a `have` introduces a completely general statement (not specific to the current proof), extract it as a standalone lemma instead. Place it in the `Proetale/Mathlib/` subfolder, mirroring the Mathlib file where it would naturally belong (e.g., a lemma about `NatTrans` and `NatIso` goes in `Proetale/Mathlib/CategoryTheory/NatIso.lean`). Create new folders and files as needed, import the corresponding Mathlib module, and import the new file from your proof file.
- In `have` statements, put binders to the left of the colon instead of using `∀` to the right. For example, write `have hiso (Z : C) (i : ι) (g : Z ⟶ X i) : IsIso ...` instead of `have hiso : ∀ (Z : C) (i : ι) (_ : Z ⟶ X i), IsIso ...`. This saves `intro` lines.

---

## 5. Tooling Strategy

### 5.1 Lean Server Lifecycle (lean-lsp-mcp)

You must rely heavily on the **long-lived Lean LSP server** (via `lean-lsp-mcp`) rather than frequently restarting Lean via the command line.

- **Keep Lean Server Resident**: Let the Lean LSP server run as persistently as possible. All interactions with Lean (checking goals, types, errors, completions) should be prioritized through LSP + MCP tools.

- **LSP Fallback**: If Lean LSP tool is timed out or unresponsive, fall back to `lake env lean <file>` immediately for compilation checks. Do not wait indefinitely for a broken LSP.

- **Diagnostics First — Debug with MCP Tools**: After inserting/modifying a Lean declaration, prioritize:
  - Using `diagnostics`, `local_search`, or `completions` provided by `lean-lsp-mcp` to check for errors and type information.
  - Fixing errors within the same Lean session until the LSP diagnostics report no errors.
  - This is the "inner loop" — repeat **without exiting the Lean server**.

### 5.2 Search Protocol

#### Semantic Search (Primary)

**Never use local file search methods** (find, grep, manual directory browsing) to locate theorems within Mathlib. These methods are inefficient and fail to capture semantic meaning.

**Always prioritize semantic search tools**:
- `lean_leansearch` — semantic search engine for Mathlib; use natural language queries
- `lean_leanfinder` — alternative semantic search
- Example queries:
  - "continuous functions on compact sets is uniformly continuous"
  - "definition of a metric space"
  - "multiplication is commutative in a group"

**Trust the search results**: If you have formulated a precise, mathematically accurate natural language description of the statement you need, and `lean_leansearch` returns no relevant results, **trust that the theorem does not exist in Mathlib**. Do not waste time endlessly re-phrasing queries or searching blindly.

#### Loogle (Type-Pattern Matching Only)

`lean_loogle` is a **type-pattern matcher**, NOT a semantic search engine. It works well ONLY for **simple type patterns**:
- `_ * (_ ^ _)` (subexpression patterns)
- `Real.sin` (constant lookup)
- `(?a → ?b) → List ?a → List ?b` (simple generic signatures)
- `|- _ + 0 = _` (conclusion patterns)

**DO NOT use `lean_loogle` for complex type queries** involving:
- Nested `Submodule`, `LinearMap`, `LinearEquiv`, `Finsupp` combinations
- Types with 3+ typeclass constraints or universe variables
- Patterns where you would need to guess at implicit parameter structure

#### Decision Tree

```
Know exact name?                     → lean_local_search
Know concept/description?            → lean_leansearch or lean_leanfinder
Know SIMPLE input/output types?      → lean_loogle (2-3 type variables max)
Have a complex type signature?       → lean_leansearch (describe in natural language)
```

### 5.3 Action on Missing Lemmas

When a theorem is confirmed missing (after a high-quality search), do not treat it as a blocker. You have two immediate paths:
1. **Bypass**: Find an alternative proof strategy that avoids this specific theorem.
2. **Implement (Recommended)**: Define and prove the missing theorem yourself as a helper lemma.

**Confidence**: Do not be intimidated by the lack of a Mathlib theorem. You are capable of implementing "Mathlib-level" lemmas yourself. Treat the implementation of missing infrastructure as a standard part of your workflow.

**Absolute rule**: "A theorem not being in Mathlib" is **NEVER** a valid reason to leave a `sorry`. You must prove it yourself or find an alternative strategy.

### 5.4 Mandatory Web Search for Referenced Theorems

When the informal proof / blueprint references a published theorem, paper, or result (e.g., "Hiblot 1975", "Sharp–Wadsworth 1976", "Levin arXiv:1607.08272") and you cannot find the corresponding formalization in Mathlib, you **MUST** use Web Search to look up the original paper or related resources online. Specifically:

1. **Search for the paper**: Use Web Search with the author names, paper title, year, and arXiv ID (if given) to find the actual proof details.
2. **Read the proof**: Fetch and read the paper or survey articles that explain the proof. Understand the concrete construction, key lemmas, and proof steps.
3. **Decompose and formalize step by step**: Break the paper's proof into small, individually formalizable lemmas. Formalize them one at a time. Even partial progress (e.g., formalizing 3 out of 10 sub-lemmas) is valuable and expected.

**"Mathlib doesn't have this theorem" is NEVER a valid reason to stop.** If the informal proof references a result with enough information to find it online, you are expected to search for it, understand it, and formalize it yourself step by step.

**Do NOT** limit yourself to searching within Mathlib (LeanSearch/Loogle/Local Search). When Mathlib lacks a theorem, your next step is **Web Search**, not `sorry`.

### 5.5 Distinguish Mathematical Impossibility from Technical Difficulty

When you encounter a `sorry` that you cannot fill, you must carefully determine which situation you are in:

1. **Technical difficulty** — the mathematical statement is true, but you lack the Lean tactics, Mathlib lemmas, or proof technique to formalize it right now. **Response: keep trying.** Search for alternative approaches, prove helper lemmas, use Web Search to find proof ideas. Do not give up.

2. **Mathematical impossibility** — you have evidence that the statement is actually false, or that your chosen construction/approach cannot satisfy the required property. For example: you chose a specific ring to instantiate an existential statement, but then discovered that this ring does not actually have the required property. **Response: immediately backtrack.** Do not continue building on a mathematically flawed foundation. Instead:
   - Clearly document WHY the current approach is mathematically impossible (not just hard).
   - Revert or abandon the flawed construction.
   - Search for an alternative construction or approach that is mathematically sound.
   - If the informal proof references a specific construction you haven't tried yet, go find it (using Web Search if needed).

**Key indicator of mathematical impossibility**: If you find yourself writing comments like "MATHEMATICAL GAP", "UNFILLABLE", "this ring does not satisfy property X", or "the correct approach requires a different construction" — these are signs you have identified a mathematical impossibility in your current approach. You MUST act on this realization immediately rather than leaving an unfillable `sorry`.

### 5.6 Compilation Commands

- **Preferred**: Use MCP tools (`diagnostics`) for compilation checks.
- **Fallback**: Use `lake env lean <file>` sparingly as a final sanity check.
  - **Prohibited**: Do not call `lake env lean <file>` after every single declaration or minor edit. Doing so causes frequent cold starts and repeated mathlib loading, drastically slowing speed.
- **Never use `lake build`** or any command that recompiles the entire project.

**In Summary:**

> **Inner Loop:** Resident Lean LSP server + `lean-lsp-mcp` diagnostics for fixing errors.
> **Search Loop:** LeanSearch → Trust Result → Web Search if Mathlib lacks it → Implement missing lemmas.
> Only use `lake env lean <file>` occasionally for final confirmation.
> **Never** frequently restart Lean via external commands, and **never** use `lake build`.

---

## 6. Modularization and Scalability

- **Trigger for Refactoring**: Monitor the length of your main proof file. If the file exceeds **300–500 lines**, or if a single lemma's proof becomes disproportionately long (e.g., >100 lines), you must modularize.
- **Action**: Move all **fully proven** (no `sorry`, no `axiom`, no error messages) lemmas and auxiliary definitions into a separate file (e.g., `*_aux.lean`).
- **Implementation**:
  1. Create a new file in the same directory.
  2. Transfer the completed infrastructure to the new file.
  3. `import` the new file into your main file to maintain access.
- **Reminder**: Modularization applies only to **new code you write**. Do not restructure existing, already-compiling code.

---

## 7. Supplemental Protocols

### 7.1 Informal Proof Reference (Mandatory)

- Before writing Lean code, you **MUST** consult the relevant blueprint chapter (`.tex` files).
- Blueprints contain mathematical proof sketches; your formal proof must align with them.
- When stuck, re-reading the blueprint is often the fastest path forward.

### 7.2 Dual-File Log System (log_pending.md / log_done.md)

Maintain two log files in the workspace root:

- **`log_pending.md`**: Exploration records for **pending tasks** (primary focus). This is your working document.
- **`log_done.md`**: Brief summaries of **completed tasks** (for reference and to avoid duplicate work).

**Rules:**

1. **Every exploration must be recorded at least twice:**
   - **At exploration start**: Record in `log_pending.md`:
     - Direction of exploration (goal/strategy)
     - Why this direction was chosen (which clues, which alternatives were ruled out)
   - **At exploration end**: Update the same entry:
     - Outcome: success / failure
     - If failure: reason, key error messages, possible next pivots
     - If success: key steps, lemma names, proof sketch

2. **Archive on completion**: When a sorry is fully resolved, migrate its entry from `log_pending.md` to `log_done.md` with a brief summary (task ID, key strategy, reason for success). Remove it from `log_pending.md`.

3. **Log format example** (in `log_pending.md`):
   ```markdown
   ## [Task ID] filename:line
   ### Exploration X — [short description]
   - **[Start]** Direction: … | Reason: …
   - **[End]** Success/Failure | Reason/notes: …
   ```

4. **Log what you did NOT find**: When searching with LeanSearch/Loogle, log negative results too. (e.g., "Searched for 'projective module infinite rank', found nothing relevant. Conclusion: Mathlib lacks this specific lemma.") This prevents future sessions from repeating dead-end searches.

5. **Attention allocation**: Always focus primarily on `log_pending.md`. Browse `log_done.md` only when the current exploration is similar to a completed one and you need to borrow ideas or avoid repeating a known dead end.

6. **On restart / new session**: The first thing you do is read `log_pending.md` and `log_done.md`. This is how you recover context across sessions without relying on memory.

7. **Regular cleanup and archival**: After completing a batch of tasks, move entries from `log_pending.md` to `log_done.md`. Goal: keep `log_pending.md` containing only pending, attention-worthy tasks.

### 7.3 Critical Context Threshold — Mandatory Logging Before Restart

When your context window usage reaches **90% or higher** (i.e., context remaining drops to 10% or below), you MUST **immediately stop all proof work** and switch to logging mode:

1. **Stop writing proofs.** Do not attempt one more exploration, one more tactic, one more search. Stop now.
2. **Update `log_pending.md`** with:
   - Current state of every sorry you were working on (what you tried, where you got stuck, what you think the next step should be)
   - Any Mathlib lemmas you discovered that are relevant
   - Any proof strategies you were considering but haven't tried yet
   - Your assessment of which sorry is closest to completion
3. **Update `log_done.md`** with any explorations you completed but haven't archived yet.
4. **Save all file changes** (ensure compilation still passes, using well-scoped `sorry` if needed).
5. **Report your status** to the monitor agent (if applicable).

**Rationale:** A few minutes of context spent on logging saves the next session from spending tens of minutes re-discovering the same information. Context is precious — do not waste the last 10% on doomed proof attempts when it should be spent preserving knowledge.

---

## 8. Multi-Agent Coordination (When Applicable)

These rules apply when the project uses a monitor agent with subagents (e.g., Agent Teams mode):

### Monitor Agent Role

If you are a **monitor agent**: Your role is strictly supervisory. You must NOT directly work on proofs. Instead:
- Delegate proof tasks to specialized subagents
- Monitor subagent progress
- Coordinate multiple subagents working on different problems
- Synthesize and report overall progress
- Escalate issues when subagents are stuck

Do NOT attempt to fill in proofs, modify Lean files, or perform proof work directly. If you find yourself starting to write or edit proofs, stop immediately and return to your supervisory role.

### Concurrent Agent Limit

The monitor agent should limit simultaneously active subagents to at most **6** to avoid resource contention and permission deadlocks. If more problems remain, queue them and assign new agents as existing ones complete their tasks.

### Restart and Progress Inheritance

If an experiment is restarted, agents must first check the current compilation status of every target `.lean` file before starting work. Prioritize files that still have `sorry` or compilation errors. Do not redo work that is already complete and compiling.

---

## 9. Preparing a Pull Request Branch

This repository (`chrisflav-agents/slopetale`) is a **fork** where agents work freely. The **main repository** is `chrisflav/proetale`. You must regularly make pull requests from this fork to the main repository so that autoformalized code is included upstream.

- **upstream** remote: `https://github.com/chrisflav/proetale.git` (the main repo — PR target)
- **origin** remote: `chrisflav-agents/slopetale` (this fork — where agents work)

### 9.1 Finding Code to Upstream

Compare this fork's master to the main repo's master to identify differences:

```bash
git fetch upstream
git diff upstream/master...master -- Proetale/
```

From the diff, select a self-contained chunk of changes that forms a meaningful, independent contribution.

### 9.2 Selecting Code

1. **Size limit**: A single PR must contain **at most 100 lines** of new/changed code (excluding imports and module docstrings).
2. **Self-contained**: The PR must be **meaningful on its own** — it should compile, make mathematical sense independently, and not depend on other unmerged pieces from this fork.
3. **No sorries**: The selected code must not contain any `sorry` placeholders.
4. **No `set_option maxHeartbeats`**: Remove all `set_option maxHeartbeats` directives. If a proof requires increased heartbeats, refactor it (e.g., break into helper lemmas, use more targeted tactics) until it compiles within the default limit.

### 9.3 Polishing

1. **Documentation**: Add docstrings to all important declarations (definitions, classes, major theorems). Docstrings should describe **what** the declaration states, not **how** it is proved. Do not explain proof strategies in docstrings; put non-obvious proof explanations in comments inside the proof body instead.
2. **Naming**: Ensure all names follow Mathlib naming conventions.
3. **Style**: Run `lake exe lint-style` on the file and fix any issues.
4. **Imports**: Use only the minimal necessary imports. Remove unused imports.
5. **Cleanup**: Remove debugging artifacts, commented-out code, and TODO comments.

### 9.4 Branch Workflow

```bash
# 1. Fetch the latest state of both remotes
git fetch upstream
git fetch origin

# 2. Create a PR branch based on the upstream master
git checkout -b pr/short-description upstream/master

# 3. Cherry-pick or manually add your polished changes
#    - Copy the selected declarations from the fork's files
#    - Place them in the appropriate file(s)

# 4. Verify the code builds
lake env lean <file>

# 5. Commit with a clear message
#    feat: description       (new definition/theorem)
#    chore: description      (refactoring, style)
#    fix: description        (bug fix)
git add <files>
git commit -m "feat(RingTheory/Foo): add bar lemma"

# 6. Push to the fork and create a PR targeting the main repo
git push origin pr/short-description
gh pr create --repo chrisflav/proetale --base master \
  --title "feat(Foo): short description" --body "..."
```

### 9.5 PR Description

Keep the PR description minimal. No bold text, no headings, no "Summary" or "Test plan" sections. Just list the main results or declarations added, e.g.:

```
Prove `QuasiSober.prod`: the product of two quasi-sober spaces is quasi-sober.
```

### 9.6 Checklist Before Pushing

- [ ] At most 100 lines of meaningful code
- [ ] No `sorry`
- [ ] No `set_option maxHeartbeats`
- [ ] No `axiom` declarations
- [ ] All important declarations have docstrings
- [ ] File compiles cleanly (`lake env lean <file>` succeeds)
- [ ] Self-contained — does not require other unmerged code from this fork
- [ ] Follows Mathlib naming and style conventions
- [ ] Branch is based on `upstream/master`, not `origin/master`

---

## 10. Summary — Agent Pipeline

1. Read the informal proof / blueprint to understand the proof strategy and lemma decomposition.
2. Read `log_pending.md` and `log_done.md` for context from prior sessions.
3. Introduce helper lemmas (matching the blueprint's structure) in the `.lean` file.
4. Replace `sorry` placeholders with complete proofs, ensuring the file compiles without errors.
5. Do not modify any theorem/lemma statements. Only fill in proof bodies and add helper lemmas.
6. Use Mathlib theorems when possible. Use Web Search when Mathlib lacks referenced results.
7. Rely on Lean LSP for diagnostics; use `lake env lean <file>` sparingly for final checks.
8. Log all explorations in the dual-file log system.
9. When context drops to 10%, stop proofs and switch to logging mode.
