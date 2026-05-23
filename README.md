# Slopetale

<!-- archon:readme -->
<!-- Claude fills in the prose sections below. Keep the section headers. -->

## Project

A (work-in-progress) Lean 4 formalization of pro-étale cohomology following
Bhatt–Scholze, *The pro-étale topology for schemes* ([arXiv:1309.1198](https://arxiv.org/abs/1309.1198)).
The long-term target is Theorem 5.6.2 of BS13, comparing étale and pro-étale
cohomology of varieties with ℓ-adic coefficients. Current scope covers the
commutative-algebra preliminaries (w-contractible / w-local rings, ind-étale
and weakly étale algebras), the pro-étale site of an affine scheme, and the
associated local-structure theorems. The blueprint in `blueprint/` tracks the
informal mathematics; `archon-protected.yaml` lists declarations whose
signatures are owned by the mathematician.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

- `Proetale/` — main Lean source
- `blueprint/` — leanblueprint source (build with `leanblueprint pdf` and `leanblueprint web`)
- `references/` — PDFs, papers, and informal notes backing the formalization
- `archon-protected.yaml` — declarations agents must not modify
- `.archon/` — agent state (not committed)

## How to build

```bash
lake exe cache get   # download Mathlib olean cache
lake build           # compile the project
```

## How to run the formalization loop

```bash
archon loop .
```

This launches the plan → prove → review loop and opens a dashboard.
