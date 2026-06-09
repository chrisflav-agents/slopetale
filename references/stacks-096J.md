# Stacks Project tag 096J — Lemma 61.3.6 (`lemma-structure-local-isomorphism`)

## Citation
The Stacks Project authors, *The Stacks Project*, chapter "Pro-étale
Cohomology" (`proetale.tex`), Section 61.3 "Local isomorphisms",
Lemma 61.3.6. Permalink:
<https://stacks.math.columbia.edu/tag/096J>.

## Slug
stacks-096J

## Retrieval status
RETRIEVED — 2026-06-04

## Local source files
- `references/stacks-096J.tex` — verbatim excerpt of `proetale.tex`
  lines 271–401 (the whole of Section 61.3 "Local isomorphisms":
  section header + Definition 096E + Lemmas 096F, 096G, 096H, 096I,
  096J, 096K, 096L with proofs).
  Retrieved from
  <https://raw.githubusercontent.com/stacks/stacks-project/master/proetale.tex>.

We did not separately vendor `sites.tex` (where the unrelated
`u_p h_U = h_{u(U)}` Yoneda lemma at tag 04D2 actually lives — see
"Notes for Dispatcher" below); the dispatcher can re-fetch on demand
if needed.

## Why this source
The blueprint chapter `local-structure.tex` paraphrases, inside its
inverse-direction sketch for `thm:identifies-local-ring-to-top-fully-faithful`
(lines 510–554), the identification "$\mathcal{O}_Y = p^{-1}\mathcal{O}_X$
when $A \to B$ identifies local rings" without an explicit Stacks tag.
The iter-135 blueprint-writer directive asked for the verbatim Stacks
096J text so it could be cited with a `% SOURCE:` / `% SOURCE QUOTE:`
block. **However, tag 096J does not say what the directive claims it
says** (see "Notes for Dispatcher"). This pointer vendors the actual
section so the blueprint-writer (or planner) can pick the correct
neighbouring tag — most likely 096K (`lemma-fully-faithful-spaces-over-X`)
combined with the parenthetical fact stated in the proof of 096L
(`lemma-local-isomorphism-fully-faithful`).

## Contents map
The excerpt at `references/stacks-096J.tex` covers all of Section 61.3
(chapter 61 "Pro-étale Cohomology"), keyed by Stacks tag and the LaTeX
label so a later reader can grep either way. File offsets are relative
to `references/stacks-096J.tex`:

- §61.3 "Local isomorphisms" — file line 16
  (tag 096D, `\label{section-local-isomorphism}`).
- **Definition 61.3.1** (tag 096E,
  `\label{definition-local-isomorphism}`) — file lines 21–32.
  Defines both `local isomorphism` and `identifies local rings` (the
  latter is the property cited throughout the slopetale blueprint).
- **Lemma 61.3.2** (tag 096F,
  `\label{lemma-base-change-local-isomorphism}`) — file lines 37–51.
  Base change preserves both properties. Proof omitted.
- **Lemma 61.3.3** (tag 096G,
  `\label{lemma-composition-local-isomorphism}`) — file lines 53–67.
  Composition preserves both properties. Proof omitted.
- **Lemma 61.3.4** (tag 096H,
  `\label{lemma-local-isomorphism-permanence}`) — file lines 69–82.
  Permanence: if $A \to B, A \to C$ both have the property then
  $B \to C$ does too. Proof omitted.
- **Lemma 61.3.5** (tag 096I,
  `\label{lemma-local-isomorphism-implies}`) — file lines 84–96.
  Local isomorphism ⇒ (étale ∧ identifies local rings ∧ quasi-finite).
  Proof omitted.
- **Lemma 61.3.6 (tag 096J,
  `\label{lemma-structure-local-isomorphism}`)** — **the directive's
  named target tag** — file lines 98–107. **Actual statement (verbatim
  from line 100–102):** "Let $A \to B$ be a local isomorphism. Then
  there exist $n \geq 0$, $g_1, \ldots, g_n \in B$, $f_1, \ldots, f_n
  \in A$ such that $(g_1, \ldots, g_n) = B$ and $A_{f_i} \cong B_{g_i}$."
  Proof omitted. This is a *structure-theoretic* statement about local
  isomorphisms; it has nothing to do with $f^\sharp$ being an
  isomorphism. (See "Notes for Dispatcher".)
- **Lemma 61.3.7** (tag 096K,
  `\label{lemma-fully-faithful-spaces-over-X}`) — file lines 109–128.
  Statement: for $p : (Y,\mathcal{O}_Y) \to (X,\mathcal{O}_X)$,
  $q : (Z,\mathcal{O}_Z) \to (X,\mathcal{O}_X)$ morphisms of locally
  ringed spaces, *if $\mathcal{O}_Y = p^{-1}\mathcal{O}_X$* then
  $\Mor_{\mathrm{LRS}/X}(Z,Y) \to \Mor_{\mathrm{Top}/X}(Z,Y)$
  forgetting $f^\sharp$ is bijective. Proof "immediate from the
  definitions" (one line).
- **Lemma 61.3.8** (tag 096L,
  `\label{lemma-local-isomorphism-fully-faithful}`) — file lines
  130–144. Statement: the functor $B \mapsto \Spec(B)$ from
  ($A$-algebras identifying local rings) to (topological spaces over
  $X = \Spec(A)$) is fully faithful. **Proof body (verbatim, file
  lines 140–143):** "This follows from Lemma
  `lemma-fully-faithful-spaces-over-X` and the fact that *if
  $A \to B$ identifies local rings, then the pullback of the
  structure sheaf of $\Spec(A)$ via $p : \Spec(B) \to \Spec(A)$ is
  equal to the structure sheaf of $\Spec(B)$*." — this parenthetical
  fact is what the blueprint actually wants to cite, and it is **not**
  given a separate Stacks tag (it is asserted, without proof, inside
  the proof of 096L).

## Caveats
- Stacks tag identifiers are stable but the printed lemma/section
  numbers (61.3.6 etc.) can shift if the chapter is reorganised.
  Always cite by tag, not by number.
- The Stacks Project does not publish per-tag PDFs; the canonical
  source is the LaTeX file. No PDF was downloaded.
- The verbatim TeX excerpt uses Stacks-internal macros
  (`\Spec`, `\Mor`) defined in the project's preamble
  (`stacks-project-preamble.tex`); the excerpt is not standalone-
  compilable but is faithful to the source.

## Quality / provenance
The Stacks Project is the definitive open reference for this area of
algebraic geometry and its tag system is the canonical citation
mechanism. The TeX excerpt comes from the master branch of the
project's official GitHub repository (`stacks/stacks-project`); the
rendered HTML at <https://stacks.math.columbia.edu/tag/096J> was used
to confirm the chapter/section/lemma numbering and the chosen line
range. Confidence that this is the authoritative version: maximal.

## Notes for Dispatcher

**Tag mismatch.** The iter-135 directive describes tag 096J as
"Lemma 26.10.1: characterizes when a ring map identifies local rings
in terms of the structure-sheaf comparison map being an isomorphism"
with the candidate statement "$\varphi$ identifies local rings if
and only if $f^\sharp : f^* \mathcal{O}_{\Spec A} \to
\mathcal{O}_{\Spec B}$ is an isomorphism". **None of this matches
the actual Stacks tag 096J.** The real tag 096J:

- Lives in chapter 61 (Pro-étale Cohomology), section 61.3 "Local
  isomorphisms", as Lemma 61.3.6 with label
  `lemma-structure-local-isomorphism` — NOT chapter 26 / §26.10.
- States a *structural decomposition* of a local isomorphism into
  finitely many Zariski-localised isomorphisms; it never mentions
  $f^\sharp$.

The directive also mentions tag 04D2 as a "closely-related variant in
the morphisms-of-schemes chapter". Tag 04D2 is **Lemma 7.5.6 of
`sites.tex`** (chapter 7 "Sites and Sheaves", section "Functoriality
of categories of presheaves"), with statement "for $u : \mathcal{C}
\to \mathcal{D}$ a functor and $U \in \mathcal{C}$, $u_p h_U =
h_{u(U)}$". This is unrelated to schemes or to identifying local
rings, contradicting the directive's framing.

**What the dispatcher likely wants instead.** Reading the blueprint
chapter `local-structure.tex` lines 510–554 alongside the section
above, the fact actually being invoked is:

  If $A \to B$ identifies local rings then, setting $p : \Spec(B)
  \to \Spec(A)$, one has $\mathcal{O}_{\Spec(B)} = p^{-1}
  \mathcal{O}_{\Spec(A)}$.

That fact is **not given its own Stacks tag**. It is stated, without
proof, *inside the proof of Lemma 61.3.8* (tag 096L,
`lemma-local-isomorphism-fully-faithful`). The closest standalone
tagged result is Lemma 61.3.7 (tag 096K,
`lemma-fully-faithful-spaces-over-X`), which assumes
$\mathcal{O}_Y = p^{-1}\mathcal{O}_X$ as a hypothesis and concludes
that the forgetful map $\Mor_{\mathrm{LRS}/X}(Z, Y) \to
\Mor_{\mathrm{Top}/X}(Z, Y)$ is a bijection. So the blueprint-writer
will probably want to cite **096K + the parenthetical inside 096L's
proof**, not "096J".

The verbatim text of both 096K and 096L is included in the vendored
`references/stacks-096J.tex`, so this pointer covers what the
blueprint-writer needs even though the dispatcher's named tag was
misidentified. The slug remains `stacks-096J` to match the directive
name.
