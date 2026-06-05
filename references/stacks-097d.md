# Stacks Project tag 097D — Lemma 61.6.2 (`lemma-construct-profinite`)

## Citation
The Stacks Project authors, *The Stacks Project*, chapter "Pro-étale
Cohomology" (`proetale.tex`), Section 61.6 "Identifying local rings
versus ind-Zariski", Lemma 61.6.2. Permalink:
<https://stacks.math.columbia.edu/tag/097D>.

## Slug
stacks-097d

## Retrieval status
RETRIEVED — 2026-06-02

## Local source files
- `references/stacks-097d.tex` — verbatim excerpt of `proetale.tex`
  lines 846–1031 (the full lemma group around tag 097D: section
  header + helper Lemma 097C + Lemma 097D + Example 09BJ + the two
  w-local-morphism lemmas + Proposition 097G that consumes 097D).
  Retrieved from
  <https://raw.githubusercontent.com/stacks/stacks-project/master/proetale.tex>.

The whole `proetale.tex` chapter source (6463 lines) is upstream at
the same URL — fetch it on demand if more context is needed. We did
not vendor the full chapter to avoid bloating `references/`.

## Why this source
The dispatcher's strategy table attributes a particular framing
("Profinite Pullback for W-local rings; pullback of a profinite
extension to a profinite cover lifts to a weakly étale extension")
to tag 097D. The blueprint file `local-structure.tex` instead cites
097D for "modifying $\pi_0$ of $\Spec(A)$ to match a given profinite
space, via an ind-Zariski colimit construction". This excerpt settles
which framing matches the actual Stacks tag, so the plan agent can
decide whether the "Stacks 097D sub-phase (i) profinite infra" /
"sub-phase (iv) WLocal wrapper" rows of the strategy table need
re-routing.

## Contents map
The excerpt at `references/stacks-097d.tex` covers (numbering matches
Stacks tags / rendered numbering at
<https://stacks.math.columbia.edu/tag/0965>, chapter 61):

- §61.6 "Identifying local rings versus ind-Zariski" (tag 097B) —
  section header + motivation paragraph; introduces $\pi_0(\Spec(A))$
  as a profinite space.
- Lemma 61.6.1 (tag 097C, label `lemma-construct`) — for $T \subset
  \pi_0(X)$ closed, build surjective ind-Zariski $A \to B$ whose
  $\Spec$ is the preimage of $T$.
- **Lemma 61.6.2 (tag 097D, label `lemma-construct-profinite`)** —
  **the target tag**. Given a continuous map from a profinite space
  $T$ to $\pi_0(\Spec(A))$, produces an ind-Zariski $A \to B$
  realising the cartesian-over-$\pi_0$ pullback with
  $\pi_0(\Spec(B)) = T$. Proof: write $T = \lim T_i$ as a profinite
  limit, build $B_i$ via 097C applied to $A_i = \prod_{t \in T_i} A$,
  set $B = \colim B_i$.
- Example 61.6.3 (tag 09BJ, label `example-construct-space`) — the
  field case: any profinite $T$ is homeomorphic to $\Spec$ of an
  ind-Zariski $k$-algebra (apply 097D with $X = \Spec(k)$).
- Lemma 61.6.4 (tag 097E, label
  `lemma-w-local-morphism-equal-points-stalks-is-iso`) — w-local
  morphisms identifying both local rings and $\pi_0$ are
  isomorphisms.
- Lemma 61.6.5 (tag 097F, label
  `lemma-w-local-morphism-equal-stalks-is-ind-zariski`) — w-local
  morphisms identifying local rings are ind-Zariski; this is the
  immediate consumer of 097D.
- Proposition 61.6.6 (tag 097G, label
  `proposition-maps-wich-identify-local-rings`) — every ring map
  identifying local rings becomes ind-Zariski after a faithfully flat
  ind-Zariski extension; assembled from 097F + `lemma-make-w-local`.

Cross-references that 097D itself cites (for tracing): tag 08ZY
(`topology-lemma-profinite`, writing profinite spaces as limits of
finite discrete spaces), tag 096L
(`lemma-local-isomorphism-fully-faithful`), tag 096T
(`lemma-ind-zariski-implies`), tag 096C (`lemma-silly`, identifying
$\pi_0$ of the limit).

Per the Stacks "statistics" page for tag 097D, four downstream tags
refer to 097D: 097F and 097G in the same section above, and two more
later in the chapter (see
<https://stacks.math.columbia.edu/tag/097D/statistics#dependencies>
for the live list — not vendored).

## Caveats
- Stacks tag identifiers are stable but the printed lemma/section
  numbers (61.6.2 etc.) can shift if the chapter is reorganised.
  Always cite by tag, not by number.
- The Stacks Project does not publish per-tag PDFs; the canonical
  source is the LaTeX file. No PDF was downloaded.
- The verbatim TeX excerpt uses Stacks-internal macros (`\Spec`,
  `\colim`, `\Im`, `\xymatrix`) that are defined in the project's
  preamble (`stacks-project-preamble.tex`); the excerpt is not
  standalone-compilable but is faithful to the source.
- The strategy table's framing of 097D as "weakly étale extension"
  does **not** match this tag: 097D produces an **ind-Zariski**
  extension (surjective on $\Spec$, identifies local rings), not a
  weakly étale one. The blueprint's `local-structure.tex` framing
  matches; the strategy-table framing does not.

## Quality / provenance
The Stacks Project is the definitive open reference for this area of
algebraic geometry and its tag system is the canonical citation
mechanism. The TeX excerpt comes from the master branch of the
project's official GitHub repository
(`stacks/stacks-project`); the rendered HTML (used to confirm the
section/chapter/numbering) is the project's own website. Confidence
that this is the authoritative version: maximal.
