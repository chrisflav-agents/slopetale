# Stacks Project tags 04GG, 04GH (+ 04GJ helper); tag 0DXB FLAGGED

## Citation
The Stacks Project authors, *The Stacks Project*, chapter "Algebra"
(`algebra.tex`), Section "Henselian local rings" (label
`section-henselian`, tag 04GE), Lemma `lemma-characterize-henselian`
(tag 04GG, rendered as Lemma 10.155.3 on master) and Lemma
`lemma-finite-over-henselian` (tag 04GH, rendered as Lemma 10.155.4 on
master). Plus chapter "Local Cohomology" (`local-cohomology.tex`),
Section "Cohomological dimension", Lemma `lemma-cd-local` (tag 0DXB,
rendered as Lemma 51.4.6). Permalinks:
<https://stacks.math.columbia.edu/tag/04GG>,
<https://stacks.math.columbia.edu/tag/04GH>,
<https://stacks.math.columbia.edu/tag/0DXB>.

## Slug
stacks-04gg

## Retrieval status
RETRIEVED — 2026-06-04

## Local source files
- `references/stacks-04gg.tex` — verbatim excerpts:
  1. `algebra.tex` lines 42066–42433 (section header
     `\section{Henselian local rings}` + `definition-henselian` +
     `lemma-uniqueness` + `lemma-characterize-henselian` [tag 04GG]
     with full proof + `lemma-finite-over-henselian` [tag 04GH]
     with full proof + `lemma-mop-up` [tag 04GJ]).
     Retrieved from
     <https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex>.
  2. `local-cohomology.tex` lines 527–539 (`lemma-cd-local` [tag 0DXB]
     with full proof). Retrieved from
     <https://raw.githubusercontent.com/stacks/stacks-project/master/local-cohomology.tex>.

The full `algebra.tex` (1.7 MB) and `local-cohomology.tex` are
upstream at the same URLs — fetch on demand if more context is
needed.

## Why this source
The `blueprint-writer-strictly-henselian-04gg` dispatcher needs
verbatim `% SOURCE QUOTE:` blocks for three lemmas it is about to
write into
`blueprint/src/chapters/Proetale_Mathlib_RingTheory_Etale_StrictlyHenselian.tex`:
the henselian-decomposition pipeline ("Algebra over henselian local
ring is a finite product of local rings"). Quoting from training
memory would risk mistagging or restating the lemma; this file gives
the writer the exact text to copy.

## Contents map
The TeX excerpts at `references/stacks-04gg.tex` cover (numbering
matches the rendered Stacks page; the master tex source has no
in-file lemma/section numbers — only labels — so cite by tag):

- §10.155 "Henselian local rings" (tag 04GE; label
  `section-henselian`) — section intro paragraph on conventions.
- Definition 10.155.1 (tag 04GF, label `definition-henselian`) —
  defines henselian / strictly henselian local rings.
- Lemma 10.155.2 (label `lemma-uniqueness`) — uniqueness of the
  Hensel lift of a simple root. Cited inside the proof of 04GG.
- **Lemma 10.155.3 (tag 04GG, label `lemma-characterize-henselian`)**
  — the 13-condition equivalence characterising henselian local
  rings. Items used most below: (1) the definition; (8) unique
  retraction along an étale map; (9)/(10) any finite $R$-algebra is a
  (finite) product of local rings; (11)/(13) decompose finite-type /
  quasi-finite algebras as $A\times B$ with $A$ finite and $B$
  non-quasi-finite / $B\otimes_R\kappa=0$.  Proof is by chains of
  implications, cites `proposition-etale-locally-standard`,
  `lemma-etale-makes-quasi-finite-finite`, `lemma-uniqueness`,
  `lemma-NAK`, `lemma-grothendieck-general`, `lemma-finite-flat-local`,
  `lemma-charpoly` (none of these are vendored — `lake env grep` the
  upstream `algebra.tex` if you need them).
- **Lemma 10.155.4 (tag 04GH, label `lemma-finite-over-henselian`)**
  — the four-part lemma: (1) finite over henselian = finite product
  of henselian locals each finite over $R$; (2) finite-over-henselian
  + $S$ local ⇒ $S$ henselian and the map is local; (3) finite-type
  + quasi-finite at $\mathfrak q$ ⇒ $S_{\mathfrak q}$ henselian finite
  over $R$; (4) the corresponding quasi-finite global statement.
  Proof is a thin wrapper over 04GG parts (10)/(11).
- Lemma 10.155.5 (tag 04GJ, label `lemma-mop-up`) — companion: any
  finite type algebra over a henselian local ring is a product
  $A_1\times\cdots\times A_n\times B$ with each $A_i$ finite local
  and $B$ non-quasi-finite over the closed point. One-line proof from
  04GG (10)+(11). Included because it is the sibling lemma the
  dispatcher's strictly-henselian chapter is likely to cite alongside
  04GH.
- **Lemma 51.4.6 (tag 0DXB, label `lemma-cd-local`)** — see
  "Caveats" below; included for verification, but DOES NOT MATCH the
  dispatcher's stated content for 0DXB.

## Caveats

### Tag 0DXB does NOT match the dispatcher's description
The directive describes 0DXB as "residue-product Hensel-lift
reduction (orthogonal idempotents lifting from $S/\mathfrak mS$ to
$S$)". This is wrong. Tag 0DXB resolves (via
`tags/tags` in the Stacks repo) to label
`local-cohomology-lemma-cd-local`, which states
$\mathrm{cd}(A,I) = \max_{\mathfrak p}\mathrm{cd}(A_{\mathfrak p},
I_{\mathfrak p})$ for a finitely generated ideal $I$. It is in
chapter "Local Cohomology", section "Cohomological dimension", and
has no relation to henselian rings or idempotent lifting. The
verbatim text is included in `stacks-04gg.tex` so the dispatcher can
confirm this for themselves.

Likely intended tags for "orthogonal idempotents lifting from
$S/\mathfrak mS$ to $S$ when $S$ is finite over a henselian local
ring $R$":

- The fact is folded directly into the proof of
  **04GG, implication (8)⇒(10)** (see lines 42245–42267 of
  `algebra.tex` / lines ~189–211 of the vendored excerpt). There is
  no separate Stacks tag for this internal proof step.
- For raw idempotent-lifting (no Henselian assumption, only
  Jacobson-radical / nilpotency), candidates are:
  - **00J9** (`algebra-lemma-lift-idempotents`) — lifting idempotents
    modulo a nil ideal.
  - **05BU** (`algebra-lemma-lift-idempotents-noncommutative`) — the
    noncommutative version.
  - **07LY** (`more-algebra-lemma-lift-idempotent`) — lift idempotent
    along a Henselian pair.
  - **07M4** (`more-algebra-lemma-lift-idempotent-upstairs`) — lift
    upstairs along a Henselian pair.
  - **09XF** (`more-algebra-lemma-idempotents-determined-modulo-radical`)
    — idempotents are determined modulo the Jacobson radical.

The most likely intended tag, given the phrasing "residue-product /
Hensel-lift / S/mS lifting to S", is **04GG itself** (the proof step
(8)⇒(10)) or **07LY** if the dispatcher conflated the local henselian
case with the henselian-pair case. The dispatcher should re-check
its source text before quoting.

### Other caveats
- Stacks tag identifiers are stable but the printed lemma numbers
  ("10.155.3", "51.4.6") can shift if the chapter is reorganised;
  cite by tag, not by number.
- The Stacks Project does not publish per-tag PDFs; only the LaTeX is
  vendored.
- The verbatim excerpts use Stacks-internal macros (`\Spec`,
  `\colim`, `\Im`, ...) defined in the project's preamble
  (`stacks-project-preamble.tex`); the excerpt is not
  standalone-compilable but is faithful to the source.

## Quality / provenance
Vendored TeX comes directly from the master branch of the Stacks
Project's official GitHub repository
(`github.com/stacks/stacks-project`); tag-to-label mapping comes from
the same repository's `tags/tags` table (also fetched and grepped
during retrieval). Rendered chapter numbers / lemma indices were
cross-checked against the project's own website
(<https://stacks.math.columbia.edu/tag/04GG> etc.). Confidence that
this is the authoritative version: maximal.
