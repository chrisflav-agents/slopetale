# Stacks Project — Tags 092P and 092Q (Weakly étale ring maps, field base)

## Citation

The Stacks Project Authors. *Stacks Project*, Chapter 15 ("More on
Algebra"), Section 15.106 ("Weakly étale ring maps"). Tags **092P**
(Lemma 15.106.15) and **092Q** (Lemma 15.106.16). Source repository:
<https://github.com/stacks/stacks-project>, file `more-algebra.tex`.
The section's introductory note attributes most of its results to
J.-P. Olivier, "Anneaux absolument plats universels et épimorphismes à
buts réduits" (and the related paper by D. Ferrand on epimorphisms).

Canonical viewing URLs:
- <https://stacks.math.columbia.edu/tag/092P>
- <https://stacks.math.columbia.edu/tag/092Q>

## Slug

stacks-092PQ

## Retrieval status

RETRIEVED — 2026-06-03

## Local source files

- `references/stacks-092PQ.tex` — verbatim LaTeX excerpt of
  Section 15.106 ("Weakly étale ring maps") of `more-algebra.tex`,
  spanning the section header through the end of tag **092Q**'s proof.
  Copied verbatim from lines 30179–30552 of the shared full-chapter
  download `references/stacks-09xi-more-algebra-full.tex`.
- `references/stacks-09xi-more-algebra-full.tex` — the entire
  `more-algebra.tex` file (≈1.4 MB, 39 221 lines). **Shared** with the
  `stacks-09xi` retrieval — not re-downloaded for this slug. Retrieved
  on 2026-06-02 from
  <https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex>.

(No PDF: the Stacks Project does not publish per-tag PDFs. The
rendered HTML at the canonical URLs above was used only to verify the
tag-to-label mapping; TeX is the authoritative source.)

## Why this source

A blueprint-writer is filling two "TBA." gaps in
`blueprint/src/chapters/more-on-local-structure.tex` for the Lean
targets `Algebra.WeaklyEtale.isAlgebraic`,
`Algebra.WeaklyEtale.etale_of_fg`, `Algebra.WeaklyEtale.indEtale_field`,
and a new `Algebra.WeaklyEtale.isAlgebraic_of_weaklyEtale`. Under
cite-and-read discipline (`% SOURCE QUOTE:` / `% SOURCE QUOTE PROOF:`),
the writer needs the verbatim statement and proof TeX of 092P and 092Q
in the excerpt — paraphrase is not acceptable.

## Contents map

The verbatim excerpt `stacks-092PQ.tex` mirrors Section 15.106 of
`more-algebra.tex` top-to-bottom. Locations are line numbers inside
the shared full-chapter file `stacks-09xi-more-algebra-full.tex` (=
the upstream `more-algebra.tex`); a parenthesized range gives the
matching line numbers inside the local excerpt `stacks-092PQ.tex`.

Section header and definitions:

| Block | `…-full.tex` lines | `stacks-092PQ.tex` lines |
| ----- | ------------------ | ------------------------ |
| `\section{Weakly étale ring maps}` + `\label{section-weakly-etale}` + Olivier/Ferrand attribution | 30179–30185 | 17–23 |
| `definition-weakly-etale` (def. of absolutely flat / weakly étale) | 30187–30192 | 25–30 |
| `definition-weak-dimension` | 30222–30227 | 60–65 |

Helper lemmas in the same section (transitively used by 092P / 092Q):

| Block | `…-full.tex` lines | `stacks-092PQ.tex` lines | Role |
| ----- | ------------------ | ------------------------ | ---- |
| `lemma-key` | 30200–30220 | 38–58 | flat $A$-mod ⇒ flat $B$-mod when $B\otimes_A B\to B$ flat |
| `lemma-weak-dimension-goes-up` | 30229–30246 | 67–84 | weak-dim transports along weakly étale |
| `lemma-absolutely-flat` | 30248–30285 | 86–123 | 4-way characterization of absolutely flat |
| `lemma-product-fields-absolutely-flat` | 30287–30299 | 125–137 | $\prod K_i$ absolutely flat |
| `lemma-base-change-weakly-etale` | 30301–30319 | 139–157 | base change preserves weakly étale |
| `lemma-absolutely-flat-over-absolutely-flat` | 30321–30343 | 159–181 | weakly étale over reduced ⇒ reduced |
| `lemma-composition-weakly-etale` | 30345–30371 | 183–209 | composition of weakly étale |
| `lemma-go-down` | 30373–30401 | 211–239 | faithfully flat descent of weak étale-ness |
| `lemma-weakly-etale-permanence` | 30403–30414 | 241–252 | between weakly étale algebras, maps are weakly étale |
| `lemma-formally-unramified` | 30416–30432 | 254–270 | $B\otimes_A B\to B$ flat ⇒ $\Omega_{B/A}=0$ |
| `lemma-weakly-etale-finite-type` | 30434–30450 | 272–288 | finite presentation + weakly étale ⇒ étale |
| `lemma-when-weakly-etale` | 30452–30484 | 290–322 | localization / étale / filtered colim ⇒ weakly étale |

(Helper lemmas above are NOT each individually assigned to a public
Stacks tag here; only `\label{...}` names are stable. The tag system
maps `lemma-absolutely-flat-fields` → **092P** and
`lemma-absolutely-flat-over-field` → **092Q**; for the helpers, cite
by label, not by guessed tag.)

The two target tags:

| Block | Stacks tag | `…-full.tex` lines | `stacks-092PQ.tex` lines | Statement (verbatim) |
| ----- | ---------- | ------------------ | ------------------------ | -------------------- |
| **`lemma-absolutely-flat-fields`** | **092P** = Lemma 15.106.15 | **30486–30500** | **327–341** | "Let $L/K$ be an extension of fields. If $L\otimes_K L\to L$ is flat, then $L$ is an algebraic separable extension of $K$." |
| **`lemma-absolutely-flat-over-field`** | **092Q** = Lemma 15.106.16 | **30502–30552** | **346–396** | "Let $B$ be an algebra over a field $K$. The following are equivalent: (1) $B\otimes_K B\to B$ is flat, (2) $K\to B$ is weakly étale, (3) $B$ is a filtered colimit of étale $K$-algebras. Moreover, every finitely generated $K$-subalgebra of $B$ is étale over $K$."  |

Within each target block, the statement runs from `\begin{lemma}`
through `\end{lemma}` and the proof from `\begin{proof}` through
`\end{proof}`. Explicitly: in `stacks-092PQ.tex`,
- 092P statement: lines 327–331 (`\begin{lemma}` … `\end{lemma}`).
- 092P proof:     lines 333–341 (`\begin{proof}` … `\end{proof}`).
- 092Q statement: lines 346–357 (`\begin{lemma}` … `\end{lemma}`).
- 092Q proof:     lines 359–396 (`\begin{proof}` … `\end{proof}`).

Tag-to-label mapping for 092P and 092Q was independently verified
against the rendered tag pages
<https://stacks.math.columbia.edu/tag/092P> and
<https://stacks.math.columbia.edu/tag/092Q> on 2026-06-03; both
statements matched the excerpt byte-for-byte (modulo HTML rendering of
math).

## Caveats

- The `\ref{algebra-...}` commands inside the vendored text point into
  chapter 10 (`algebra.tex`), a different file. They are **not** broken
  in the full Stacks build, but the excerpt is not self-contained for
  standalone compilation. Resolve any specific `algebra-...` reference
  at `https://stacks.math.columbia.edu/tag/XXXX`.
- The 092P proof has a small grammatical glitch in the source ("any
  subfield $K \subset L' \subset L$ the map …"); this is preserved
  verbatim in the excerpt — do not "fix" it when quoting.
- The 092Q proof similarly has "$B$ is a absolutely flat ring" (sic);
  preserved verbatim.
- No PDF version exists — the Stacks Project does not publish per-tag
  PDFs.
- The 092Q statement bundles both the equivalence (1)⇔(2)⇔(3) **and**
  the finite-subalgebra "moreover" clause into a single tag. When the
  Lean side splits these (e.g. `Algebra.WeaklyEtale.etale_of_fg` vs
  `Algebra.WeaklyEtale.indEtale_field`), both Lean targets cite the
  same tag 092Q — that is correct, not a misattribution.

## Quality / provenance

The Stacks Project is open-source under the GNU FDL with publicly
versioned LaTeX source on GitHub. The two target lemma blocks in
`stacks-092PQ.tex` are byte-for-byte identical to lines 30486–30552
of `stacks-09xi-more-algebra-full.tex` (= the master commit of
`more-algebra.tex` as of 2026-06-02). This is the definitive reference
for tags 092P and 092Q; any textbook or lecture-note restatement
should be cross-checked against this excerpt, not the other way around.
