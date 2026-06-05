# Stacks Project — Tag 09XI (Lemma 15.11.6, "Characterize henselian pair")

## Citation

The Stacks Project Authors. *Stacks Project*, Tag 09XI =
Lemma 15.11.6 ("characterize-henselian-pair"), Chapter 15 ("More on
Algebra"), Section 15.11 ("Henselian pairs"). Source repository:
<https://github.com/stacks/stacks-project>. The lemma carries its own
internal `\begin{reference}` block citing Raynaud, *Anneaux locaux
hensélien*, Lect. Notes in Math. **169** (1970), Chapter XI, and
Gabber, "Affine analog of the proper base change theorem", *Israel J.
Math.* **87** (1994), Proposition 1.

## Slug

stacks-09xi

## Retrieval status

RETRIEVED — 2026-06-02

## Local source files

- `references/stacks-09xi.tex` — verbatim LaTeX excerpt covering tag
  09XI (`lemma-characterize-henselian-pair`) **plus** every helper
  lemma its proof cites that lives in the same chapter:
  - `definition-zariski-pair`
  - `definition-henselian-pair`
  - `lemma-idempotents-determined-modulo-radical`
  - `lemma-check-isomorphism-zariski`
  - `lemma-helper-finite`
  - `lemma-helper-finite-type`
  - `lemma-lift-idempotent-upstairs`

  All blocks copied verbatim from `more-algebra.tex` master @ commit-of-day
  2026-06-02. Cross-references prefixed `algebra-…` point into
  `algebra.tex` (a different chapter) and are left as-is — to resolve
  one, use `https://stacks.math.columbia.edu/tag/XXXX` with the matching
  tag.

- `references/stacks-09xi-more-algebra-full.tex` — the entire
  `more-algebra.tex` file (≈1.4 MB, 39 221 lines) as fetched. Keep as a
  fallback: lets a blueprint-writer grep for any extra
  `\ref{...}` target the excerpt didn't include without a second
  network round-trip. Retrieved from
  <https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex>.

(No PDF: the Stacks Project does not publish per-tag PDFs. The
chapter-level PDF is bundled into the 7000-page `book.pdf`, which is
disproportionate to ship here. The rendered HTML at
<https://stacks.math.columbia.edu/tag/09XI> is the canonical viewing
URL but is not vendored — TeX is the authoritative source.)

## Why this source

`Algebra.Etale.idempotent_lift_limit` in
`Proetale/Mathlib/RingTheory/Etale/HenselianPairLift.lean` (around L270)
is a banked `sorry`. STRATEGY.md commits to closing it by porting the
self-contained idempotent-lifting argument in tag 09XI directly: the
(1)⇔(2)⇔(3)⇔(4) cycle in `lemma-characterize-henselian-pair` is the
precise statement Mathlib's `HenselianRing` / `HenselianPair`
infrastructure routes onto. The previously-cited "Hiblot 1975" and
"Sharp–Wadsworth 1976" attributions were confirmed non-existent by
prior reference-retriever runs; tag 09XI is the source of record.

## Contents map

The verbatim excerpt `stacks-09xi.tex` is laid out top-to-bottom in
the order the dependencies are needed. Locations are line numbers
inside `stacks-09xi-more-algebra-full.tex` (= the upstream
`more-algebra.tex`):

| Block | Stacks tag | `…-full.tex` lines | Role in the 09XI proof |
| ----- | ---------- | ------------------ | ---------------------- |
| `lemma-lift-idempotent-upstairs` | (no public tag — Sec. 15.10) | 1977–2017 | Idempotents of `B/IB` lift étale-locally; used in (2)⇒(4) and inside `lemma-helper-finite` |
| `definition-zariski-pair` | (Sec. 15.11 prelim.) | 2245–2249 | "I in Jacobson radical" pair |
| `lemma-idempotents-determined-modulo-radical` | (Sec. 15.11 prelim.) | 2251–2262 | Injectivity of idempotents `B → B/IB` for Zariski pair; used in (2)⇒(4) |
| `lemma-check-isomorphism-zariski` | (Sec. 15.11 prelim.) | 2264–2287 | Flat-integral-fp + iso mod I ⇒ iso; used in (5)⇒(2) |
| `lemma-helper-finite` | (Sec. 15.11 prelim.) | 2289–2344 | Produces monic `f` of the Gabber shape `T^n(T-1)+…` killing `b`; used in (5)⇒(2) |
| `definition-henselian-pair` | (Sec. 15.11) | 2393–2404 | Definition (1) of a henselian pair |
| `lemma-helper-finite-type` | (Sec. 15.11) | 2501–2550 | Decomposes `B'/IB'` integral-closure-wise compatibly with a given fin.type splitting; used in (5)⇒(2) |
| **`lemma-characterize-henselian-pair`** | **09XI** | **2552–2734** | **The lemma 09XI itself — five-fold equivalence and its proof (the relevant cycle for `idempotent_lift_limit` is (2)⇒(4) via `lemma-lift-idempotent-upstairs` + `lemma-idempotents-determined-modulo-radical`).** |

The five clauses of 09XI (verbatim from the source):

1. `(A,I)` is a henselian pair.
2. Every étale map `A → A'` with a section `σ : A' → A/I` lifts to a section `A' → A`.
3. For every **finite** `A`-algebra `B`, the map `B → B/IB` is a bijection on idempotents.
4. For every **integral** `A`-algebra `B`, the map `B → B/IB` is a bijection on idempotents.
5. (Gabber) `I ⊂ Jac(A)` and every monic `f(T) = Tⁿ(T-1) + aₙTⁿ + … + a₀` with `aᵢ ∈ I`, `n ≥ 1` has a root `α ∈ 1 + I` (unique).

The proof in `more-algebra.tex` proceeds (2)⇒(4)⇒(3)⇒(1)⇒(5)⇒(2). For
`idempotent_lift_limit`, the operative direction is the **(2)⇒(4)
half**, which is just two paragraphs and uses only the two lemmas
`lemma-idempotents-determined-modulo-radical` and
`lemma-lift-idempotent-upstairs` — both already vendored in
`stacks-09xi.tex`.

## Caveats

- The `\ref{algebra-...}` and `\ref{lemma-...}` commands inside the
  vendored text are pointers into other Stacks files
  (`algebra.tex`, etc.). They are **not** broken — they resolve in the
  full Stacks build — but if you `pdflatex` the excerpt in isolation
  you'll get undefined references. That is expected; the excerpt is
  meant to be read, not compiled standalone.
- The lemma is sometimes referred to colloquially as "Tag 09XI: lifting
  idempotents along a henselian pair". Strictly, lifting idempotents
  is one of the **equivalent** characterizations (clauses (3)–(4)), not
  the headline statement. When porting to Lean, the directly useful
  fact is the (2)⇒(4) direction: from "every étale map with a section
  mod I lifts" one obtains "the idempotents of any integral B match
  those of B/IB".
- The internal `\begin{reference}` block of 09XI cites Raynaud
  (Hensélisation, LNM 169, 1970) and Gabber (Israel J. Math. 1994).
  Neither of those is vendored under `references/`; if a blueprint
  chapter wants to cite the original sources of the equivalence (not
  just Stacks), those are the legitimate primary references.
- No PDF version is included — the Stacks Project does not publish
  per-tag PDFs. The TeX is authoritative.

## Quality / provenance

The Stacks Project is open-source under the GNU FDL with publicly
versioned LaTeX source on GitHub. The vendored excerpt is **byte-for-byte
identical** to lines 1977–2734 of upstream `more-algebra.tex` at the
master commit of 2026-06-02. This is the definitive reference for the
statement of tag 09XI; any other source (textbook restatement,
lecture-note paraphrase) should be cross-checked against it, not the
other way around.
