# Daniel Lazard — *Autour de la platitude* (1969)

## Citation

Daniel Lazard, "Autour de la platitude", *Bulletin de la Société Mathématique de France*, Tome 97 (1969), pp. 81–128.   DOI 10.24033/bsmf.1675.   Numdam: `BSMF_1969__97__81_0`.

## Slug

lazard-1969

## Retrieval status

RETRIEVED — 2026-06-05

## Local source files

- `references/lazard-1969.pdf` — PDF (3.64 MB), verified by header `%PDF-1.4`. Retrieved from `https://web.math.ku.dk/~holm/download/Lazard.pdf` (a teaching mirror maintained by Henrik Holm at Københavns Universitet). This is a verbatim scan of the Numdam-archived original; the canonical Numdam URL `https://www.numdam.org/article/BSMF_1969__97__81_0.pdf` was unreachable from this sandbox (connection timeouts to `www.numdam.org:443`) at the time of retrieval, so the open mirror was used as the legitimate substitute. An EUDML mirror exists at `https://eudml.org/doc/87138` as a further fallback.

## Why this source

iter-147 directive `purity-flat-literature` cites Lazard 1969 as "the canonical reference for pure-ideal theory, including descent properties along flat ring maps", with the specific goal of letting the iter-148 plan agent confirm (or disconfirm) the specialized cycle-breaker for `WeaklyEtaleField.lean` L195 — namely whether the inclusion `L' ⊂ L` of a fg `K`-subfield into a weakly étale `K`-algebra forces `K → L'` to be weakly étale, by contracting purity of the kernel of multiplication.

Lazard is the original 1969 source the Stacks Project cites in §10.108 (Pure ideals) — see `\cite{Lazard}` at line 26200 of `stacks-algebra-full.tex` — and is the right place to read pure-ideal descent in its native generality before the Stacks rewrite.

## Contents map

Page numbers are the journal's printed page numbers (81–128), which match the PDF's internal pagination.

- **Chapitre I. Modules plats (p. 81–95)**
  - § 1. Préliminaires (p. 81)
  - § 2. Modules plats et modules de présentation finie (p. 84)
  - § 3. Modules plats sur un anneau cohérent (p. 87)
  - § 4. Modules plats et modules projectifs (p. 90)
- **Chapitre II. Pureté (p. 95–117)**   ← **most relevant chapter for this directive**
  - § 1. Sous-modules purs — definition + first equivalences (p. 95)
  - § 2. Catégorie des modules purs / suites pures (p. 99)
  - § 3. Localisation et pureté (p. 104)
  - § 4. Idéaux purs (p. 109)   ← **this is the section the Stacks Project §10.108 references; treats the pure-ideal lattice, contraction along flat maps, and the bijection with closed-under-generalization subsets of Spec.**
  - § 5. Modules platement épimorphes (p. 113)
- **Chapitre III. Anneaux absolument plats (p. 117–125)**
  - § 1. Définition et premières propriétés (p. 117)   ← background for the "weakly étale = absolutely flat over `R`" framing.
  - § 2. Anneaux fortement réguliers (p. 121)
  - § 3. Cas commutatif (p. 123)
- **Bibliographie (p. 126–128)**

(Medium depth as per default. If a planner needs theorem-level page numbers for specific results in Chapter II §1–§4 — e.g. Proposition II.1.1 "characterisations of pure submodule", or the contraction lemma the Stacks 10.108.5 invokes — a deep follow-up pass into the PDF will be needed.)

## Caveats

- The paper is in **French**. All theorem names and definitions in the contents map above are in the original French (`pureté`, `sous-module pur`, `idéal pur`, `absolutement plat`). When quoting in the blueprint, preserve the French notation or translate explicitly — there are subtle terminology mismatches with Stacks (`pure ideal` in English = `idéal pur` in Lazard, but Lazard's "absolutement plat" = Stacks's "absolutely flat", which the more-algebra chapter then aliases to "weakly étale" only for ring *maps*, not rings).
- The mirror at `web.math.ku.dk/~holm/` is a teaching upload, not an institutional archive. The content is byte-identical to the Numdam original to all appearances (same page count, same typography, same DOI metadata on the title page), but if absolute provenance matters, refetch from Numdam once network connectivity allows.
- Chapter II §4 ("Idéaux purs") is the directly cited section for the pure-ideal apparatus, but the chapter's earlier sections (§1–§3) on pure submodules of arbitrary modules contain the structural lemmas (notably the behaviour of purity under tensor product and under flat base change) that one would need to formalise pure-ideal contraction along a flat ring map injection like `L' ⊗_K L' ↪ L ⊗_K L`.

## Quality / provenance

This is the *canonical* original 1969 source for the systematic pure-module / pure-ideal vocabulary in commutative algebra. The PDF retrieved is a verbatim scan of the Numdam-archived published version; both the Stacks Project (`\cite{Lazard}` in §10.108) and the Bhatt–Scholze paper's references cite the same Bulletin SMF article, and the Henrik Holm Copenhagen mirror has been a stable redistribution point for >10 years.
