# Bourbaki — *Algèbre commutative*, Chapitre I "Modules plats" (1958 draft)

## Citation

N. Bourbaki, *Algèbre commutative*, Chapitre I "Modules plats". 1958 working draft (Rédaction n° 308) by Claude Chevalley — basis for the published 1961 / 1985 Springer Hermann edition (ISBN 978-3-540-33976-2 covers Chapitres 1 à 4 in the reprinted Springer edition).

Archives Bourbaki item: `https://archives-bourbaki.ahp-numerique.fr/items/show/752` ("Rédaction n° 308 : Appendice I … Chapitre I d'Algèbre commutative. Modules plats", Chevalley, novembre 1958, 74 pp).

## Slug

bourbaki-AC-Ch1-modules-plats-draft

## Retrieval status

RETRIEVED — 2026-06-05 (1958 WORKING DRAFT, NOT THE 1961 PUBLISHED CHAPTER)

## Local source files

- `references/bourbaki-AC-Ch1-modules-plats-draft.pdf` — PDF (11.80 MB), verified by header `%PDF-1.5`. Retrieved from `https://archives-bourbaki.ahp-numerique.fr/files/original/a09f550075e74cdd70d912efd9652721.pdf` (Archives Bourbaki, file name `r308_iecl_bki08-4.pdf`). The Archives Bourbaki is the **legitimate open digitization project** of the Bourbaki Group's working manuscripts, maintained jointly by IECL, AHP, and Mathdoc.

## Why this source

iter-147 directive `purity-flat-literature` cites Bourbaki *Algèbre commutative* Chapitre I §3 ("Modules plats") — specifically §3.5 "Modules plats et localisation" and any treatment of *pure submodules* — as one of the four classical references that, jointly with Lazard 1969, fix the algebraic foundations the iter-148 plan agent needs to decide the L195 specialized cycle-breaker in `Proetale/Algebra/WeaklyEtaleField.lean`.

The 1958 working draft retrieved here corresponds in scope (and largely in content) to the published Chapter I but is **not** the verbatim 1961 published text. The published Hermann/Springer Chapter I is paywalled and was not obtainable through any open channel during this retrieval (Springer link: `https://link.springer.com/book/10.1007/978-3-540-33976-2`).

## Contents map

The 1958 draft organizes the chapter as (page numbers refer to the draft PDF's printed pagination, not arXiv-style absolute page numbers; the draft is hand-paginated within each §):

- **Appendice I.** Diagrammes — suites exactes
- **Appendice II.** Définition des groupes `Tor_n(E, F)`
- **Chapitre I. Modules plats**
  - **§ 1. Définition des modules plats.** Equivalences with `(M ⊗ —)` exactness, and the relationship to `Tor_1 = 0`.
  - **§ 2. Propriétés d'isomorphisme liées à la platitude.** Module-categorical / functorial properties; flat base-change of tensor products.
  - **§ 3. Construction de modules plats.** Localisation, free / projective ⇒ flat, direct limits of flat modules, transfer along ring maps.

(The retriever's note from the Archives Bourbaki landing page suggests these are the only three sections in this draft; the published 1961 Chapter I has additional sections — `§ 4. Modules fidèlement plats`, `§ 5. Equations linéaires sur un anneau`, **`§ 6. Modules platement épimorphes` / treatment of pure submodules** — that appear to have been added between 1958 and publication. The draft therefore does NOT contain Bourbaki's published material on pure submodules.)

A planner who needs the published §3.5 "Modules plats et localisation" or the published treatment of *sous-modules purs* should:

1. Treat this draft as historical context (useful for the original framing of `M flat ↔ Tor_1 = 0`), not as a direct substitute.
2. Quote Lazard 1969 Chapter II §1 instead — Lazard explicitly references and extends Bourbaki's pure-submodule formalism, and our Lazard scan is the actual 1969 published text.
3. If the iter-148 plan absolutely requires citing the published Bourbaki AC §I.3.5, fall back to the §15.106 / §15.107 vendored Stacks excerpts (already in `stacks-09xi-more-algebra-full.tex` / `stacks-pure-ideals.tex`), which prove the same statements citation-free.

## Caveats

- **DRAFT, NOT PUBLISHED VERSION.** Statements, numbering, and even the section structure differ from the published 1961 Chapter I. Do NOT cite from this PDF as "Bourbaki AC Ch. I §X.Y" — cite as "Bourbaki AC Ch. I draft (Chevalley, 1958), §X" or use Lazard / Stacks instead.
- **French.** Like Lazard 1969 the text is entirely in French.
- **Handwritten + typewritten mix.** The draft is partly hand-typeset, partly handwritten, with handwritten corrections in margins. OCR will be unreliable; visual inspection is required.
- **Published edition is paywalled.** Springer (`10.1007/978-3-540-33976-2`) and the equivalent Hermann French original have no legitimate open copy located. Note this for the dispatcher — Bourbaki's published treatment of pure submodules is unobtainable through any legitimate open channel.

## Quality / provenance

The Archives Bourbaki project (jointly IECL Nancy + AHP Lorraine + Cellule Mathdoc Grenoble) is the *authoritative* open digitization of the Bourbaki Group's working manuscripts. The PDF is the project's own scan of the original mimeograph and includes Chevalley's signature and dating. This is the best primary source available for Bourbaki's evolving treatment of flatness short of purchasing the published Hermann/Springer Chapter I.
