# Sharp–Wadsworth 1976 (charpoly descent) — attempt

## Citation as given by dispatcher

R. Y. Sharp and A. R. Wadsworth, paper on "characteristic-polynomial
descent for Henselian / integral extensions", mid-1970s. Exact title
unknown — the blueprint names "Sharp–Wadsworth 1976 charpoly descent"
without further pointer. (Citation per the dispatcher's directive,
explicitly flagged as "Exact title unknown".)

## Slug

sharp-wadsworth-1976

## Retrieval status

NOT_RETRIEVED — 2026-06-02. No local source file exists. DO NOT cite
this as `(read from …)`.

The cited paper **does not appear to exist**. See "Sources tried"
below for the evidence.

## Sources tried

- WebSearch `Sharp Wadsworth 1976 Henselian characteristic polynomial
  descent` — no hits attributable to a joint Sharp–Wadsworth paper.
- WebSearch `"R.Y. Sharp" "Wadsworth" henselian 1976 integral` — no
  joint paper hits. Returned independent works by each author from
  the period.
- WebSearch `"R. Y. Sharp" Wadsworth coauthor commutative algebra` —
  Sharp's coauthors do not include Wadsworth in any returned result.
- WebSearch `"A.R. Wadsworth" "henselian" 1976 1975 Pacific Journal
  Math` — Wadsworth's only located henselian paper is the 1983
  Pacific J. Math paper on p-henselian fields, not a 1976 paper.
- Bash `curl -sLk https://mathweb.ucsd.edu/~wadswrth/publications.html`
  — successfully fetched **A. R. Wadsworth's complete publication
  list from his UCSD page**. Of his publications in 1975–1977:
    - 1974: "Pairs of domains where all intermediate domains are
      Noetherian", Trans. AMS 195. (no Sharp)
    - 1975: "Similarity of quadratic forms and isomorphism of their
      function fields", Trans. AMS 208, 352–358. (no Sharp)
    - 1976: "Hilbert subalgebras of finitely generated algebras",
      J. Algebra 43, 298–304. **(no Sharp, not about henselian rings)**
    - 1977: (with D. B. Shapiro) "Spaces of similarities. III.", J.
      Algebra 46. (no Sharp)
    - 1977: "Hilbert subalgebras of finitely generated algebras. II",
      Comm. Algebra 5. (no Sharp)
    - 1977: (with D. B. Shapiro) "On multiples of round and Pfister
      forms", Math. Z. 157. (no Sharp)
    - 1977: (with R. Elman and T. Y. Lam) "Amenable fields and Pfister
      extensions", Conf. on Quadratic Forms — 1976. (no Sharp)

  **Wadsworth has no coauthored paper with anyone named Sharp anywhere
  in his publication list.** This is authoritative — the list is the
  author's own UCSD page (`mathweb.ucsd.edu/~wadswrth/publications.html`).

## Why it matters / what to do next

The dispatcher (iter-126 plan, preparing iter-127) wanted this paper
to inform a substantive attempt at the L350 sorry in
`Proetale/Mathlib/RingTheory/Etale/HenselianPair.lean`
(`Algebra.Etale.idempotent_lift_limit`).

**Assessment.** The citation "Sharp–Wadsworth 1976" appears to be a
**hallucination by the blueprint writer**. The combined evidence:

1. Wadsworth's own publication list has zero Sharp-coauthored entries
   from any year.
2. Wadsworth's actual 1976 paper is on Hilbert subalgebras (J. Alg
   43, 298–304), which has no obvious relevance to characteristic-
   polynomial descent for henselian rings.
3. R. Y. Sharp's mid-1970s output (e.g. "The effect on associated
   prime ideals produced by an extension of the base field", Math.
   Scand. 38, 43–52, 1976) is also not on henselian descent.
4. The directive itself flagged "Exact title unknown" — the blueprint
   names the pair without enough specificity for the reader to
   recover the actual paper, because no actual paper underlies it.

The dispatcher's iter-127 planner should treat this pointer as
unsubstantiated and should NOT rely on it for the L350 strategy.
**Recommended action: delete or annotate the
"à la Hiblot 1975 / Sharp–Wadsworth 1976" remark in
`Proetale_Mathlib_RingTheory_Etale_HenselianIdempotentLift.tex`
lines 130–133, since the citations are not verifiable.** Modern
references for the same technique (descent of an idempotent's
characteristic polynomial through a henselian extension) include:

- Raynaud, M., *Anneaux locaux henséliens*, LNM 169, Springer, 1970
  — definitive treatment of henselian local rings; the Newton /
  approximation step appears in the standard form there.
- Stacks Project tag 04GE et seq.; specifically tag 09XI for
  "lifting idempotents" and tag 04GG for henselian-pair lifting of
  étale algebras.
- EGA IV, §18 — Hensel's lemma and étale lifting in the standard
  reference form.
- Bourbaki, *Algèbre Commutative*, Ch. IX — complete Noetherian local
  rings and Hensel-lifting; Ch. III §4 for charpoly.

If the iter-127 planner still wants a primary source obtained, the
dispatcher should send a new directive naming one of these (which
DO exist).

<!-- NO contents map, NO abstract, NO recalled statements. There is
     nothing verified to record. -->
