# Hiblot 1975 (henselian rings) — attempt

## Citation as given by dispatcher

Jean-Jacques Hiblot, *Sur les anneaux henséliens*, Comptes Rendus de
l'Académie des Sciences, Série A, **280** (1975), pp. 1429–1431
(citation from the dispatcher's directive — explicitly flagged as
"approximate publication info; verify exact citation").

## Slug

hiblot-1975

## Retrieval status

NOT_RETRIEVED — 2026-06-02. No local source file exists. DO NOT cite
this as `(read from …)`.

The cited paper **could not be located through any open channel and
may not exist under this title**. See "Sources tried" below.

## Sources tried

- WebSearch `"Hiblot 1975 \"anneaux henséliens\" Comptes Rendus"` — no
  hits attributable to a Hiblot paper on henselian rings.
- WebSearch `"J.-J. Hiblot" OR "Jean-Jacques Hiblot" henselian 1975`
  — no hits.
- WebSearch `"Hiblot" "Comptes Rendus" anneaux henséliens` — returned
  unrelated Lafon / Raynaud / Seydi papers on henselian rings.
- WebSearch `Hiblot "Sur les anneaux henséliens" 1975 CRAS` — no
  exact-title hit. Search engine surfaced a *different* 1975 Hiblot
  CRAS paper instead: "Des anneaux euclidiens dont le plus petit
  algorithme n'est pas à valeurs finies", C. R. Acad. Sci. Paris Sér.
  A-B, **281** (1975), no. 12, A411–A414 — **about Euclidean rings,
  not henselian rings**.
- WebSearch `Hiblot "des anneaux euclidiens" 1975 Comptes Rendus` —
  confirmed the Euclidean-rings paper as Hiblot's only located 1975
  CRAS publication.
- WebSearch `"Hiblot" 1975 OR 1976 numdam OR CRAS henselien` — no
  match for a Hiblot henselian paper at Numdam.
- WebFetch `https://zbmath.org/?q=au:hiblot+py:1975` — 403 (zbMATH
  blocks programmatic access).
- WebFetch `https://gallica.bnf.fr/...` (Gallica CRAS index) — 400.
- WebFetch `https://www.bing.com/search?q="Hiblot"+1975+"hens%C3%A9liens"` —
  only unrelated / spam results; no mathematical literature hits.

## Why it matters / what to do next

The dispatcher (iter-126 plan, preparing iter-127) wanted this paper
to inform a substantive attempt at the L350 sorry in
`Proetale/Mathlib/RingTheory/Etale/HenselianPair.lean`
(`Algebra.Etale.idempotent_lift_limit`) — specifically the descent /
limit-identification step for the Newton-Cauchy sequence of `Y^2 - Y`
over a henselian local ring.

**Assessment.** The citation `Hiblot 1975 / Sharp-Wadsworth 1976`
appears in the blueprint at
`blueprint/src/chapters/Proetale_Mathlib_RingTheory_Etale_HenselianIdempotentLift.tex`
lines 130–133, in the form
"...à la Hiblot 1975 / Sharp–Wadsworth 1976 — not in this chapter."
No bibliographic entry backs either name (the blueprint has no
bibliography file). The directive itself flags the Hiblot citation
as "approximate publication info; verify exact citation" and the
Sharp–Wadsworth citation as "Exact title unknown".

Combined with the search evidence (Hiblot's only located 1975 CRAS
paper is on Euclidean rings, and no Sharp–Wadsworth henselian paper
exists — see `sharp-wadsworth-1976.md`), the most likely explanation
is that **both names are misremembered or fabricated** by the
blueprint author. The dispatcher's iter-127 planner should treat the
"Hiblot 1975 / Sharp–Wadsworth 1976" pointer as unsubstantiated and
should NOT rely on it for the L350 strategy.

**Recommended alternatives for the iter-127 planner:**
- Raynaud, M., *Anneaux locaux henséliens*, Lecture Notes in
  Mathematics **169**, Springer-Verlag, 1970 — the standard reference
  for henselian rings, contains the Newton-iteration / approximation
  machinery in its modern form.
- Stacks Project tag 04GE et seq. (Henselian local rings) — for the
  henselian-pair version and idempotent lifting (Stacks tag 09XI:
  "lifting idempotents").
- Bourbaki, *Algèbre Commutative*, Ch. IX (Anneaux locaux noethériens
  complets) — characteristic-polynomial descent and Hensel-lifting.

The dispatcher may want to send a new directive to this subagent
naming one of these instead — those sources DO exist and have known
locations.
