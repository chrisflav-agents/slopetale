# Task Pending

## Proetale/Algebra/IndZariski.lean

### Sorry 1: Line 77 (Transitivity)
**Status:** IN PROGRESS - Needs composition of ind properties via scalar towers
**Blocker:** Missing lemma showing ind respects composition

### Sorry 2: Line 124 (Localization is IndZariski)
**Status:** IN PROGRESS - Need to show general localization satisfies ind_isLocalIso
**Blocker:** `IsLocalization M S` doesn't directly give `IsStandardOpenImmersion` for general M

### Sorry 3: Line 143 (BijectiveOnStalks for IndZariski)
**Status:** IN PROGRESS - Need BijectiveOnStalks preserved by filtered colimits
**Blocker:** Missing preservation lemma

### Sorry 4: Line 151 (Colimit preservation)
**Status:** IN PROGRESS - Requires ind idempotence
**Blocker:** Need lemma about idempotence of ind for properties ≤ finitely presentable

### Sorry 5: Line 225 (ind-ind-Zariski = ind-Zariski)
**Status:** IN PROGRESS - Idempotence of ind
**Blocker:** Same as Sorry 4

### Sorry 6: Line 238 (Algebra version)
**Status:** IN PROGRESS - Conversion between MorphismProperty.ind and ObjectProperty.ind
**Blocker:** Depends on Sorry 5

**Common theme:** All require proving ind is idempotent or showing properties preserved by filtered colimits.

---


## Proetale/Algebra/WContractible.lean

### Sorry 1: Line 362 (Z definition - NEW in Session 8)
**Status:** STUB - Added to fix compilation error
**Blocker:** Requires `LocallyConnectedSpace (PrimeSpectrum A)` instance + full profinite Pullback construction
**Part of:** Sorry 4 infrastructure (150-200+ lines)
**Recommendation:** Accept as part of infrastructure gap

### Sorry 2: Line 418 (BijectiveOnStalks of ind-étale from w-strictly-local)
**Status:** BLOCKED - Missing Mathlib theorem (Session 7-8 confirmed)
**Blocker:** Requires theorem "étale algebra over strictly Henselian local ring has unique maximal ideal lying over the maximal ideal, and localization at that ideal is isomorphic to the base ring"
**Blueprint reference:** thm:ind-etale-strictly-henselian-localization-isom (line 1702)
**Estimated:** 100-150 lines to formalize missing theorem + apply it
**Recommendation:** Accept as Mathlib gap

### Sorry 3: Line 441 (Retraction exists for faithfully flat + BijectiveOnStalks)
**Status:** BLOCKED - Dependency on WLocal.lean sorry (Session 7-8 confirmed)
**Blocker:** Depends on `RingHom.IsWLocal.bijective_of_bijective` (sorry'd in WLocal.lean)
**Infrastructure available:** ✓ Restriction construction complete, ✓ Extremally disconnected projectivity exists
**Estimated:** 50-100 lines once dependency is resolved
**Recommendation:** Work on WLocal.lean first

### Sorry 4: Line 539 (W-contractible cover construction)
**Status:** BLOCKED - Missing profinite Pullback infrastructure (Session 7-8 confirmed)
**Blocker:** Requires colimit over DiscreteQuotient T (150-200+ lines of categorical infrastructure)
**Missing:** Colimit construction, π₀ property proof, w-local property proof, faithfully flat proof
**Recommendation:** Accept as infrastructure gap

### Compilation Status (Session 8):
- ✅ File now COMPILES with 4 sorries (fixed LocallyConnectedSpace error by stubbing Z definition)
- Sorry count: 4 (was 5, but one was duplicate/miscount)

---

## Proetale/Algebra/WStrictLocalization.lean

### Sorry 1: Line 64 (Retractions imply strictly Henselian)
**Status:** NOT STARTED - Foundational result requiring hundreds of lines
**Blocker:** Requires étale descent, prime avoidance, section extension

### Sorry 2: Line 108 (WLocalization is strictly Henselian)
**Status:** BLOCKED - Missing critical infrastructure
**Blocker:** Need IsStrictlyHenselianLocalRing preserved by RingEquiv, BijectiveOnStalks for WLocalization

---

## Proetale/Algebra/WLocalization/Ideal.lean

### Sorry 1: Line 378 (Surjectivity of quotient map)
**Status:** MATHEMATICAL ISSUE - algebraMap is NOT surjective (it's ind-Zariski)
**Blocker:** Need local-to-global principle: surjectivity from BijectiveOnStalks + Spec bijection
**Note:** Current approach assumes surjectivity of base map, which is false

---


## Proetale/Mathlib/Algebra/Category/CommAlgCat/Limits.lean

### Sorry 1: Line 186 (preservesColimitsOfSize_forget_commRingCat)
**Status:** BLOCKED - Missing Mathlib infrastructure
**Blocker:** `Under.forget` only preserves filtered colimits, not all colimits

### Sorry 2: Line 400 (preservesFilteredColimitsOfSize_forget)
**Status:** UNIVERSE LEVEL MISMATCH
**Note:** Downstream uses only need `{u, u}` which already exists, may not be critical

### Sorry 3: Line 444 (AlgCat.preservesFilteredColimitsOfSize_forget_moduleCat)
**Status:** IN PROGRESS - Requires explicit filtered colimit construction
**Blocker:** Need to construct filtered colimits in AlgCat (100+ lines based on CommAlgCat pattern)

---

## Proetale/Topology/LocalProperties.lean

### Sorry 1: Line 95 (Injectivity of colimit descent)
**Status:** BLOCKED - Missing sheaf descent infrastructure
**Blocker:** Requires glue lemmas between concrete category theory, sheaf amalgamation, and colimit preservation
**Session 3 analysis:** This is sheaf descent for colimits - proving that if F restricted to each member of a covering preserves colimits, then F preserves colimits. Requires 50-100+ lines of infrastructure connecting:
  - Concrete category structure on sheaves
  - Sheaf property (hom_ext, amalgamation)
  - Colimit preservation in presheaves vs sheaves
  - Pullback functors and colimit preservation
**Recommendation:** Accept as Mathlib gap or substantial infrastructure development. Check if lemma is actually needed downstream.

### Sorry 2: Line 98 (Surjectivity of colimit descent)
**Status:** BLOCKED - Same as Sorry 1
**Blocker:** Same infrastructure gap as injectivity case

---

## Proetale/Topology/SpectralSpace/ConnectedComponent.lean

### Sorry 1: Line 308 (Fiber preconnectedness)
**Status:** BLOCKED - Missing Mathlib infrastructure
**Blocker:** Need lemma showing continuous preimage of connected sets is preconnected, or explicit fiber homeomorphism construction using pullback universal property
**Session 3 analysis:** Attempted to show fiber `g⁻¹{t}` is preconnected by proving it's contained in `f⁻¹(connectedComponent(f y))`. Failed because:
  - `IsPreconnected s → t ⊆ s → IsPreconnected t` is FALSE in general
  - `IsConnected s → Continuous f → IsPreconnected (f ⁻¹' s)` exists only with additional conditions (f open/closed + injective)
**Recommendation:** Accept as Mathlib gap or prove missing fiber homeomorphism infrastructure (20-50 lines)

---

## Proetale/Mathlib/Topology/Connected/TotallyDisconnected.lean

### Sorry 1: Line 77 (Product of quotient maps)
**Status:** BLOCKED - Missing Mathlib infrastructure
**Blocker:** Product of quotient maps is NOT generally a quotient map. Requires additional conditions (open maps, local compactness, or sophisticated proof). ConnectedComponents.mk is not generally open.
**Note:** This is a known mathematical fact that should be in Mathlib

---

## Proetale/Mathlib/RingTheory/Localization/Prod.lean

### Sorry 1: Line 22 (prodTopEquiv)
**Status:** BLOCKED - Mathematical statement issue
**Blocker:** Current statement is mathematically impossible. For `(s,t)` with `s ∉ q`, the image `(algebraMap s, t)` must be a unit in product ring, but `t` is not necessarily a unit in `T`.
**Required fix:** Consult blueprint and revise statement (possibly `(S × T)_{q.prod ⊤} ≃ S_q × Tˣ` or different formulation)
**Session 3 analysis:** Helper lemma `primeCompl_prod_top` proved successfully, but main theorem needs statement correction

---

## Proetale/Mathlib/RingTheory/Henselian.lean

### Sorry 1: Lines ~310-320 (henselization_jointly_surjective - 3 sub-sorries)
**Status:** IN PROGRESS - Decomposed into sub-problems
**Sub-sorries:** (1) IsFiltered for étale algebras, (2) PreservesFilteredColimits for forget₂, (3) PreservesColimit composition
**Estimated complexity:** 50-100 lines per sub-sorry

### Sorry 2: Line 495 (henselization_of_quotient_is_henselian)
**Status:** NOT STARTED - Requires descent theory
**Estimated complexity:** 100-200 lines

---

## Proetale/Mathlib/RingTheory/Ideal/GoingDown.lean

### Sorry 1: Line 49 (localization_bijective_of_subsingleton)
**Status:** BLOCKED - Needs divisibility lemma (Session 11)
**Root cause:** Found correct approach via `IsLocalization.iff_of_le_of_exists_dvd`, but needs to prove divisibility condition

**Session 11 findings:**
- ✅ Correct approach identified: Use `IsLocalization.iff_of_le_of_exists_dvd`
- ✅ Proved containment: `algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl`
- ❌ Need to prove: `∀ s ∈ q.primeCompl, ∃ r ∈ algebraMapSubmonoid S p.primeCompl, s ∣ r`
- This divisibility should follow from uniqueness hypothesis (q is unique prime lying over p)

**Required fix:** Prove divisibility lemma using uniqueness (40-60 lines) OR construct explicit ring isomorphism (50-80 lines)

**Stacks reference:** 00EA (mathematical content is correct)

**Compilation status:** File does NOT compile (type class synthesis error at line 52)
**Recommendation:** Accept as Mathlib gap OR assign with explicit task to prove divisibility lemma first

---

## Proetale/Mathlib/CategoryTheory/MorphismProperty/Ind.lean

### Sorry 1: Line 163 (op_isFinitelyPresentable)
**Status:** BLOCKED - Categorical infrastructure missing
**Blocker:** For `f : X ⟶ Y` in `Cᵒᵖ`, LHS uses `Under Y.unop` while RHS uses `Under X` - different base objects, no direct equivalence exists
**Impact:** Blocks all 6 sorries in IndZariski.lean
**Recommendation:** Accept as sorry or Mathlib PR - mathematically obvious but technically intricate
**Session 3 analysis:** Attempted direct equivalence and coyoneda approaches, both failed due to fundamental categorical mismatch

---

## Proetale/Mathlib/CategoryTheory/MorphismProperty/IndSpreads.lean

### Sorry 1: Line 99 (IsStableUnderComposition for ind P)
**Status:** RESOLVED in session 3 ✓
**Resolution:** Used Mathlib's correct assumptions in section `WithFinitelyPresentable`

---

## Proetale/Topology/Flat/CompactOpenCovered.lean

### Sorry 1: Line 36 (comp - composition of compact-open covers)
**Status:** MATHEMATICAL IMPOSSIBILITY - Statement needs revision
**Issue:** Lemma requires preimages of compact opens to be compact, but this fails without additional assumptions (proper maps, compact spaces, or spectral structure)
**Recommendation:** Add assumption `IsProperMap (g i k)` or `CompactSpace (Y i k)`, or accept as sorry

---

## Proetale/Topology/Comparison/Etale.lean

### Sorry 1: Line 70 (isIso_unit_sheafAdjunction)
**Status:** BLOCKED - Needs category assumptions
**Issue:** Result proven for `A = Ab.{u + 1}` (line 55 instance exists), but general case for arbitrary category `A` requires additional assumptions about limits/colimits and concrete category structure
**Recommendation:** Either specialize to `Ab.{u + 1}` or add typeclass assumptions to `A`, or accept as sorry (requires 100+ lines following blueprint proof via affine étale schemes + filtered colimits)

---

## Proetale/Topology/Coherent/Affine.lean

### Sorry 1: Line 226 (EffectiveEpi → Surjective in CostructuredArrow)
**Status:** FUNDAMENTAL INFRASTRUCTURE GAP
**Issue:** Requires showing effective epis in costructured arrow category correspond to surjective morphisms. True for `P = @Etale` but not for arbitrary morphism properties without additional assumptions.

### Sorry 2: Line 241 (Surjective → EffectiveEpi in Over category)
**Status:** FUNDAMENTAL INFRASTRUCTURE GAP
**Issue:** Requires showing surjective morphisms are effective epis. True for `P = @Etale` (via `Scheme.Etale.effectiveEpi_of_surjective`) but not for general `P`.

**Note:** File compiles successfully. Instances work despite sorries. Comments acknowledge these are "non-trivial in general." Recommend accepting as infrastructure gaps or restricting to `P = @Etale`.

---

## Proetale/Topology/Comparison/Affine.lean

### Status: BLOCKED - Dependency compilation error
**Blocker:** Cannot compile due to errors in `Proetale/Mathlib/AlgebraicGeometry/Sites/Small.lean` (lines 42, 47)
**Sorries:** 11 sorries related to affine pro-étale site (PreservesOneHypercovers, LocallyCoverDense, IsCoverDense, HasPullbacks, isSheaf, baseChange, IsGenerating)
**Action needed:** Fix Small.lean before working on Affine.lean

---
