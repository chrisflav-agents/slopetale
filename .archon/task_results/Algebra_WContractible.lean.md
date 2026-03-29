# Proetale/Algebra/WContractible.lean

## Status: All sorries are fundamental infrastructure gaps (400-600+ lines total)

### Compilation Status
✅ File compiles successfully with 4 sorries

### Sorry 1: Line 363 (Z definition)
**Status:** STUB - Added in Session 8 to fix compilation
**Blocker:** Requires `LocallyConnectedSpace (PrimeSpectrum A)` instance
**Infrastructure needed:**
- LocallyConnectedSpace instance for PrimeSpectrum
- Profinite pullback construction (150-200+ lines)
- Definition uses DiscreteQuotient and continuous maps to ConnectedComponents

**Blueprint reference:** def:modify-pi0-profinite
**Estimated effort:** 150-200+ lines
**Recommendation:** Accept as infrastructure gap

### Sorry 2: Line 432 (bijectiveOnStalks_of_indEtale_wStrictlyLocal)
**Status:** BLOCKED - Missing Mathlib theorem
**Blocker:** Requires formalization of thm:ind-etale-strictly-henselian-localization-isom

**Mathematical content (from blueprint line 1702-1712):**
- Let A be strictly Henselian local ring
- Let A → B be ind-étale
- Let n be maximal ideal of B lying over maximal ideal m of A
- Then A → B_n is an isomorphism

**Proof sketch:**
1. Write B = colim_i B_i as filtered colimit of étale A-algebras
2. Localization commutes with colimits: B_n = colim_i (B_i)_{n_i}
3. Apply thm:etale-over-strictly-henselian-localization-isom to each B_i
4. Each (B_i)_{n_i} ≅ A, so B_n ≅ A

**Missing infrastructure:**
- Need to formalize étale-over-strictly-henselian-localization-isom first
- Need lemmas about localization commuting with filtered colimits
- Need to track maximal ideals through colimit

**Estimated effort:** 100-150 lines
**Recommendation:** Accept as Mathlib gap or substantial project

### Sorry 3: Line 461 (exists_retraction_of_bijectiveOnStalks)
**Status:** BLOCKED - Depends on WLocal.lean sorry
**Blocker:** Depends on `RingHom.IsWLocal.bijective_of_bijective` (sorry'd in WLocal.lean)

**Mathematical content (from blueprint line 2101-2122):**
- Let A be w-local with π₀(Spec A) extremally disconnected
- Let A → B be faithfully flat, bijective on stalks, with B w-local
- Then A → B has a retraction

**Proof sketch (Stacks 09AZ):**
1. Closed points V(IB) → V(I) is surjective (from faithfully flat)
2. V(I) ≅ π₀(Spec A) is extremally disconnected (projective in CompHaus)
3. Get section σ: V(I) → V(IB) using projectivity
4. Image T ⊆ π₀(Spec B) is closed, maps homeomorphically to π₀(Spec A)
5. Use Restriction construction: B → B_T (surjective, ind-Zariski)
6. B_T is w-local, π₀(Spec B_T) ≅ T ≅ π₀(Spec A)
7. A → B_T identifies local rings and has matching π₀
8. Apply RingHom.IsWLocal.bijective_of_bijective: A ≅ B_T
9. Compose to get retraction

**Available infrastructure:**
- ✅ Restriction construction (lines 89-351) - fully formalized
- ✅ Extremally disconnected projectivity - exists in Mathlib
- ✅ range_algebraMap_specComap (line 207) - proved
- ✅ isClosedEmbedding_algebraMap_specComap (line 346) - proved

**Missing piece:**
- ❌ RingHom.IsWLocal.bijective_of_bijective (in WLocal.lean)
  - Statement: w-local map that is bijective and has π₀ isomorphism is an isomorphism
  - This is the key theorem connecting local structure to global structure

**Estimated effort:** 50-100 lines once dependency resolved
**Recommendation:** Work on WLocal.lean first, then return to this

### Sorry 4: Line 543 (exists_wContractibleCover)
**Status:** BLOCKED - Missing profinite Pullback infrastructure
**Blocker:** Requires colimit over DiscreteQuotient T

**Mathematical content (from blueprint, Stacks 0983):**
- Given w-strictly-local ring A
- Construct w-contractible cover D

**Construction:**
1. Let T = Ultrafilter(π₀(Spec A)) (extremally disconnected by Gleason)
2. Get surjection f: T → π₀(Spec A)
3. For each S: DiscreteQuotient T, construct Pullback S f (line 365)
4. Take D = colim_{S: DiscreteQuotient T} Pullback S f
5. Verify: D is ind-Zariski, faithfully flat, w-contractible

**Available infrastructure:**
- ✅ Pullback construction (lines 365-397) - defined
- ✅ Pullback.indZariski (line 389) - proved
- ✅ Pullback.bijectiveOnStalks_algebraMap (line 392) - proved
- ✅ Gleason's theorem - exists in Mathlib (StoneCech.projective)

**Missing infrastructure:**
- ❌ Colimit over DiscreteQuotient T
- ❌ Proof that colimit preserves ind-Zariski
- ❌ Proof that π₀(Spec D) = T
- ❌ Proof that D is w-local
- ❌ Proof that D is faithfully flat
- ❌ Proof that stalks at maximal ideals are strictly Henselian

**Estimated effort:** 150-200+ lines
**Recommendation:** Accept as infrastructure gap

## Summary

All 4 sorries in WContractible.lean are fundamental infrastructure gaps:
- Sorry 1: 150-200+ lines (profinite pullback)
- Sorry 2: 100-150 lines (Henselian localization theorem)
- Sorry 3: 50-100 lines (blocked by WLocal.lean)
- Sorry 4: 150-200+ lines (profinite colimit)

**Total estimated effort:** 450-650 lines

**Critical path:**
1. Sorry 2 requires formalizing missing Mathlib theorem about étale algebras over strictly Henselian rings
2. Sorry 3 requires completing WLocal.lean first
3. Sorries 1 and 4 require substantial categorical infrastructure

**Recommendation:** Accept all 4 sorries as infrastructure gaps. The file compiles successfully and the mathematical content is well-documented. These are not tractable for a single prover session.

## Next Steps

If forced to make progress:
1. **Best option:** Work on WLocal.lean's `RingHom.IsWLocal.bijective_of_bijective` first, then return to Sorry 3
2. **Alternative:** Attempt Sorry 2 by formalizing thm:ind-etale-strictly-henselian-localization-isom
3. **Not recommended:** Sorries 1 and 4 require too much infrastructure

However, per PROGRESS.md Session 12 plan, this file has been deprioritized in favor of files with smaller, more tractable sorries.
