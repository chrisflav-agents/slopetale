# Session 4 Recommendations

## Priority Targets for Next Session

### HIGH PRIORITY - Ready for Implementation

#### 1. Proetale/Algebra/WContractible.lean - exists_retraction_of_bijectiveOnStalks (line 456)
**Status:** Partial progress, clear path forward

**Why prioritize:**
- Blueprint proof outline is complete and clear
- All key infrastructure exists and compiles (WLocal.lean has 0 sorries)
- Step 1 already complete (surjectivity proved)
- Estimated 50-100 lines remaining

**Next steps:**
1. Apply `CompactT2.Projective` to get section σ: π₀(Spec R) → π₀(Spec S)
2. Define T = Set.range σ, prove it's closed
3. Instantiate `Restriction T` for ring S
4. Prove S_T is w-local (may need helper lemma)
5. Verify R → S_T satisfies `bijective_of_bijective` hypotheses
6. Extract retraction S → R

**Key lemmas available:**
- `CompactT2.ExtremallyDisconnected.projective`
- `Restriction.indZariski`
- `Restriction.algebraMap_surjective`
- `RingHom.IsWLocal.bijective_of_bijective`

---

### MEDIUM PRIORITY - Requires Infrastructure

#### 2. Proetale/Mathlib/RingTheory/Ideal/GoingDown.lean - localization_bijective_of_subsingleton (line 18)
**Status:** Partial progress, needs infrastructure

**Why medium priority:**
- Partial progress made (condition 1 complete, condition 2 partial)
- Requires 50-100+ lines of new infrastructure
- Mathlib gap: no lemmas for restricting IsLocalization to smaller submonoid

**Approaches to consider:**
1. **Consult Stacks 00EA:** Read the original proof carefully to understand how uniqueness is used
2. **Prove auxiliary lemmas:** About submonoid relationships under uniqueness hypothesis
3. **Alternative characterization:** Find different way to show localizations coincide
4. **Accept as sorry:** Document as Mathlib gap

**If attempting:** Focus on understanding how uniqueness hypothesis allows elements of q.primeCompl not in image of p.primeCompl to be expressed via smaller submonoid.

---

### LOW PRIORITY - Accept as Blockers

#### 3. Proetale/Topology/Coherent/Affine.lean - Preregular sorries (lines 226, 241)
**Status:** Blocked - fundamental infrastructure gap

**Recommendation:** **Accept as sorry**

**Rationale:**
- Comments explicitly acknowledge "non-trivial in general"
- Properties hold for specific P (like Etale) but not arbitrary morphism properties
- File compiles successfully, instances work despite sorries
- Would require 50-100+ lines of categorical infrastructure
- Better suited for Mathlib contribution

**If upstream requires:** Should be addressed as part of broader Mathlib work on costructured arrow categories and morphism properties.

---

#### 4. Proetale/Topology/Flat/CompactOpenCovered.lean - comp (line 36)
**Status:** Blocked - statement issue

**Recommendation:** **Revise statement before attempting**

**Issue:** Mathematically impossible with only surjectivity assumption. Preimages of compact sets under continuous maps are not necessarily compact without additional structure.

**Required fixes (choose one):**
1. Add proper map assumption: `(hgp : ∀ i k, IsProperMap (g i k))`
2. Add compact space assumption: `[∀ i k, CompactSpace (Y i k)]`
3. Add spectral/prespectral structure assumptions
4. Weaken conclusion to only require images cover U

**Action:** Consult blueprint or upstream to determine intended statement.

---

## Proof Patterns Discovered

### Pattern 1: Localization Restriction Problem
**Context:** Proving IsLocalization for smaller submonoid when you have it for larger submonoid

**Gap:** Mathlib lemmas all go opposite direction (extending to larger submonoid)

**Workaround:** Direct proof via `isLocalization_iff` - prove three conditions (units, surjectivity, injectivity) separately

**Reusable for:** Similar localization problems where submonoids have containment relationship

---

### Pattern 2: Projectivity for Lifting
**Context:** Constructing sections/retractions using topological projectivity

**Key lemmas:**
- `CompactT2.Projective`: Lifting property for compact T2 spaces
- `CompactT2.ExtremallyDisconnected.projective`: Extremally disconnected spaces are projective

**Application:** When you have surjective map and need to construct section, check if domain is extremally disconnected compact T2

**Reusable for:** Other retraction/section construction problems in topological settings

---

## Known Blockers - Do Not Retry

### 1. op_isFinitelyPresentable (from session 3)
**File:** Proetale/Mathlib/CategoryTheory/MorphismProperty/Ind.lean:163

**Issue:** Under categories have different base objects after taking opposites - fundamental categorical mismatch

**Impact:** Blocks 6 sorries in IndZariski.lean

**Status:** Accept as Mathlib gap or candidate for Mathlib PR

---

### 2. Coherent/Affine Preregular sorries
**File:** Proetale/Topology/Coherent/Affine.lean:226, 241

**Issue:** Properties don't hold for arbitrary morphism properties

**Status:** Accept as documented infrastructure gap

---

### 3. CompactOpenCovered comp
**File:** Proetale/Topology/Flat/CompactOpenCovered.lean:36

**Issue:** Statement mathematically impossible with current assumptions

**Status:** Needs statement revision before attempting

---

## Session Metrics Summary

- **Targets attempted:** 4
- **Resolved:** 0
- **Partial progress:** 2 (WContractible, GoingDown)
- **Blocked:** 2 (Coherent/Affine, CompactOpenCovered)
- **Promising for next session:** 1 (WContractible)

## Recommended Focus

**Next session should prioritize:** `exists_retraction_of_bijectiveOnStalks` in WContractible.lean

This target has the highest probability of completion with all infrastructure in place and clear implementation path.
