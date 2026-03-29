# Session 9 Recommendations

## Immediate Priorities

### 1. Complete GoingDown.lean (HIGH PRIORITY - 95% done)
**File:** Proetale/Mathlib/RingTheory/Ideal/GoingDown.lean
**Status:** 1 sorry remaining (line 42)
**Effort:** 5-30 lines

**What's needed:**
Prove the disjoint lemma:
```lean
Disjoint (↑(Ideal.span {n}) : Set S) (Algebra.algebraMapSubmonoid S p.primeCompl)
```
where `n ∉ Algebra.algebraMapSubmonoid S p.primeCompl`.

**Approaches to try:**
1. **Search Mathlib** for lemmas about:
   - `Submonoid.closure` and disjointness
   - `algebraMapSubmonoid` properties
   - Ideal span disjoint from submonoid

2. **Extract as helper lemma** in separate file (recommended):
   - Create `Proetale/Mathlib/Algebra/Submonoid/Disjoint.lean`
   - State general lemma: if `n ∉ Submonoid.closure S`, then `Ideal.span {n}` is disjoint from `S`
   - Import and use in GoingDown.lean

3. **Direct proof** showing that if `a * n ∈ algebraMapSubmonoid` for some `a`, derive contradiction

**Why prioritize:** Only 1 sorry left, proof structure validated, high-value theorem for downstream work.

---

## Medium Priority Targets

### 2. WContractible.lean sorries (4 remaining)
**File:** Proetale/Algebra/WContractible.lean
**Status:** Compilation fixed in session 8, surjectivity infrastructure complete from session 6
**Effort:** Variable (1 is stubbed infrastructure, 3 are proof sorries)

**Sorries:**
- Line 362: Z definition (stubbed - requires 150-200 lines of profinite infrastructure)
- Lines 400+: Remaining proof sorries using session 6 infrastructure

**Recommendation:** Focus on the 3 proof sorries first, leave Z definition stub for later.

---

## Research Tasks

### 3. Survey modified files for new opportunities
**Context:** Git diff shows 17 files modified with 234 insertions, 166 deletions
**Action:** Check if any of the 14 other modified files have unblocked sorries or new proof opportunities

**Files to check:**
- Proetale/Algebra/IndEtale.lean
- Proetale/Algebra/IndZariski.lean
- Proetale/Mathlib/CategoryTheory/MorphismProperty/IndSpreads.lean
- Proetale/Mathlib/RingTheory/Henselian.lean
- Others from git diff

---

## Known Blockers (Do NOT Assign)

### Opposite Category Preservation (Ind.lean:163)
Blocks 6 sorries in IndZariski.lean. Requires sophisticated categorical argument or Mathlib PR.

### Coherent/Affine Preregular (Affine.lean:226,241)
Accept as documented infrastructure gap. File compiles despite sorries.

### Small.lean Typeclass Resolution (Small.lean:23)
Typeclass metavariable resolution issue. Accept as infrastructure gap.

### CompactOpenCovered Statement (CompactOpenCovered.lean:36)
Statement mathematically impossible without additional assumptions. Needs blueprint consultation.

### Localization/Prod Statement (Prod.lean:29)
Statement mathematically impossible as written. Needs blueprint consultation.

---

## Proof Patterns Discovered

### Pattern: IsLocalization.of_le for submonoid extension
**When:** Need to show localization at smaller submonoid equals localization at larger submonoid
**Technique:** Use `@IsLocalization.of_le` with explicit type parameters
**Key insight:** Prove containment `M ≤ N`, then `IsLocalization M S` implies `IsLocalization N S`
**Application:** GoingDown session 9

### Pattern: Going-down + Uniqueness → Contradiction
**When:** Have going-down property and uniqueness of primes lying over p
**Technique:**
1. Assume element n not in desired set
2. Find prime q' containing n using `Ideal.exists_le_prime_disjoint`
3. Apply going-down to get q'' ≤ q' lying over p
4. Use uniqueness to show q'' = q
5. Derive contradiction from n ∈ q' and q ≤ q'
**Key lemmas:** `Ideal.exists_le_prime_disjoint`, `Ideal.exists_ideal_le_liesOver_of_le`, `Subsingleton.elim`
**Application:** GoingDown sessions 7, 8, 9

---

## Session 9 vs Session 8 Comparison

**Session 8:**
- 2 sorries in GoingDown.lean
- Blocked on comap contravariance issue
- Proof structure unclear

**Session 9:**
- 1 sorry in GoingDown.lean (50% reduction)
- Proof structure validated and simplified
- Only technical disjoint lemma remains
- Clear path to completion

**Net progress:** +1 sorry resolved, proof 95% complete

---

## Next Session Strategy

1. **Assign GoingDown completion** to a prover with instructions to:
   - Try Mathlib search for submonoid disjointness lemmas
   - If not found, extract helper lemma to separate file
   - Estimated 30-60 minutes to complete

2. **Assign WContractible proof sorries** (not the Z stub) to a prover

3. **Survey task** to check modified files for new opportunities

4. **Do NOT assign** any of the known blockers without new mathematical insights
