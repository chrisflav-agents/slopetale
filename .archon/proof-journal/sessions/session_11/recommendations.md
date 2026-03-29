# Session 11 Recommendations

## Immediate Priority: GoingDown.lean (HIGH CONFIDENCE)

**Target:** `Proetale/Mathlib/RingTheory/Ideal/GoingDown.lean:23` (localization_bijective_of_subsingleton)

**Status:** 95% complete - only one helper lemma remains

**Why prioritize:**
- Proof structure is complete and validated
- File compiles cleanly
- Mathematical approach is clear
- Only 40-60 lines of work remaining
- Session 10 blocker was resolved by finding `IsLocalization.iff_of_le_of_exists_dvd`

**What to do:**
Prove the divisibility helper lemma:
```lean
lemma divisibility_from_uniqueness (n : S) (hn : n ∈ q.primeCompl) :
    ∃ m ∈ algebraMapSubmonoid S p.primeCompl, n ∣ m
```

**Proof strategy:**
1. Assume for contradiction that no such `m` exists
2. Use going-down to find a prime `q'` containing `n` and lying over `p`
3. Apply uniqueness hypothesis: `q' = q`
4. Contradiction: `n ∈ q` but `n ∈ q.primeCompl`

**Key lemmas to use:**
- `Ideal.exists_le_prime_disjoint`: Find prime containing element disjoint from submonoid
- `Algebra.HasGoingDown.exists_ideal_le_liesOver_of_le`: Going-down property
- `Subsingleton.elim`: Uniqueness of primes lying over p

**Estimated effort:** 40-60 lines

---

## Accept as Sorry (Do NOT Assign)

### WContractible.lean (4 sorries)
**Reason:** Confirmed infrastructure gaps requiring 100-200+ lines each. File compiles successfully.

### Other Known Blockers
See PROJECT_STATUS.md for full list of 15 documented blockers across 9 files.

---

## Survey Needed (Medium Priority)

The recent commit modified 17 files with 203 insertions and 165 deletions. Survey these files for new unblocked sorries:

1. Proetale/Algebra/IndEtale.lean
2. Proetale/Algebra/IndZariski.lean
3. Proetale/Algebra/WLocalization/Ideal.lean
4. Proetale/Mathlib/Algebra/Category/CommAlgCat/Limits.lean
5. Proetale/Mathlib/AlgebraicGeometry/Sites/Small.lean
6. Proetale/Mathlib/CategoryTheory/MorphismProperty/Ind.lean
7. Proetale/Mathlib/CategoryTheory/MorphismProperty/IndSpreads.lean
8. Proetale/Mathlib/RingTheory/Henselian.lean
9. Proetale/Mathlib/RingTheory/Localization/Prod.lean
10. Proetale/Mathlib/Topology/Connected/TotallyDisconnected.lean
11. Proetale/Mathlib/Topology/QuasiSeparated.lean
12. Proetale/Topology/Coherent/Affine.lean
13. Proetale/Topology/Flat/CompactOpenCovered.lean
14. Proetale/Topology/SpectralSpace/ConnectedComponent.lean

**Action:** Check each file for sorries that are not in the known blockers list.

---

## Proof Pattern Discovered

**Pattern:** IsLocalization bidirectional equivalence via divisibility

**When:** Need to prove `IsLocalization M S` where you have `IsLocalization N S` and `M ⊆ N`

**Technique:** Use `IsLocalization.iff_of_le_of_exists_dvd`:
- Prove `M ≤ N`
- Prove `∀ n ∈ N, ∃ m ∈ M, n ∣ m`
- Apply `.mpr` to transfer from `IsLocalization N S` to `IsLocalization M S`

**Key insight:** This is superior to constructing isomorphisms or proving IsLocalization from scratch. The divisibility condition is often provable using uniqueness or going-down properties.

**Application:** GoingDown session 11

**Status:** Validated, ready for reuse
