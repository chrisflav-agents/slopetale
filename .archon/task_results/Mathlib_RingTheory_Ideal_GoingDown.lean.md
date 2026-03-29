# Proetale/Mathlib/RingTheory/Ideal/GoingDown.lean

## localization_bijective_of_subsingleton (line 18)

### Attempt 1
- **Approach:** Use `IsLocalization.of_le_of_exists_dvd` to show the two submonoids generate the same localization
- **Result:** BLOCKED - Fundamental direction mismatch
- **Key insight:** Found `IsLocalization.of_le_of_exists_dvd` but it goes in the wrong direction
- **Progress:**
  - ✅ Proved containment: `algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl`
  - ✅ Proved `q + ⟨s⟩ = ⊤` for `s ∉ q` using going-down and uniqueness
  - ❌ **FUNDAMENTAL BLOCKER:** `IsLocalization.of_le_of_exists_dvd` requires `M ≤ N` and proves `IsLocalization N S` from `IsLocalization M S`. But we need the reverse: we have `IsLocalization q.primeCompl` and need `IsLocalization (algebraMapSubmonoid S p.primeCompl)` where the latter is smaller.

### Mathematical Analysis

**The Problem:**
Given:
- `R`, `S` commutative rings with `Algebra R S`
- Going-down property: `Algebra.HasGoingDown R S`
- Prime ideals `p ⊆ R`, `q ⊆ S` with `q` lying over `p`
- Uniqueness: For any prime `p'` in `R`, there's at most one prime in `S` lying over `p'`

Need to prove: `IsLocalization (algebraMapSubmonoid S p.primeCompl) (Localization.AtPrime q)`

**Why it's blocked:**
The fundamental issue is a direction mismatch:
- We have: `IsLocalization q.primeCompl (Localization.AtPrime q)` (by definition)
- We need: `IsLocalization (algebraMapSubmonoid S p.primeCompl) (Localization.AtPrime q)`
- We proved: `algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl`

Mathlib's `IsLocalization.of_le_of_exists_dvd` goes from smaller to larger submonoid (M ≤ N), but we need the reverse direction.

**What was accomplished:**
1. ✅ Proved `q + ⟨s⟩ = ⊤` for any `s ∉ q` using going-down and uniqueness (40 lines)
2. ✅ This is a non-trivial result showing the uniqueness hypothesis has strong consequences
3. ✅ File compiles with 1 sorry

**Missing infrastructure:**
Mathlib lacks a lemma like:
```lean
theorem IsLocalization.of_ge {M N : Submonoid R} [IsLocalization N S]
    (h : M ≤ N) : IsLocalization M S
```

Or equivalently, a characterization that two submonoids generate the same localization when one contains the other and they have the same "saturation" with respect to divisibility.

### Recommendation

This sorry requires either:
1. **Mathlib PR:** Add `IsLocalization.of_ge` or similar reverse direction lemma (10-20 lines)
2. **Alternative proof:** Construct an explicit ring isomorphism between the two localizations (80-100 lines)
3. **Accept as infrastructure gap:** The mathematical content (Stacks 00EA) is correct

### Next Steps

For the next session:
1. Check if there's an alternative Mathlib lemma for the reverse direction
2. Consider proving the ring isomorphism directly using universal properties
3. Or accept this as a fundamental Mathlib gap requiring upstream contribution

### Compilation Status
✅ File compiles with 1 sorry at line 18

### Relevant Lemmas Found
- `IsLocalization.of_le_of_exists_dvd` - goes in wrong direction (M ≤ N)
- `Ideal.disjoint_primeCompl_of_liesOver` - disjointness of complements
- `Ideal.exists_ideal_le_liesOver_of_le` - going-down property
- `Ideal.add_eq_one_iff` - ideal sum characterization

