# Session 10 Recommendations

## Critical Finding: GoingDown Blocker Identified

Session 10 identified the precise blocker for `GoingDown.lean:18` (localization_bijective_of_subsingleton):

**Root cause:** Mathlib has `IsLocalization.of_le` to extend from smaller to larger submonoid (M ≤ N), but lacks the reverse direction. We need to restrict from `IsLocalization q.primeCompl` to `IsLocalization (algebraMapSubmonoid S p.primeCompl)` where the latter is contained in the former.

**Mathematical content:** The Stacks Project proof (00EA) is correct - under going-down with uniqueness, the two localizations are equal. The issue is purely a Lean/Mathlib formalization gap.

## Immediate Actions for Plan Agent

### DO NOT ASSIGN (Blocked)
1. **GoingDown.lean:18** - Blocked on Mathlib gap (IsLocalization direction)
2. **WContractible.lean** - All 4 sorries are 100-200+ line infrastructure gaps
3. All other known blockers from PROJECT_STATUS.md

### DO ASSIGN (High Priority)
Survey the 14 modified files from recent commit for new unblocked sorries:
- Proetale/Algebra/IndEtale.lean
- Proetale/Algebra/IndZariski.lean (check if Ind.lean blocker resolved)
- Proetale/Algebra/WLocalization/Ideal.lean
- Proetale/Mathlib/Algebra/Category/CommAlgCat/Limits.lean
- Proetale/Mathlib/AlgebraicGeometry/Sites/Small.lean
- Proetale/Mathlib/CategoryTheory/MorphismProperty/IndSpreads.lean
- Proetale/Mathlib/RingTheory/Henselian.lean
- Proetale/Mathlib/RingTheory/Localization/Prod.lean
- Proetale/Mathlib/Topology/Connected/TotallyDisconnected.lean
- Proetale/Mathlib/Topology/QuasiSeparated.lean
- Proetale/Topology/Coherent/Affine.lean
- Proetale/Topology/Flat/CompactOpenCovered.lean
- Proetale/Topology/SpectralSpace/ConnectedComponent.lean

## Options for GoingDown Blocker

### Option 1: Prove IsLocalization.of_ge (Recommended)
**Effort:** 30-50 lines
**Approach:** Prove a lemma that restricts IsLocalization from larger to smaller submonoid when the smaller submonoid's elements are already units.

**Signature:**
```lean
theorem IsLocalization.of_ge {R : Type*} [CommSemiring R] (M N : Submonoid R)
    {S : Type*} [CommSemiring S] [Algebra R S]
    [IsLocalization N S] (h : M ≤ N) : IsLocalization M S := ...
```

**Strategy:** Use that every element of M is a unit (via h and IsLocalization N), then apply the universal property.

### Option 2: Construct Isomorphism
**Effort:** 40-60 lines
**Approach:** Prove the two localizations are isomorphic as rings, then transfer the IsLocalization instance.

### Option 3: Accept as Sorry
**Effort:** 0 lines
**Approach:** Document as Mathlib gap and move on. The mathematical content is sound.

## Proof Patterns Discovered

### Pattern: IsLocalization Direction Matters
**When:** Working with IsLocalization and submonoid containment
**Key insight:** `IsLocalization.of_le` only goes from smaller to larger (M ≤ N). There is no reverse direction in Mathlib.
**Workaround:** May need to construct IsLocalization directly or prove custom lemma.

## Session Statistics
- **Sorry count:** 55 → 55 (no change)
- **Targets attempted:** 2
- **Blockers identified:** 1 (GoingDown Mathlib gap)
- **Blockers resolved:** 0

## Next Session Priority

1. **Survey modified files** - Check 14 files for new opportunities
2. **Consider GoingDown options** - Decide whether to attempt Option 1 or accept as sorry
3. **Avoid known blockers** - Do not retry WContractible or other documented blockers
