# Session 3 Recommendations

## Priority Actions for Next Session

### HIGH PRIORITY - Unblocked Targets

#### 1. IndEtale.lean:56 - NOW UNBLOCKED ✓
**Status:** Ready to work
**Reason:** `IsStableUnderComposition (ind P)` is now available (resolved in session 3)
**Approach:** Use the new instance to prove composition of ind-étale morphisms
**Estimated difficulty:** Medium
**Impact:** Unblocks 1 sorry

---

### MEDIUM PRIORITY - Statement Corrections Needed

#### 2. Localization/Prod.lean:29 - prodTopEquiv
**Status:** Requires statement revision
**Issue:** Current statement is mathematically impossible (elements don't map to units)
**Action:**
1. Consult blueprint to understand intended construction
2. Revise statement to one of:
   - `(S × T)_{q.prod ⊤} ≃ S_q × Tˣ` (product with unit group)
   - Different submonoid for localization
   - Alternative formulation
3. Once corrected, should be provable
**Impact:** 1 sorry (but needs clarification first)

---

### LOW PRIORITY - Mathlib Infrastructure Gaps

These targets are blocked by missing Mathlib infrastructure. Recommend deferring unless willing to invest in substantial infrastructure development.

#### 3. Ind.lean:163 - op_isFinitelyPresentable
**Blocker:** Categorical mismatch between Under categories with different base objects
**Impact:** Blocks 6 sorries in IndZariski.lean
**Options:**
- Accept as sorry (mathematically obvious, technically intricate)
- Mathlib PR to add this lemma
- Find alternative proof strategy for IndZariski sorries that doesn't require this
**Recommendation:** Accept as sorry for now, consider Mathlib PR later

#### 4. SpectralSpace/ConnectedComponent.lean:294 - lift_bijective_of_isPullback
**Blocker:** Missing fiber homeomorphism infrastructure for pullbacks
**Impact:** 2 sorries (injectivity + surjectivity)
**Options:**
- Prove missing infrastructure (20-50 lines)
- Accept as Mathlib gap
**Recommendation:** Accept as sorry unless this is critical path

#### 5. LocalProperties.lean:95,98 - preservesColimitsOfShape_of_cover
**Blocker:** Missing sheaf descent theory for colimits
**Impact:** 2 sorries
**Options:**
- Substantial infrastructure development (50-100+ lines)
- Accept as Mathlib gap
- Check if lemma is actually needed downstream
**Recommendation:** Accept as sorry, investigate if there's a workaround for downstream uses

---

## Proof Patterns Discovered

### Pattern 1: Using Mathlib's "Correct Assumptions"
**When:** Infrastructure lemmas with TODO comments about assumptions
**Technique:** Don't try to weaken assumptions - use exactly what Mathlib provides
**Example:** IndSpreads composition required full `IsFinitelyAccessibleCategory`, `HasPushouts`, etc.
**Lesson:** Trust Mathlib's design - the assumptions are there for a reason

---

## Targets to AVOID (Known Blockers)

Do NOT assign these in next planning iteration without addressing blockers first:

1. **Ind.lean:163** - Requires categorical infrastructure or Mathlib PR
2. **LocalProperties.lean:95,98** - Requires sheaf descent infrastructure
3. **SpectralSpace/ConnectedComponent.lean:294** - Requires fiber homeomorphism infrastructure
4. **Localization/Prod.lean:29** - Requires statement correction from blueprint

---

## Suggested Next Session Focus

### Option A: Continue with Unblocked Work
Focus on targets that don't require new infrastructure:
- IndEtale.lean:56 (now unblocked)
- Other sorries in files not yet attempted
- Review TASK_PLAN.md for additional targets

### Option B: Infrastructure Investment
If willing to invest time, prioritize:
1. **op_isFinitelyPresentable** (blocks 6 sorries) - highest leverage
2. Fiber homeomorphisms (blocks 2 sorries)
3. Sheaf descent (blocks 2 sorries, but may not be needed)

### Option C: Statement Clarification
- Consult blueprint for prodTopEquiv intended construction
- Correct statement and prove

**Recommendation:** Option A (continue with unblocked work) unless infrastructure is deemed critical.

---

## Search Strategy Insights

Session 3 used 127 lemma searches effectively:
- Semantic search (LeanSearch/LeanFinder) successfully identified relevant lemmas
- When searches returned no results, correctly concluded lemmas don't exist in Mathlib
- Avoided wasting time on repeated searches with minor rephrasing

**Lesson:** Trust negative search results - if high-quality semantic search finds nothing, the lemma likely doesn't exist.

---

## Compilation Health

All edited files compile cleanly (8/9 diagnostic checks clean, 1 error in unrelated file). This is excellent - continue this practice of verifying compilation after each change.
