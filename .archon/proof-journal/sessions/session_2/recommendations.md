# Recommendations for Next Plan Iteration

## Priority 1: Infrastructure Work (Required Before Resuming Blocked Targets)

### 1.1 Prove IsStableUnderComposition for ind
**File:** `Proetale/Mathlib/CategoryTheory/MorphismProperty/IndSpreads.lean:99`
**Blocks:** IndEtale.of_indEtale_etale
**Difficulty:** Medium
**Approach:** The sorry at line 99 needs to be filled. This should follow from the definition of ind and the fact that composition of filtered colimits preserves the ind property.

### 1.2 Prove ind Idempotence
**New lemma needed:** `ind (ind P) = ind P` for properties P ≤ finitely presentable
**Blocks:** 3 sorries in IndZariski.lean (of_colimitPresentation, iff_ind_indZariski, iff_ind_indZariksi)
**Difficulty:** Medium-Hard
**Approach:** This is a general categorical fact about ind constructions. May require proving that IsLocalIso is bounded by finitely presentable objects.

### 1.3 Prove CompatiblePreserving for Over.changeProp
**New lemma needed:** `CompatiblePreserving (smallGrothendieckTopology Q) (Over.changeProp S hPQ le_rfl)`
**Blocks:** AlgebraicGeometry/Sites/Small.changeProp_isContinuous
**Difficulty:** Easy-Medium
**Approach:** Should be straightforward since `changeProp` with `le_rfl` acts as identity on morphisms: `(F.map g).hom = g.hom`. Prove that identity-like functors preserve compatibility.

### 1.4 Prove Composition and Preservation for ind
**New lemmas needed:**
- Composition of ind properties via scalar towers
- BijectiveOnStalks preserved by filtered colimits
**Blocks:** IndZariski.trans, IndZariski.bijectiveOnStalks_algebraMap
**Difficulty:** Medium
**Approach:** Use that filtered colimits preserve various properties. For composition, use that IsLocalIso.comp exists and lift through the ind construction.

### 1.5 General Localization is ind-Zariski
**New lemma needed:** `IsLocalization M S → IsLocalIso R S` for general submonoid M
**Blocks:** IndZariski.of_isLocalization
**Difficulty:** Medium-Hard
**Approach:** Either prove directly that general localization is a local isomorphism, or show that any localization can be written as a filtered colimit of Away localizations (which are known to be local isomorphisms).

## Priority 2: Targets Requiring Local-to-Global Principles

### 2.1 WLocalization/Ideal.quotientMap_algebraMap_bijective
**File:** Proetale/Algebra/WLocalization/Ideal.lean:378
**Difficulty:** Hard
**Approach:** The base map `algebraMap A I.WLocalization` is NOT globally surjective (it's ind-Zariski). Need to prove the quotient map is bijective using:
- Local surjectivity (surjective on stalks) + `surjective_of_localized_maximal`
- Or BijectiveOnStalks + Spec bijection (but this may be circular)
- Or prove a new helper lemma about quotient surjectivity from local properties

**Recommendation:** Defer until after ind infrastructure is complete, as the proof may become clearer with better ind lemmas available.

## Priority 3: Targets Ready After Infrastructure

Once the infrastructure work in Priority 1 is complete, the following targets should be immediately assignable:

1. **IndEtale.of_indEtale_etale** - unblocked by 1.1
2. **IndZariski.of_colimitPresentation** - unblocked by 1.2
3. **IndZariski.iff_ind_indZariski** - unblocked by 1.2
4. **IndZariski.iff_ind_indZariksi** - unblocked by 1.2
5. **IndZariski.trans** - unblocked by 1.4
6. **IndZariski.bijectiveOnStalks_algebraMap** - unblocked by 1.4
7. **IndZariski.of_isLocalization** - unblocked by 1.5
8. **AlgebraicGeometry/Sites/Small.changeProp_isContinuous** - unblocked by 1.3

## Reusable Proof Patterns

### Pattern 1: Direct Limit Characterization
**Use case:** Proving properties of ideals or modules
**Technique:** Express object as direct limit of FG sub-objects, use that operations commute with direct limits
**Example:** WeakDimension.all_ideals_flat

### Pattern 2: Component-wise Factorization
**Use case:** Product ring homomorphisms
**Technique:** Show stalks at special primes factor through individual components
**Example:** StalkIso.prod lemmas

### Pattern 3: Localization Decomposition
**Use case:** Explicit computation with localized elements
**Technique:** Use `IsLocalization.mk'_surjective` to write elements as fractions
**Example:** StalkIso.prod surjectivity proofs

## Do NOT Assign (Blocked)

The following targets should NOT be assigned to provers until the infrastructure work is complete:
- All 6 sorries in IndZariski.lean
- IndEtale.of_indEtale_etale
- WLocalization/Ideal.quotientMap_algebraMap_bijective
- AlgebraicGeometry/Sites/Small.changeProp_isContinuous

## Suggested Next Steps

1. Create infrastructure tasks for Priority 1 items (1.1-1.5)
2. Assign these to provers with category theory expertise
3. Once infrastructure is complete, reassign the blocked targets
4. Consider WLocalization/Ideal task only after ind infrastructure is solid
