# Session 5 Recommendations

## For Plan Agent - Session 6 Priorities

### HIGH PRIORITY: Complete WContractible (40-80 lines remaining)

**Target:** `Proetale/Algebra/WContractible.lean:454` - `exists_retraction_of_bijectiveOnStalks`

**Status:** Proof skeleton complete. 4 routine sorries remain.

**Sorries to fill:**
1. Line 489: `IsWLocalRing S_T` - Prove Restriction preserves w-local structure (10-20 lines)
2. Line 498: `IsWLocal (algebraMap R S_T)` - Composition of w-local maps (10-20 lines)
3. Line 499: Connected components injectivity - Use `hrange` (10-20 lines)
4. Line 500: Connected components surjectivity - Use `hσ` (10-20 lines)

**Why prioritize:**
- Main structural work complete (session 5 breakthrough)
- All infrastructure exists
- Each sorry is well-scoped and routine
- Highest-value target (resolves 4 sorries, completes major theorem)

**Approach:**
- Search for w-local preservation lemmas for ind-Zariski maps
- Use composition lemmas for IsWLocal
- For π₀ bijection: leverage `hrange : Spec(S_T) = mk⁻¹'T` and `hσ : T → π₀(R) surjective`

---

### MEDIUM PRIORITY: Accept Small.lean as Infrastructure Gap

**Target:** `Proetale/Mathlib/AlgebraicGeometry/Sites/Small.lean:23`

**Status:** Blocked by typeclass resolution issue

**Recommendation:** Accept the 1 remaining sorry as infrastructure gap. The mathematical content is trivial (changeProp with le_rfl is essentially identity), but formal proof hits metavariable resolution in RepresentablyFlat for comma categories.

**Rationale:**
- CoverPreserving complete (75% reduction from 4 to 1 sorry)
- File compiles cleanly
- Blocker is technical typeclass issue, not mathematical gap
- Time better spent on WContractible

---

### LOW PRIORITY: Other Targets

**Do NOT assign these without addressing blockers:**
- GoingDown.lean:18 - Needs 50-100 lines of localization infrastructure
- Coherent/Affine.lean:226,241 - Accept as infrastructure gap (documented in session 4)
- CompactOpenCovered.lean:36 - Statement issue (needs revision)
- Ind.lean:163 - Categorical blocker (blocks 6 IndZariski sorries)

---

## Proof Patterns Discovered

### Pattern: Projectivity for Section Construction

**When:** Need to construct continuous section of surjective map between compact T2 spaces

**Technique:** Use `CompactT2.Projective` when domain is extremally disconnected

**Key lemmas:**
- `CompactT2.Projective`: Lifting property
- `CompactT2.ExtremallyDisconnected.projective`: Extremally disconnected ⇒ projective

**Application:** WContractible session 5 (lines 465-471)

### Pattern: Restriction Construction for Closed Subsets

**When:** Need to localize at closed subset T ⊆ π₀(Spec A)

**Technique:** Use `Restriction T` colimit construction

**Key lemmas:**
- `Restriction.indZariski`: A → Restriction T is ind-Zariski
- `Restriction.range_algebraMap_specComap`: Spec(Restriction T) = mk⁻¹'T

**Application:** WContractible session 5 (lines 473-487)

---

## Session 6 Action Items

1. **Assign WContractible to prover** - Complete 4 remaining sorries (estimated 40-80 lines)
2. **Accept Small.lean sorry** - Document as infrastructure gap, move to "blocked" list
3. **Update task_done.md** - Mark Small.lean as "partial completion" (4→1 sorry)
4. **Avoid reassigning blocked targets** - Focus resources on completable work

---

## Metrics to Track

- **WContractible completion:** Target for session 6
- **Sorry count:** Should decrease by 4 if WContractible completes
- **Blocked targets:** Currently 13 sorries across 7 files (documented with reasons)
