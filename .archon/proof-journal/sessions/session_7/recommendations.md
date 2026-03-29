# Session 7 Recommendations

## Priority Actions for Plan Agent

### 1. Investigate Sorry Count Regression (URGENT)

**Issue:** Sorry count increased from 54 to 55 (net +1)

**Action:** Before assigning new tasks, identify which file gained a sorry:
```bash
git diff HEAD~1 --unified=0 | grep -E '^\+.*sorry|^-.*sorry'
```

**Possible causes:**
- Refactoring introduced new sorry
- File structure change exposed hidden sorry
- Compilation issue created temporary sorry

**Priority:** HIGH - understand regression before proceeding

### 2. Complete GoingDown.lean (20-30 lines remaining)

**Status:** Blocked at witness extraction step

**What's done:**
- Proved `q ⊔ Ideal.span {n} = ⊤` using going-down + uniqueness
- Established proof framework with `IsLocalization.iff_of_le_of_exists_dvd`

**What's needed:**
```lean
-- From htop : q ⊔ Ideal.span {n} = ⊤, extract witnesses
have : 1 ∈ q ⊔ Ideal.span {n} := by rw [htop]; trivial
obtain ⟨a, ha, b, hb, hab⟩ := ... -- use Ideal.mem_sup
-- hab : 1 = a + b * n, where a ∈ q, b ∈ S
-- Construct divisibility: n divides some element of algebraMapSubmonoid
```

**Recommendation:** Assign to prover with specific instruction to complete witness extraction only (not restart proof)

**Priority:** MEDIUM - mathematical approach is sound, just needs completion

### 3. Return to WContractible.lean (HIGH PRIORITY)

**Status:** Session 6 completed surjectivity infrastructure

**Remaining work:** 60-100 lines for section construction

**Why prioritize:**
- Clear path forward (surjectivity done)
- High-value target (4 sorries)
- Previous session made significant progress

**Recommendation:** Assign to prover for session 8

**Priority:** HIGH

## Proof Patterns Discovered

### Pattern: Going-Down + Uniqueness → Ideal Equality

**When:** Have going-down property and uniqueness of primes lying over p

**Technique:** To prove `q ⊔ Ideal.span {n} = ⊤` for `n ∉ q`:
1. Use `PrimeSpectrum.zeroLocus_empty_iff_eq_top` to reduce to showing no prime contains the ideal
2. For any prime q' containing q ⊔ Ideal.span {n}, apply going-down to get q'' ≤ q' lying over p
3. Use uniqueness to show q'' = q
4. Derive contradiction: n ∈ q' but n ∉ q = q'' ⊆ q'

**Key lemmas:**
- `PrimeSpectrum.zeroLocus_empty_iff_eq_top`
- `Ideal.exists_ideal_le_liesOver_of_le`
- `Subsingleton.elim`

**Application:** GoingDown session 7

### Pattern: Subsingleton.elim with Subtypes

**When:** Using uniqueness to prove equality of elements in subtype

**Issue:** Type structure must match exactly - pairs not triples

**Correct form:**
```lean
have : (⟨x, ⟨hx1, hx2⟩⟩ : {a : A // P a ∧ Q a}) =
       (⟨y, ⟨hy1, hy2⟩⟩ : {a : A // P a ∧ Q a}) :=
  Subsingleton.elim _ _
```

**Incorrect form:**
```lean
Subsingleton.elim ⟨x, hx1, hx2⟩ ⟨y, hy1, hy2⟩  -- Type mismatch
```

## Targets to Avoid

### Do Not Reassign (Blocked)

These targets remain blocked from previous sessions:

1. **Ind.lean:163** - Opposite category preservation (blocks 6 IndZariski sorries)
2. **Small.lean:23** - Typeclass resolution issue
3. **Coherent/Affine.lean:226,241** - Accept as infrastructure gap
4. **CompactOpenCovered.lean:36** - Statement issue
5. **Localization/Prod.lean:29** - Statement issue
6. **SpectralSpace/ConnectedComponent.lean:294** - Missing infrastructure
7. **LocalProperties.lean:95,98** - Missing infrastructure

## Session 8 Recommendations

### Option A: Complete GoingDown (Conservative)
- Assign GoingDown.lean with specific instruction: "Complete witness extraction only, do not restart proof"
- Estimated effort: 20-30 lines
- Risk: LOW (clear path)
- Reward: 1 sorry resolved

### Option B: Focus on WContractible (Aggressive)
- Assign WContractible.lean to complete section construction
- Estimated effort: 60-100 lines
- Risk: MEDIUM (complex proof)
- Reward: 4 sorries resolved

### Option C: Parallel Approach (Recommended)
- Assign both targets to different provers if using multi-agent mode
- GoingDown: quick win (20-30 lines)
- WContractible: high-value target (60-100 lines)
- Risk: MEDIUM (resource contention)
- Reward: Up to 5 sorries resolved

## Monitoring Points

1. **Sorry count:** Must not increase further - investigate any regression immediately
2. **GoingDown completion:** Should resolve in 1 session if witness extraction is straightforward
3. **WContractible progress:** Monitor whether section construction approach is viable

## Notes for Provers

### GoingDown.lean
- Do NOT restart the proof
- The mathematical approach is correct
- Only complete the witness extraction step
- Use `Ideal.mem_sup` and `Ideal.mem_span_singleton`

### WContractible.lean
- Surjectivity infrastructure is complete (session 6)
- Focus on section construction using `CompactT2.Projective`
- Use session 6 patterns for membership proofs
