# Session 6 Recommendations

## Priority Targets for Session 7

### 1. HIGH PRIORITY: WContractible.lean - Complete exists_retraction_of_bijectiveOnStalks

**Why prioritize:** Surjectivity infrastructure now in place. Session 6 established the comap surjectivity proof. Next steps are well-defined.

**Remaining work:**
- Complete section construction using `CompactT2.Projective`
- Define `T = range σ` and `S_T = Restriction T`
- Prove `IsWLocalRing S_T` and `IsWLocal (algebraMap R S_T)`
- Prove injectivity and surjectivity of π₀ map for `S_T → R`
- Apply `bijective_of_bijective` to get `R ≃ S_T`
- Extract retraction

**Estimated effort:** 60-100 lines

**Key lemmas to search:**
- Projectivity of extremally disconnected spaces
- Restriction construction preservation of w-local structure
- Ind-Zariski preservation lemmas

---

## Proof Patterns Discovered

### Pattern 1: Subtype Membership with Equality Constraints

**Problem:** When proving `⟨x, proof_of_membership⟩` where membership depends on an equality `h : a = b`, direct substitution fails.

**Solution:** Use ideal containment calculations instead:

```lean
rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
calc I.map f ≤ (comap f q).map f := Ideal.map_mono ...
           _ ≤ q := Ideal.map_comap_le
```

**When to use:** Proving membership in `zeroLocus`, `Subtype` with dependent types, or any situation where `▸` or `subst` causes type mismatches.

---

### Pattern 2: Homeomorphism Composition with Restricted Sets

**Problem:** Composing homeomorphisms with restricted functions requires careful membership tracking.

**Solution:** Use equality hypotheses with `▸` for type conversions, but not for subtype construction:

```lean
let comap_closed : closedPoints S → closedPoints R := fun p =>
  ⟨comap f p.val, hI.symm ▸ comap_mem p.val (hS.symm ▸ p.property)⟩
```

**When to use:** Working with `WLocalSpace.closedPointsHomeomorph` and converting between `closedPoints` and `zeroLocus`.

---

## Blocked Targets (Do Not Assign)

No new blockers identified in session 6. Existing blockers from session 5 remain:

- Small.lean:23 (typeclass resolution)
- Ind.lean:163 (opposite category preservation)
- GoingDown.lean:18 (localization restriction)
- Coherent/Affine.lean (infrastructure gap)
- CompactOpenCovered.lean (statement issue)

---

## Session 7 Strategy

1. **Focus:** WContractible.lean exclusively
2. **Approach:** Follow blueprint's 7-step structure (steps 1-2 now complete)
3. **Tools:** Heavy use of LSP goal checking, LeanSearch for projectivity lemmas
4. **Target:** Complete all remaining sorries in WContractible (reduce from 4 to 0)

**Success criteria:** WContractible compiles with 0 sorries, reducing project total from 54 to 50.
