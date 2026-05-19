# Lemma Extraction: PR #25 — BijectiveOnStalks for local isos

## Results

### StalkIso.lean

- **Main Result** `RingHom.IsLocalIso.bijectiveOnStalks`: Local isomorphisms are bijective on stalks.
  - Depends on: `Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion`, `IsLocalization.bijective`, `Localization.localRingHom_comp`, `Function.Bijective.of_comp_iff'`

- **Main Result** `RingHom.BijectiveOnStalks.bijective_of_bijective`: A ring hom bijective on stalks inducing a bijection on Spec is itself bijective.
  - Depends on: `injective_of_injectiveOnStalks`, `flat_of_localizations_flat`, `GeneralizingMap`, `surjective_of_forall_isMaximal_exists`, inline `going_down_key`

- `RingHom.BijectiveOnStalks.comp`: BijectiveOnStalks is stable under composition.
  - Depends on: `Localization.localRingHom_comp`

### Proetale/Mathlib/RingTheory/Spectrum/Prime/RingHom.lean (new file, all supporting)

- `RingHom.injective_of_injectiveOnStalks`: Injective stalks + surjective Spec → injective.
- `RingHom.flat_of_localizations_flat`: Flat localizations → flat.
- `RingHom.surjective_of_forall_isMaximal_exists`: Surjectivity criterion via maximal ideals.
- `RingHom.exists_mul_mem_range_of_surjective`: Converse of the above.

### LocalIso.lean (minor)

- `RingHom.IsLocalIso.toAlgebra`: Helper + `algebraize` attribute.

## Dependency Graph

```
bijective_of_bijective
├── injective_of_injectiveOnStalks (Mathlib file)
├── flat_of_localizations_flat (Mathlib file)
├── surjective_of_forall_isMaximal_exists (Mathlib file)
└── going_down_key (inline have, lines 105-119)

bijectiveOnStalks
├── h_alg_bij (inline: S_p → (S_g)_{p_g} bijective, lines 43-54)
├── h_comp_bij (inline: R_{f⁻¹(p)} → (S_g)_{p_g} bijective, lines 61-76)
└── factorization via localRingHom_comp + of_comp_iff' (lines 77-83)

comp
└── localRingHom_comp (existing API)
```

## Proof of `bijectiveOnStalks`

Given `f : R →+* S` a local iso, show for every prime `p` of `S` the stalk map `R_{f⁻¹(p)} → S_p` is bijective.

1. Find `g ∉ p` with `R → S_g` a standard open immersion; let `r` be the element with `R_r ≅ S_g`.
2. Since `g ∉ p`, powers of `g` are disjoint from `p`, so `p_g := p · S_g` is prime with `p_g ∩ S = p`.
3. **Stalk map `S_p → (S_g)_{p_g}` is bijective**: `(S_g)_{p_g}` is also a localization of `S` at `p` (localizing away from `g` then at the image prime = localizing at `p` since `g ∉ p`). Apply `IsLocalization.bijective`.
4. **Stalk map `R_{f⁻¹(p)} → (S_g)_{p_g}` is bijective**: `S_g` is a localization of `R` at `r`, so `(S_g)_{p_g}` is also a localization of `R` at `f⁻¹(p)`. Apply `IsLocalization.bijective`.
5. **Factor and conclude**: `R_{f⁻¹(p)} → S_p → (S_g)_{p_g}` equals `R_{f⁻¹(p)} → (S_g)_{p_g}` by `localRingHom_comp`. Composition is bijective + second factor is bijective → first factor is bijective by `of_comp_iff'`.

## Proof of `bijective_of_bijective`

Given `f : R →+* S` bijective on stalks with `Spec f` bijective, show `f` bijective.

**Injectivity**: Stalks are injective at all primes → at all maximal ideals. With `Spec f` surjective, apply `injective_of_injectiveOnStalks`.

**Surjectivity**:
1. `f` is flat (stalk maps are bijective hence flat, apply `flat_of_localizations_flat`).
2. `Spec f` is generalizing (from flatness).
3. **Going-down key**: If `Spec f` is injective and generalizing, then for primes `p, q` of `S` with `c ∉ p, c ∈ q`, we have `¬(q.comap f ≤ p.comap f)`. Proof: specialization in `Spec R` lifts by generalizing, injectivity forces `q ≤ p`, contradicting `c ∈ q \ p`.
4. Apply `surjective_of_forall_isMaximal_exists`: for each `s ∈ S` and maximal `m`, use stalk bijectivity at `q` (with `q.comap f = m`) to write `s` as a fraction, use going-down to show certain elements are units in a localization, then clear denominators.

## Steps (independent)

### From `bijective_of_bijective`

1. **Injective generalizing maps on Spec reflect specialization**: If `g : X → Y` is injective and generalizing, and `g x ⤳ g y`, then `x ⤳ y`. This is the core of `going_down_key` (lines 105-119).
   - Input: `Function.Injective g`, `GeneralizingMap g`, `g x ⤳ g y`
   - Output: `x ⤳ y`

### From `bijectiveOnStalks`

2. The `h_alg_bij` and `h_comp_bij` blocks (lines 43-76) are applications of existing Mathlib API (`IsLocalization.isLocalization_isLocalization_atPrime_isLocalization` + `IsLocalization.bijective`) with different submonoids. They share a pattern but are structurally different enough that a common wrapper would just restate existing API. **Not worth extracting.**

### Already extracted (in Mathlib helper file)

3. `injective_of_injectiveOnStalks`, `flat_of_localizations_flat`, `surjective_of_forall_isMaximal_exists` — already properly factored into a separate file.

## Step 4: Generalization

### Step 1: Specialization reflection

- **Specialized** (PrimeSpectrum): If `PrimeSpectrum.comap f` is injective and generalizing, then `q.comap f ≤ p.comap f → q ≤ p`.
- **Generalized** (topology): If `g : X → Y` is injective and generalizing, and `g x ⤳ g y`, then `x ⤳ y`. No ring theory needed.
- **Name**: `GeneralizingMap.specializes_of_map_specializes`
- **Hypotheses needed**: `TopologicalSpace X`, `TopologicalSpace Y`, `GeneralizingMap g`, `Function.Injective g`
- **Placement**: `Proetale/Mathlib/Topology/Inseparable.lean` (extends existing file)
