# Analogy: bridge a `ContinuousMap (PrimeSpectrum C) (PrimeSpectrum B)` over `Spec A` to a ring map `B →ₐ[A] C` using `BijectiveOnStalks` hypotheses

## Mode
api-alignment

## Slug
lane-d-lrs-bridge

## Iteration
134

## Question

What is Mathlib's idiomatic shape for promoting a bare continuous map between Spec spaces to a morphism of locally-ringed spaces — and then to a ring map — under a local-ring-stalk-isomorphism hypothesis such as `Algebra.BijectiveOnStalks`?

## Project artifact(s)
- `Proetale/Algebra/IdentifiesLocalRings.lean:60-67` — `structure HomOver A B C`: continuous map `PrimeSpectrum C → PrimeSpectrum B` + `comp_comap_algebraMap` compatibility witness.
- `Proetale/Algebra/IdentifiesLocalRings.lean:90-100` — `continuousMap_of_algHom`: sorry-free forward direction.
- `Proetale/Algebra/IdentifiesLocalRings.lean:136-139` — `continuousMap_of_algHom_bijective`: the open sorry; this is the *only* substantive obligation in the file.
- `Proetale/Algebra/StalkIso.lean:27-30` — definition of `Algebra.BijectiveOnStalks`.

## Decisions identified

### Decision 1: Carrier shape for `HomOver` — `structure (ContinuousMap + Prop field)` vs. Mathlib's `Over (Spec.toLocallyRingedSpace.obj (op A))`

- **Mathlib idiom**: `CategoryTheory.Over (Spec A)`. An object is `(Y, p : Y ⟶ Spec A)` with `Y : Scheme`; a morphism `Y₁ ⟶ Y₂` over `Spec A` is a pair `(f : Y₁ ⟶ Y₂, h : f ≫ p₂ = p₁)` with `f` a **`Scheme.Hom`** — i.e. with full sheaf-level data, not a bare `ContinuousMap`. Cite: `Mathlib/CategoryTheory/Comma/Over/Basic.lean` (the `Over` machinery, used everywhere in AG), and `Mathlib/AlgebraicGeometry/Over.lean` for the AG-side notation `Scheme.Hom.IsOver` / `X.Over Y`.
- **Project's path**: `HomOver A B C` carries a `ContinuousMap` plus a `Prop` compatibility witness; no sheaf data.
- **Gap**: divergent-and-intentional. Mathlib's `Over (Spec A)` is the wrong shape here because the *point* of Stacks 096L is precisely that the continuous-only shape coincides with the scheme-morphism shape when both algebras identify local rings. Using `Over (Spec A)` as the codomain of the equivalence would assume the theorem.
- **Cost of divergence (if any)**: None of the standard kind. The codomain of the bijection is a new shape because the theorem is non-trivial; this is correct.
- **Verdict**: PROCEED. `HomOver` is the right shape *as the codomain of the Stacks 096L equivalence*. (Downstream consumers who want a `Scheme.Hom` will first transport along `algHomEquivContinuousMap.symm` to get a ring map, then `Spec.map` it — that round-trip is the unavoidable price of stating the theorem at all.)

### Decision 2: Final-step bridge from `B →ₐ[A] C` to `Spec C → Spec B` (the forward map)

- **Mathlib idiom**: `Spec.homEquiv : (Spec S ⟶ Spec R) ≃ (R ⟶ S)` lives at `Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean:569`. It is the affine-`Spec/Γ` adjunction, with `(Spec S ⟶ Spec R)` on the LHS understood as **`Scheme.Hom`** (= `LocallyRingedSpace.Hom` underneath). Supporting machinery: `ΓSpec.adjunction : Scheme.Γ.rightOp ⊣ Scheme.Spec` (line 393) and `ΓSpec.locallyRingedSpaceAdjunction` (line 327).
- **Project's path**: the forward direction (`continuousMap_of_algHom`) bypasses `Spec.homEquiv` entirely and just uses `PrimeSpectrum.comap` to extract the continuous map directly. This is correct because `HomOver` is continuous-only — `Spec.homEquiv` would give back a `Scheme.Hom` that we'd then have to discard the sheaf data of.
- **Gap**: divergent-equivalent (with one caveat). The composite `Spec.homEquiv.symm` then forget-to-`ContinuousMap` is naturally isomorphic to `PrimeSpectrum.comap`, but the project's direct route is more efficient and doesn't introduce sheaf-machinery dependencies.
- **Verdict**: PROCEED. The direct `PrimeSpectrum.comap`-based forward map is the right call.

### Decision 3: Inverse-direction bridge from `(φ, h) : HomOver A B C` to a ring map `B →ₐ[A] C` — go through `LocallyRingedSpace.Hom` or direct via `Localization.localRingHom`?

- **Mathlib idiom (the would-be route)**: First promote `(φ, h)` to a `LocallyRingedSpace.Hom` between `Spec.toLocallyRingedSpace.obj (op (.of B))` and `Spec.toLocallyRingedSpace.obj (op (.of C))`, then apply `Spec.homEquiv.symm` (or equivalently `Spec.preimage`, line 549 of `GammaSpecAdjunction.lean`) to read off the ring map. The promotion would build (i) a presheaf comap `φ⁻¹ 𝒪_Spec B → 𝒪_Spec C` and (ii) prove each stalk map is an `IsLocalHom`. Per the blueprint sketch at `local-structure.tex:546-611`, the presheaf comap is constructed as the chain `φ⁻¹ 𝒪_Y ≅ φ⁻¹ p⁻¹ 𝒪_X = (p ∘ φ)⁻¹ 𝒪_X = q⁻¹ 𝒪_X ≅ 𝒪_Z`.
- **Crucial gap in this idiom**: **Mathlib has NO existing lemma that promotes a `ContinuousMap` between `LocallyRingedSpace`s (or `Spec` schemes) to a `LocallyRingedSpace.Hom` from stalk-bijection hypotheses.** `LocallyRingedSpace.Hom` (`Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean:78`) extends `PresheafedSpace.Hom`, which definitionally **requires** the presheaf comap as primary data. The closest analogues — `IsOpenImmersion.of_isIso_stalkMap` at `Mathlib/AlgebraicGeometry/OpenImmersion.lean:431`, `Preimmersion`, `ClosedImmersion.of_continuous_injective_isClosedMap` — all take a pre-existing `Scheme.Hom` and *add* properties; none constructs the morphism from continuous-plus-stalk data.
- **Project's path (current sorry)**: open.
- **Direct alternative (recommended)**: build `f : B →ₐ[A] C` *pointwise* using only the existing `BijectiveOnStalks.localRingHom` API in `Proetale/Algebra/StalkIso.lean` (no sheaf machinery). For each prime `p` of `C`, the chain
  ```
  B  →  B_{φ(p)}  ≅  A_{φ(p) ∩ A}  =  A_{p ∩ A}  ≅  C_p
  ```
  is the composite of: `algebraMap B (Localization.AtPrime (φ p).asIdeal)`, then `(Localization.localRingHom _ _ (algebraMap A B) rfl)`-inverse (exists by `BijectiveOnStalks A B`), then a rewrite using the `h` field of `HomOver` (this rewrites the comap prime), then `Localization.localRingHom _ _ (algebraMap A C) rfl` (exists by `BijectiveOnStalks A C`). The injection `C → ∏ p, C_p` (essentially `IsLocalization.AtPrimes.injective`-style; or: any element of `C` is determined by its images in all local rings `C_p`) lets one extract `f(b) ∈ C` from this family.
- **Gap**: divergent-with-cost in either direction.
  - Going through `LocallyRingedSpace.Hom` costs: writing a presheaf comap from scratch (large amount of `RingedSpace`-level scaffolding the project doesn't otherwise touch), unfamiliar Mathlib namespaces (`TopCat.Presheaf.pushforward`, `inverseImage`, `Sheaf.pushforward`), and the eventual `Spec.homEquiv.symm` strips all that data away anyway.
  - Going direct costs: building one ad-hoc "ring map from local data" helper. But this helper already half-exists — `RingHom.injective_of_localRingHom_injective` (used in `StalkIso.lean:247`) and the structural ingredients in `bijective_of_bijective` (lines 244-307) are exactly the same shape.
- **Verdict**: **DIVERGE_INTENTIONALLY** (away from the sheaf-theoretic route). Build the ring map directly. The blueprint's L614-L631 list of "candidate Mathlib helpers" is a red herring — the named candidates exist, but using them forces the prover to construct exactly the sheaf data the adjunction will then discard. The pointwise-localization route uses *only* infrastructure the project has already built for `BijectiveOnStalks` and matches the proof style of neighboring lemmas (`bijective_of_bijective`).

## Recommendation

Close `continuousMap_of_algHom_bijective` by the **direct route** — *do not* build a `LocallyRingedSpace.Hom` or invoke `Spec.homEquiv` / `ΓSpec.adjunction`. Concretely:

1. **Add a helper to `Proetale/Algebra/StalkIso.lean`** (or a small new file `Proetale/Algebra/RingHomOfLocalData.lean`) of the rough shape

   ```
   /-- A ring map `B → C` is determined by, and constructible from, a coherent family
       of local maps `B_{q} → C_p` indexed by primes `p` of `C`, where `q = comap p`,
       provided each `B_q` is recovered from a third ring `A` via `BijectiveOnStalks`. -/
   noncomputable def ringHom_of_local_data [Algebra A B] [Algebra A C]
       [Algebra.BijectiveOnStalks A B] [Algebra.BijectiveOnStalks A C]
       (φ : PrimeSpectrum C → PrimeSpectrum B)
       (h : ∀ p, (algebraMap A B).comap (φ p).asIdeal = (algebraMap A C).comap p.asIdeal) :
       B →ₐ[A] C
   ```

   built by sending `b ∈ B` to the unique `c ∈ C` whose image in every `C_p` equals
   `(Localization.localRingHom _ _ (algebraMap A C) rfl)
     ((Localization.localRingHom _ _ (algebraMap A B) rfl) ⁻¹
       (algebraMap B _ b))`
   after rewriting along `h p`. Existence/uniqueness of such `c` is one structural
   lemma: the localization-comparison map `C → ∏ p, C_p` is injective, and the
   constructed family is in the image because each `b` already determines an
   element of every `C_p` by the chain above.

2. **Surjectivity** of `continuousMap_of_algHom` follows: given `(φ, h)`, take
   `f := ringHom_of_local_data φ h`; check `PrimeSpectrum.comap f = φ` by computing
   on each prime via the construction (it's tautological after one
   `Localization.localRingHom` unfolding).

3. **Injectivity** follows by the same localization-injectivity step: two
   `A`-algebra maps `f₁, f₂ : B →ₐ[A] C` with `Spec(f₁) = Spec(f₂)` produce the same
   localized maps `B_q → C_p` (both factor through the canonical
   `A_{q ∩ A} ≅ B_q` and `A_{p ∩ A} ≅ C_p` from `BijectiveOnStalks`, and these
   identifications pin down the local map uniquely), hence `f₁ = f₂` via
   the injection `C → ∏ p, C_p`.

4. **Update the blueprint sketch** (`local-structure.tex:546-631`) on a later pass:
   the helper list at L614-L631 should be replaced by a one-line pointer to the
   direct construction, with `Spec.homEquiv` / `ΓSpec.adjunction` removed as
   "expected ingredients". They are *real Mathlib idioms* (cited above) but they
   are *not the right tool for this proof*.

The persistent posture for future iters: `Algebra.BijectiveOnStalks` is a strictly
algebraic typeclass, and its consumers should likewise stay algebraic. Crossing
into `AlgebraicGeometry.LocallyRingedSpace` / `Scheme` would be appropriate only
if the project later wants to *export* the equivalence as an instance of a
Mathlib categorical equivalence — at which point the route is `algHomEquivContinuousMap` (already in place) composed with `Spec.homEquiv` to land in the
`Over (Spec A)` category. That export, if needed, is a separate corollary, not a
prerequisite for closing the current sorry.

---

## iter-135 revision (existence half only)

### What iter-134 got right
- **Decision 1 (HomOver carrier)**: confirmed PROCEED; no change.
- **Decision 2 (forward map)**: confirmed PROCEED; no change.
- **Injectivity half of Decision 3**: closed sorry-free by iter-134 prover via the per-prime `Localization.localRingHom` + `PrimeSpectrum.toPiLocalization_injective` route, exactly as the iter-134 recipe predicted.

### What iter-134 got wrong (existence half)
The iter-134 recipe claimed the candidate ring map `f : B → C` — defined per-prime — would be in the image of `C → ∏_p Loc.AtPrime p.asIdeal` "by the chain above". This is **wrong**:
- `PrimeSpectrum.toPiLocalization` is **injective but generally not surjective** (the iter-134 prover and `Mathlib/RingTheory/Spectrum/Maximal/Localization.lean:124, 248` `toPiLocalization_not_surjective_of_infinite` both confirm this).
- The candidate family being in the image is itself a substantive structural claim — it is the global-section content of the structure-sheaf identification `O_{Spec C} ≅ q_C^{-1} O_{Spec A}`.

The iter-134 analogist's "DIVERGE_INTENTIONALLY away from sheaves" verdict on Decision 3 was **over-optimistic about the algebraic content available**. There is no Olivier / flat-epi shortcut in Mathlib (verified — see "Option 2 verdict" below), and the per-prime route alone cannot close existence.

### Revised verdict on Decision 3
The verdict on Decision 3 (inverse-direction bridge) is **partially reversed**: injectivity should stay algebraic (as iter-134 closed), but existence requires sheaf-level data. The blueprint sketch L546–611 was correct: sheafification + global-sections is the only viable Mathlib-available route.

### Options surveyed for the existence half

#### Option 1 — sheaf-theoretic short circuit (RECOMMENDED)
Build a `Scheme.Hom Spec C ⟶ Spec B` from `(φ, h)`, then read off the ring map via `AlgebraicGeometry.Spec.preimage` / `Spec.homEquiv.symm`. The bottleneck is constructing the presheaf comap (= sheaf morphism `φ^{-1} O_{Spec B} → O_{Spec C}`) from continuous + BijectiveOnStalks data, since Mathlib does NOT have a "build LRS.Hom from base + stalk maps" constructor (confirmed by iter-134; re-verified in iter-135).

The minimal sheaf-iso we must build (does not exist in Mathlib):

```
lemma Algebra.BijectiveOnStalks.isIso_structureSheaf_pullback
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.BijectiveOnStalks A B] :
    -- q := Spec.map (CommRingCat.ofHom (algebraMap A B)) : Spec(.of B) ⟶ Spec(.of A)
    -- the canonical morphism q.c : q.base^{-1} O_{Spec A} → O_{Spec B} is an iso
    sorry
```

This is the algebraic content of Stacks 096J ⇔ 04D2. Once landed, the existence proof reads:

```
private theorem exists_algHom_of_continuousMap
    [Algebra.BijectiveOnStalks A B] [Algebra.BijectiveOnStalks A C]
    (φ : HomOver A B C) : ∃ f : B →ₐ[A] C, continuousMap_of_algHom f = φ := by
  -- (i) Build φ-as-Scheme.Hom: base φ.toContinuousMap, comap = chain
  --   φ^{-1} O_{Spec B} ≅ φ^{-1} q_B^{-1} O_{Spec A} = (q_B ∘ φ)^{-1} O_{Spec A}
  --                    = q_C^{-1} O_{Spec A} ≅ O_{Spec C}
  -- The middle equality uses φ.comp_comap_algebraMap. The two `≅`'s use
  -- isIso_structureSheaf_pullback for A→B and A→C.
  -- (ii) Verify stalk maps are local (free from the iso construction).
  -- (iii) Apply Spec.preimage to get B →+* C, lift to A-alg via algebraMap commutativity.
  sorry
```

Concrete Mathlib citations for the helpers:
- `AlgebraicGeometry.StructureSheaf.comap` (`Mathlib/AlgebraicGeometry/StructureSheaf.lean:1089`) — the section-level structure-sheaf comap for a ring map, with comap-on-stalks already equal to `Localization.localRingHom` (`comap_apply`, line 1108).
- `AlgebraicGeometry.Spec.locallyRingedSpaceMap` (`Mathlib/AlgebraicGeometry/Spec.lean:239`) — `Spec` as a functor to `LocallyRingedSpace`; its stalk maps are `Localization.localRingHom` (`localRingHom_comp_stalkIso`, line 221).
- `AlgebraicGeometry.LocallyRingedSpace.Hom` (`Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean:78`) and `homMk` (line 156) — the structure to populate.
- `AlgebraicGeometry.Spec.preimage` / `Spec.homEquiv` (`Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean:549, 569`) — the final ring-map extraction.
- `AlgebraicGeometry.isIso_iff_isIso_stalkMap` (`Mathlib/AlgebraicGeometry/OpenImmersion.lean:464`) — the stalk-iso ↔ Scheme-iso criterion (useful as a lemma about how the comap iso composes).
- `TopCat.Sheaf.pushforward` / `TopCat.Sheaf.pullback` (`Mathlib/Topology/Sheaves/Functors.lean:62, 91`) — sheaf inverse-image functors; used to formulate `q^{-1} O_{Spec A}` and to glue the chain.

LOC estimate: 150–250 (50–100 for `isIso_structureSheaf_pullback` + 100–150 for the existence proof, using the comap chain). The chain unfolds via existing simp lemmas (`Spec.locallyRingedSpaceMap_toHom`, `Spec.sheafedSpaceMap_hom_c_app`).

Downstream benefit: the `isIso_structureSheaf_pullback` helper is reusable for ANY downstream consumer needing the "BijectiveOnStalks ⇒ structure sheaf identification" direction (e.g. eventually for `Proetale/Algebra/WContractible.lean:519`'s `PullbackProfinite.diag.map` field, which the file's docstring confirms "is constructed via the identifies-local-rings bijection").

#### Option 2 — Flat-epimorphism / Olivier characterization (REJECTED)
Search of `Mathlib/` (iter-135) confirms:
- `RingHom.FlatEpi` does **not** exist.
- The Olivier characterization (flat epi `A → B` ⇔ `B = colim A_S` over a directed system of localizations) does **not** exist.
- `Mathlib/Algebra/Category/Ring/Epi.lean` covers `CommRingCat.epi_iff_epi` (`Algebra.IsEpi` = tensor-collapse condition) and `RingHom.surjective_iff_epi_and_finite`, but no flat-epi specialization.
- Closest available result: `Mathlib/AlgebraicGeometry/Morphisms/FlatMono.lean` (`Flat.isIso_of_surjective_of_mono`, `IsOpenImmersion.of_flat_of_mono`) deals with the scheme-level dual, but only in the finitely-presented setting and only gives `IsOpenImmersion`, not a constructive ring-level Olivier theorem.

Verdict: **DO NOT PURSUE this iter**. Building Olivier from scratch is ≥ 500 LOC of pure ring-theoretic infrastructure (Lazard-style colimit theorem) and would not be in the scope of a single prover round.

#### Option 3 — direct sheaf-condition proof (REJECTED)
Proving sheafiness of the candidate family on a basic-open cover of `Spec C` by hand. This is essentially reproducing the structure-sheaf identification *without* the abstraction, and per the iter-134 task report would be similar or longer in LOC (200–400) than Option 1, with no downstream payoff.

Verdict: **DO NOT PURSUE**. Option 1 strictly dominates.

#### Option 4 — full iter-133 re-engagement (SUBSUMED BY OPTION 1)
Option 4 in the iter-134 task report IS Option 1 here — the "construct LRS.Hom from continuous + stalk data" is exactly the sheaf-iso chain. The iter-134 analogist rejected it as "construct sheaf data only to discard it", but this iter-135 analysis confirms the discard is unavoidable: the existence statement *requires* a Scheme.Hom to exist, so the sheaf data must be built. The "discard" is real but inevitable.

### Concrete helper signatures iter-136 prover should target

Place in a new file `Proetale/Algebra/StructureSheafPullback.lean` (or extend `Proetale/Algebra/StalkIso.lean` if the chain is short enough):

```lean
/-- Stacks 096J ⇔ 04D2 (sheaf-level half): if `A → B` identifies local rings,
the structure-sheaf comap `(Spec.map (algebraMap A B)).base⁻¹ O_{Spec A} → O_{Spec B}`
is an iso. -/
lemma Algebra.BijectiveOnStalks.isIso_specMap_c
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.BijectiveOnStalks A B] :
    IsIso (AlgebraicGeometry.Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom (algebraMap A B))).toHom.c
```

(Statement should use whichever shape of the comap is most directly consumable; the `LocallyRingedSpace.Hom`'s `c` field is a `Y.presheaf ⟶ (f.base _* X.presheaf)` morphism. Use `isIso_iff_isIso_app` + `isIso_of_isIso_stalkMap` style reasoning, leveraging the BijectiveOnStalks hypothesis at each stalk via `Spec.localRingHom_comp_stalkIso`.)

Then the existence theorem in `Proetale/Algebra/IdentifiesLocalRings.lean`:

```lean
private theorem exists_algHom_of_continuousMap
    [Algebra.BijectiveOnStalks A B] [Algebra.BijectiveOnStalks A C]
    (φ : HomOver A B C) : ∃ f : B →ₐ[A] C, continuousMap_of_algHom f = φ
```

is built by:
1. Construct `Φ : Spec (.of C) ⟶ Spec (.of B)` as a `Scheme.Hom` via `LocallyRingedSpace.homMk` of the chain comap (using `isIso_specMap_c` on both sides + `φ.comp_comap_algebraMap` for the middle equality).
2. Set `f₀ := AlgebraicGeometry.Spec.preimage Φ : (.of B) ⟶ (.of C)` (this is a `CommRingCat` morphism).
3. Promote `f₀` to `B →ₐ[A] C` using `(f₀.hom.comp (algebraMap A B) = algebraMap A C)` — which follows by tracing the chain at the global-sections / `Spec` level.
4. Verify `continuousMap_of_algHom f = φ` by base equality (`Spec.preimage_map` round-trip on the underlying continuous map; the second field is propositional and follows from `HomOver.ext`).

### Final recommendation

**Option 1, with the `Algebra.BijectiveOnStalks.isIso_specMap_c` helper landed first.** Confidence MEDIUM that this closes existence in ≤ 150 LOC; HIGH for ≤ 300 LOC.

The persistent posture flip vs. iter-134: `Algebra.BijectiveOnStalks` *consumers that need a ring map back out* (this declaration is the canonical one) cannot stay purely algebraic. Crossing into `LocallyRingedSpace` IS required for the existence direction. The iter-134 posture "stay algebraic" was correct for injectivity (closed) but wrong for existence. Going forward, treat the structure-sheaf identification as a *prerequisite Mathlib gap-fill* for `BijectiveOnStalks`, not as optional sheaf scaffolding.
