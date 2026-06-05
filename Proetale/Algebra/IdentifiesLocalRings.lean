/-
Copyright (c) 2026 Archon agents. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon agents
-/
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Proetale.Algebra.StalkIso

/-!
# Hom-set bijection for algebras identifying local rings

Let `A` be a commutative ring and let `B`, `C` be `A`-algebras such that both
`A → B` and `A → C` identify local rings (Lean class
`Algebra.BijectiveOnStalks`). This file scaffolds the hom-set bijection
$$
  \operatorname{Hom}_{A\text{-alg}}(B, C)
    \;\simeq\; \operatorname{Hom}_{\operatorname{Top}_{\operatorname{Spec} A}}
      (\operatorname{Spec} C, \operatorname{Spec} B)
$$
which formalises Stacks Tag 096L
(`thm:identifies-local-ring-to-top-fully-faithful` and
`def:identifies-local-ring-hom-set-bijection` in the blueprint).

## Main declarations

* `Algebra.BijectiveOnStalks.HomOver A B C`: continuous maps
  `PrimeSpectrum C → PrimeSpectrum B` lying over `PrimeSpectrum A`.
* `Algebra.BijectiveOnStalks.continuousMap_of_algHom`: the forward direction
  of the bijection, induced from `Spec` functoriality of `PrimeSpectrum.comap`.
* `Algebra.BijectiveOnStalks.algHom_of_continuousMap`: the inverse direction
  (requires that both `A → B` and `A → C` identify local rings).
* `Algebra.BijectiveOnStalks.algHomEquivContinuousMap`: the resulting
  equivalence of hom-sets.

## Iter-133 status

The substantive content of Stacks 096L is concentrated in the single
`Prop`-valued helper `continuousMap_of_algHom_bijective` (typed sub-sorry
under PROGRESS.md Guard 48). Both carrier declarations
`algHomEquivContinuousMap` and `algHom_of_continuousMap` are sorry-free,
constructed mechanically from the bijectivity helper via
`Equiv.ofBijective` and its symmetric inverse. The closing proof of the
bijectivity helper requires the ringed-space identification
`𝒪_Y = p⁻¹ 𝒪_X` for `A → B` identifying local rings; see the blueprint
proof of `thm:identifies-local-ring-to-top-fully-faithful`.
-/

universe u v w

namespace Algebra.BijectiveOnStalks

variable (A : Type u) (B : Type v) (C : Type w)
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]

/-- Continuous maps `PrimeSpectrum C → PrimeSpectrum B` compatible with the
structure maps to `PrimeSpectrum A`. Equivalently, morphisms in the
overcategory `TopCat / PrimeSpectrum A` from `PrimeSpectrum C` to
`PrimeSpectrum B`. -/
structure HomOver where
  /-- The underlying continuous map. -/
  toContinuousMap : C(PrimeSpectrum C, PrimeSpectrum B)
  /-- Compatibility with the structure maps to `PrimeSpectrum A`. -/
  comp_comap_algebraMap (p : PrimeSpectrum C) :
    PrimeSpectrum.comap (algebraMap A B) (toContinuousMap p) =
      PrimeSpectrum.comap (algebraMap A C) p

namespace HomOver

variable {A B C}

instance : FunLike (HomOver A B C) (PrimeSpectrum C) (PrimeSpectrum B) where
  coe φ := φ.toContinuousMap
  coe_injective' := by
    rintro ⟨⟨f, hf⟩, _⟩ ⟨⟨g, hg⟩, _⟩ (h : f = g)
    subst h
    rfl

@[ext]
theorem ext {φ ψ : HomOver A B C} (h : ∀ p, φ p = ψ p) : φ = ψ :=
  DFunLike.ext _ _ h

end HomOver

variable {A B C}

/-- The continuous map `Spec C → Spec B` over `Spec A` induced by an
`A`-algebra homomorphism `f : B →ₐ[A] C`. This is the forward direction of
the hom-set bijection from Stacks 096L. -/
noncomputable def continuousMap_of_algHom (f : B →ₐ[A] C) : HomOver A B C where
  toContinuousMap :=
    { toFun := PrimeSpectrum.comap f.toRingHom
      continuous_toFun := PrimeSpectrum.continuous_comap _ }
  comp_comap_algebraMap p := by
    show PrimeSpectrum.comap (algebraMap A B)
        (PrimeSpectrum.comap f.toRingHom p) = _
    rw [← PrimeSpectrum.comap_comp_apply]
    congr 1
    ext x
    simp

variable (A B C)

/-- Injectivity half of `continuousMap_of_algHom_bijective`: an A-algebra
homomorphism `B →ₐ[A] C` is determined by its induced continuous map on
`PrimeSpectrum` (under the `BijectiveOnStalks` hypotheses).

The proof factors the localized map `B_q → C_p` (for `q = p.comap f`) through
the bijective `Localization.localRingHom (q ∩ A) q (algebraMap A B) rfl :
A_{q ∩ A} → B_q` (from `BijectiveOnStalks A B`); this forces both localized
maps for `f₁, f₂` to agree because the composite `A_{q ∩ A} → C_p` (= the
local ring hom of `algebraMap A C`, since both `f_i` are `A`-algebra maps) is
independent of `f`. Then `f₁ b = f₂ b` follows by injectivity of
`C → ∏ p, Loc.AtPrime p.asIdeal` (`PrimeSpectrum.toPiLocalization_injective`). -/
private theorem continuousMap_of_algHom_injective
    [Algebra.BijectiveOnStalks A B] [Algebra.BijectiveOnStalks A C] :
    Function.Injective (continuousMap_of_algHom : (B →ₐ[A] C) → HomOver A B C) := by
  intro f₁ f₂ heq
  -- The induced PrimeSpectrum comaps agree.
  have hcomap_p : ∀ p : PrimeSpectrum C,
      p.asIdeal.comap f₁.toRingHom = p.asIdeal.comap f₂.toRingHom := by
    intro p
    have h := DFunLike.congr_fun heq p
    exact congrArg PrimeSpectrum.asIdeal h
  -- Both f_i compose with algebraMap A B to algebraMap A C.
  have hf₁_alg : f₁.toRingHom.comp (algebraMap A B) = algebraMap A C := by
    ext a; simp
  have hf₂_alg : f₂.toRingHom.comp (algebraMap A B) = algebraMap A C := by
    ext a; simp
  -- Reduce to a pointwise equality, then to equality of underlying ring homs.
  apply AlgHom.coe_ringHom_injective
  apply RingHom.ext
  intro b
  -- Use injectivity of C → ∏ p, Loc.AtPrime p.asIdeal.
  apply PrimeSpectrum.toPiLocalization_injective C
  funext p
  -- Goal reduces to algebraMap C (Loc.AtPrime p.asIdeal) (f₁ b) = algebraMap C _ (f₂ b).
  show algebraMap C (Localization.AtPrime p.asIdeal) (f₁.toRingHom b) =
       algebraMap C (Localization.AtPrime p.asIdeal) (f₂.toRingHom b)
  -- Push the computation through `Localization.localRingHom`, then equate the
  -- two localized maps `B_q → C_p` via the BijectiveOnStalks A B bridge.
  -- Parameterise over the common prime `q` of `B` to avoid let-binding subst issues.
  suffices key : ∀ (q : Ideal B) [q.IsPrime] (hq₁ : q = p.asIdeal.comap f₁.toRingHom)
      (hq₂ : q = p.asIdeal.comap f₂.toRingHom),
      Localization.localRingHom q p.asIdeal f₁.toRingHom hq₁
          (algebraMap B (Localization.AtPrime q) b) =
        Localization.localRingHom q p.asIdeal f₂.toRingHom hq₂
          (algebraMap B (Localization.AtPrime q) b) by
    haveI : (p.asIdeal.comap f₁.toRingHom).IsPrime := Ideal.IsPrime.comap _
    rw [← Localization.localRingHom_to_map (p.asIdeal.comap f₁.toRingHom) p.asIdeal
      f₁.toRingHom rfl b,
      ← Localization.localRingHom_to_map (p.asIdeal.comap f₁.toRingHom) p.asIdeal
      f₂.toRingHom (hcomap_p p) b]
    exact key (p.asIdeal.comap f₁.toRingHom) rfl (hcomap_p p)
  intro q _ hq₁ hq₂
  -- The bridging map K : A_{q ∩ A} → B_q is bijective (BijectiveOnStalks A B).
  set K : Localization.AtPrime (q.comap (algebraMap A B)) →+* Localization.AtPrime q :=
    Localization.localRingHom _ _ (algebraMap A B) rfl
  have hK_bij : Function.Bijective K :=
    Algebra.BijectiveOnStalks.bijective_localRingHom (R := A) q
  set M₁ : Localization.AtPrime q →+* Localization.AtPrime p.asIdeal :=
    Localization.localRingHom q p.asIdeal f₁.toRingHom hq₁
  set M₂ : Localization.AtPrime q →+* Localization.AtPrime p.asIdeal :=
    Localization.localRingHom q p.asIdeal f₂.toRingHom hq₂
  -- Claim: M_i ∘ K is independent of `i` (both equal the local ring hom of `algebraMap A C`).
  have hNcomp : M₁.comp K = M₂.comp K := by
    refine IsLocalization.ringHom_ext (q.comap (algebraMap A B)).primeCompl ?_
    refine RingHom.ext fun a => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, M₁, M₂, K,
      Localization.localRingHom_to_map]
    -- f_i.toRingHom (algebraMap A B a) = algebraMap A C a (since f_i is A-algebra).
    rw [show f₁.toRingHom ((algebraMap A B) a) = (algebraMap A C) a from f₁.commutes a,
        show f₂.toRingHom ((algebraMap A B) a) = (algebraMap A C) a from f₂.commutes a]
  -- Conclude M₁ = M₂ via surjectivity of `K`.
  have hM_eq : M₁ = M₂ := by
    refine RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := hK_bij.surjective x
    exact RingHom.congr_fun hNcomp y
  exact RingHom.congr_fun hM_eq (algebraMap B (Localization.AtPrime q) b)

/-- **Substantive existence (Stacks 096L)**: every `(φ, h) : HomOver A B C`
arises from an `A`-algebra homomorphism `f : B →ₐ[A] C`.

This is the substantive content of Stacks 096L. Per the iter-134 mathlib
analogist recipe (`analogies/identifies-local-rings-lrs-bridge.md`), the
candidate map `f : B → C` is the unique map whose image in every
`Localization.AtPrime p.asIdeal` (for `p : PrimeSpectrum C`) equals the
chain
`B → Loc.AtPrime (φ p).asIdeal ≅ Loc.AtPrime ((φ p).asIdeal.comap (algebraMap A B))
   = Loc.AtPrime (p.asIdeal.comap (algebraMap A C)) ≅ Loc.AtPrime p.asIdeal`,
where the two `≅`'s come from `BijectiveOnStalks A B` and `BijectiveOnStalks A C`
respectively, and the middle equality is the `comp_comap_algebraMap` field of
`φ`. Uniqueness follows from `PrimeSpectrum.toPiLocalization_injective`.

**Existence**, however, is *not* a purely pointwise statement: it requires
proving the candidate family lies in the image of
`algebraMap C (∏ p, Loc.AtPrime p.asIdeal)`. The standard proof uses the
structure-sheaf identification `𝒪_{Spec C} = q^{-1} 𝒪_{Spec A}` (equivalent to
`BijectiveOnStalks A C` per Stacks 096J) — this is genuinely sheaf-level
content not captured by the per-prime localization API in scope here, so the
recipe's claim that the construction is "mechanical assembly" was
over-optimistic. The obstruction is identified and isolated to this single
declaration; the rest of the bijection (injectivity, the equivalence wrapper,
the inverse-direction definition) is closed sorry-free above and below.

**iter-136 finding (critical recipe correction).** The iter-135 mathlib-
analogist `lane-d-sub-existence` recipe targeted a helper
```
lemma Algebra.BijectiveOnStalks.isIso_specMap_c :
    IsIso (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap A B))).toHom.c
```
i.e. the `c`-component (a sheaf morphism `𝒪_{Spec A} ⟶ q_* 𝒪_{Spec B}` on
`Spec A`) is iso. This signature is **mathematically incorrect**: a stalk-
wise analysis on `Spec A` shows `c`-iso is strictly stronger than
`BijectiveOnStalks A B` and is false in general. Counterexample: take
`A = ℤ`, `B = ℚ`. The map `ℤ → ℚ` identifies local rings (only prime of `ℚ`
is `(0)`, lying over `(0) ⊂ ℤ`, and `ℤ_{(0)} = ℚ → ℚ_{(0)} = ℚ` is the
identity, hence iso). But the c-component at `r = (2) ⊂ ℤ`: stalk of
`𝒪_{Spec ℤ}` is `ℤ_{(2)}`; stalk of `q_* 𝒪_{Spec ℚ}` at `(2)` is
`colim_{g ∉ (2)} ℚ[1/g] = ℚ`. The map `ℤ_{(2)} → ℚ` is the inclusion, NOT
an iso (it is not surjective).

The **correct** statement of the structure-sheaf identification (Stacks
096J ⇔ 04D2) is at the inverse-image level: the canonical map
`q_B.base⁻¹ 𝒪_{Spec A} → 𝒪_{Spec B}` is iso as sheaves on `Spec B`
(equivalently, `𝒪_{Spec B} = q_B.base⁻¹ 𝒪_{Spec A}`). This is stalk-wise
on `Spec B`: at each `p : PrimeSpectrum B`, the stalk map is
`A_{p ∩ A} → B_p`, which is iso by `BijectiveOnStalks A B` via
`Algebra.BijectiveOnStalks.localRingHom_comp_stalkIso`.

The iter-137 prover should land the corrected helper
```
lemma Algebra.BijectiveOnStalks.isIso_invImage_structureSheaf
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.BijectiveOnStalks A B] :
    IsIso (canonical map (q_B.base)⁻¹ 𝒪_{Spec A} ⟶ 𝒪_{Spec B})
```
where the canonical map is the unit-adjoint of `q_B.toHom.c`. This helper
will then feed the LRS-construction in this proof (chain
`Φ.c⁻¹ 𝒪_{Spec B} ≅ Φ.c⁻¹ q_B⁻¹ 𝒪_{Spec A} = (q_B ∘ Φ.c)⁻¹ 𝒪_{Spec A} =
q_C⁻¹ 𝒪_{Spec A} ≅ 𝒪_{Spec C}`).

Given the recipe-level correction needed AND the substantial sheaf-level
scaffolding (≥150 LOC inverse-image+pushforward natural transformation
plumbing) the corrected helper requires, iter-136 does not land the close.
The proof body retains a single typed `sorry` with the intended construction
recorded in the proof skeleton below for the iter-137 prover to inherit. -/
private theorem exists_algHom_of_continuousMap
    [Algebra.BijectiveOnStalks A B] [Algebra.BijectiveOnStalks A C]
    (φ : HomOver A B C) : ∃ f : B →ₐ[A] C, continuousMap_of_algHom f = φ := by
  -- Proof skeleton (iter-136; corrected from iter-135 analogist recipe).
  -- iter-142 affirmation: lane re-dispatched per PROGRESS.md; obstacle
  -- (corrected sheaf-iso helper + universe alignment) unchanged.
  --
  -- Sheaf-theoretic short circuit (Option 1, Stacks 096L proof):
  --
  --   Step 1: Promote `φ : ContinuousMap (PrimeSpectrum C) (PrimeSpectrum B)`
  --     to a `Scheme.Hom Spec(.of C) ⟶ Spec(.of B)` (equivalently an
  --     `LRS`-hom) via the structure-sheaf identification at the
  --     inverse-image level:
  --     `φ.base⁻¹ 𝒪_{Spec B} ≅ φ.base⁻¹ q_B.base⁻¹ 𝒪_{Spec A}`
  --       `= (q_B.base ∘ φ.base)⁻¹ 𝒪_{Spec A}`
  --       `= q_C.base⁻¹ 𝒪_{Spec A}`  (using `φ.comp_comap_algebraMap`)
  --       `≅ 𝒪_{Spec C}`.
  --     The two `≅`'s use `isIso_invImage_structureSheaf` (the iter-137
  --     helper described in the docstring). The middle equality uses
  --     `φ.comp_comap_algebraMap`.
  --
  --   Step 2: Extract the underlying ring map `f₀ : B →+* C` via
  --     `AlgebraicGeometry.Spec.preimage` applied to the `Scheme.Hom`
  --     from step 1. The over-`Spec A` structure of the `Scheme.Hom`
  --     ensures `f₀.comp (algebraMap A B) = algebraMap A C` (commutes
  --     with the global-sections counit), so `f₀` promotes to a
  --     `B →ₐ[A] C`.
  --
  --   Step 3: Verify `continuousMap_of_algHom f = φ` via
  --     `AlgebraicGeometry.Spec.map_preimage` (which simp-unfolds the
  --     `Spec.preimage` round trip), then `HomOver.ext` for the
  --     compatibility-witness component (the field is `Prop`-valued).
  --
  -- Steps 1 and 2 reduce to a single typed `sorry` keyed on the
  -- inverse-image structure-sheaf iso. The skeleton above is the
  -- iter-137 starting point.
  --
  -- ===== iter-142 sharpened sub-goal (algebraic re-packaging) =====
  --
  -- Equivalent reduction avoiding `Scheme.Hom` / universe alignment:
  -- explicitly build the per-prime candidate ring map family and show
  -- it lifts to `B → C`. Concretely:
  --
  --   For each `p : PrimeSpectrum C`, let `q := (φ p).asIdeal : Ideal B`.
  --   Via `BijectiveOnStalks A B` at `q`, the canonical
  --     `K_p : A_{q ∩ A} →+* B_q := Localization.localRingHom _ _ (algebraMap A B) rfl`
  --   is bijective; let `Kinv_p` be its inverse. Using
  --   `φ.comp_comap_algebraMap p : q.comap (algebraMap A B) = p.asIdeal.comap (algebraMap A C)`
  --   together with `Localization.localRingHom _ _ (algebraMap A C) _` yields
  --     `α_p : A_{q ∩ A} →+* C_p`.
  --   Then the candidate
  --     `M_p : B →+* C_p := α_p.comp (Kinv_p.comp (algebraMap B B_q))`
  --   bundles to `lift : B →+* (∀ p, C_p) := Pi.ringHom (fun p ↦ M_p)`.
  --
  -- Sharper sub-goal (algebraic content of Stacks 096J ⇔ 04D2):
  --     ∃ f : B →+* C, (PrimeSpectrum.toPiLocalization C).comp f = lift
  -- (Uniqueness of `f` follows from `PrimeSpectrum.toPiLocalization_injective C`.)
  --
  -- Once this `f` is produced:
  --   * A-linearity follows by `PrimeSpectrum.toPiLocalization_injective C`
  --     applied to both sides; on each `p`, `lift (algebraMap A B a) p` and
  --     `(toPiLocalization C) (algebraMap A C a) p` both reduce to
  --     `algebraMap A (Localization.AtPrime p.asIdeal) a` via
  --     `Localization.localRingHom_to_map` and the chain construction of
  --     `M_p`.
  --   * `continuousMap_of_algHom f = φ` reduces — after `HomOver.ext` — to the
  --     pointwise claim `PrimeSpectrum.comap f.toRingHom = φ.toContinuousMap`,
  --     which follows because `M_p` factors through `algebraMap B B_q`, hence
  --     `lift b p = 0` iff `algebraMap B B_q b ∈ q.primeCompl`-pulled, pinning
  --     `comap f p = (φ p)` via the prime correspondence.
  --
  -- The reduction above is universe-stable (lives in `Type u/v/w` directly,
  -- no `Spec`-side category-theoretic categories needed). The single typed
  -- `sorry` is the sharper sub-goal.
  --
  -- ===== iter-143 materialisation =====
  -- We materialise the per-prime candidate `M_p : B →+* C_p` and the bundled
  -- `lift : B →+* ∏ p, C_p`. The proof then reduces to the precisely-typed
  -- sub-claim
  --     `∃ f : B →+* C, (toPiLocalization C).toRingHom.comp f = lift`
  -- (the structure-sheaf identification `q⁻¹ 𝒪_X ≅ 𝒪_Z` repackaged as a
  -- "compatible family lifts" sheaf condition; cf. blueprint
  -- `lem:identifies-local-ring-invImage-structureSheaf-iso`). Once that
  -- single sub-claim is in hand, A-linearity and `continuousMap_of_algHom f
  -- = φ` follow mechanically (see comments in the closing tactic).
  classical
  -- Step 0: per-prime data.
  have hcomap (p : PrimeSpectrum C) :
      (φ p).asIdeal.comap (algebraMap A B) = p.asIdeal.comap (algebraMap A C) :=
    congrArg PrimeSpectrum.asIdeal (φ.comp_comap_algebraMap p)
  have hKbij (p : PrimeSpectrum C) :
      Function.Bijective
        (Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) (φ p).asIdeal
          (algebraMap A B) rfl) :=
    Algebra.BijectiveOnStalks.bijective_localRingHom (R := A) (φ p).asIdeal
  -- Step 1: per-prime candidate ring map `M_p : B →+* C_p`.
  let M : ∀ p : PrimeSpectrum C, B →+* Localization.AtPrime p.asIdeal := fun p =>
    haveI : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
    let Lp := Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) p.asIdeal
      (algebraMap A C) (hcomap p)
    let Kinv := (RingEquiv.ofBijective _ (hKbij p)).symm.toRingHom
    Lp.comp (Kinv.comp (algebraMap B (Localization.AtPrime (φ p).asIdeal)))
  -- Step 2: bundle to `lift : B →+* ∏ p, C_p`.
  let lift : B →+* PrimeSpectrum.PiLocalization C := Pi.ringHom M
  -- Step 3: reduce to the structure-sheaf-identification sub-claim.
  -- This is the substantive content of Stacks 096L (the sheaf condition for
  -- `q⁻¹ 𝒪_X ≅ 𝒪_Z` repackaged at the global-sections level).
  suffices hex : ∃ f : B →+* C,
      (PrimeSpectrum.toPiLocalization C).toRingHom.comp f = lift by
    obtain ⟨f, hf⟩ := hex
    -- f matches M at every prime: `algebraMap C C_p (f b) = M p b`.
    have hfM (b : B) (p : PrimeSpectrum C) :
        algebraMap C (Localization.AtPrime p.asIdeal) (f b) = M p b := by
      have h : (PrimeSpectrum.toPiLocalization C).toRingHom.comp f b p = lift b p := by
        rw [hf]
      exact h
    -- A-linearity: `f (algebraMap A B a) = algebraMap A C a` via injectivity of
    -- `toPiLocalization C`.
    have hfA (a : A) : f (algebraMap A B a) = algebraMap A C a := by
      apply PrimeSpectrum.toPiLocalization_injective C
      funext p
      haveI : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
      -- M p (algebraMap A B a) = algebraMap A (Loc p) a (per-prime computation).
      have hM : M p (algebraMap A B a) = algebraMap A (Localization.AtPrime p.asIdeal) a := by
        simp only [M, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
          RingEquiv.coe_toRingHom]
        rw [← Localization.localRingHom_to_map ((φ p).asIdeal.comap (algebraMap A B))
              (φ p).asIdeal (algebraMap A B) rfl a,
          ← RingEquiv.ofBijective_apply _ (hKbij p) (algebraMap A _ a),
          RingEquiv.symm_apply_apply,
          Localization.localRingHom_to_map,
          ← IsScalarTower.algebraMap_apply A C (Localization.AtPrime p.asIdeal) a]
      -- LHS = algebraMap C (Loc p) (f (algebraMap A B a)) = M p (...) = algebraMap A (Loc p) a.
      have hLHS : (PrimeSpectrum.toPiLocalization C) (f (algebraMap A B a)) p =
          algebraMap A (Localization.AtPrime p.asIdeal) a := by
        have hLrfl : (PrimeSpectrum.toPiLocalization C) (f (algebraMap A B a)) p =
            algebraMap C (Localization.AtPrime p.asIdeal) (f (algebraMap A B a)) := rfl
        rw [hLrfl, hfM, hM]
      -- RHS = algebraMap C (Loc p) (algebraMap A C a) = algebraMap A (Loc p) a (IsScalarTower).
      have hRHS : (PrimeSpectrum.toPiLocalization C) (algebraMap A C a) p =
          algebraMap A (Localization.AtPrime p.asIdeal) a := by
        have hRrfl : (PrimeSpectrum.toPiLocalization C) (algebraMap A C a) p =
            algebraMap C (Localization.AtPrime p.asIdeal) (algebraMap A C a) := rfl
        rw [hRrfl, ← IsScalarTower.algebraMap_apply A C (Localization.AtPrime p.asIdeal) a]
      rw [hLHS, hRHS]
    -- Spec-comap: `PrimeSpectrum.comap f p = φ p` because `M_p` factors
    -- through `algebraMap B B_{φp}` and `Lp ∘ Kinv` is a local ring hom.
    have hcomapf (p : PrimeSpectrum C) : PrimeSpectrum.comap f p = φ p := by
      apply PrimeSpectrum.ext
      apply Ideal.ext
      intro b
      haveI : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
      haveI hLp : IsLocalHom
          (Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) p.asIdeal
            (algebraMap A C) (hcomap p)) :=
        Localization.isLocalHom_localRingHom _ _ _ _
      -- b ∈ (Pseudo.comap f p).asIdeal iff f b ∈ p.asIdeal (defn of Ideal.comap).
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap (f := f)]
      refine not_iff_not.mp ?_
      rw [← Ideal.mem_primeCompl_iff (P := p.asIdeal),
        ← Ideal.mem_primeCompl_iff (P := (φ p).asIdeal),
        ← IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p.asIdeal) p.asIdeal (f b),
        ← IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (φ p).asIdeal)
          (φ p).asIdeal b,
        hfM b p]
      -- Goal: IsUnit (M p b) ↔ IsUnit (algebraMap B (Loc φp) b).
      simp only [M, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom]
      refine ⟨fun hu => ?_, fun hu => ?_⟩
      · exact (MulEquiv.isUnit_map (RingEquiv.ofBijective _ (hKbij p)).symm).mp (hLp.1 _ hu)
      · exact (Localization.localRingHom _ _ (algebraMap A C) (hcomap p)).isUnit_map
          ((MulEquiv.isUnit_map (RingEquiv.ofBijective _ (hKbij p)).symm).mpr hu)
    refine ⟨{ f with commutes' := hfA }, ?_⟩
    apply HomOver.ext
    intro p
    exact hcomapf p
  -- ===== Substantive Stacks 096L sub-claim — TYPED SORRY =====
  -- Existence of `f : B →+* C` lifting the candidate family `lift = Pi.ringHom M`.
  -- Equivalent to the structure-sheaf identification `q⁻¹ 𝒪_X ≅ 𝒪_Z` on Spec C
  -- (blueprint `lem:identifies-local-ring-invImage-structureSheaf-iso`,
  -- formalised as `Algebra.BijectiveOnStalks.isIso_invImage_structureSheaf` in
  -- `Proetale/Algebra/StructureSheafPullback.lean`: iso of
  -- `invImageStructureSheafHom A B`, the sheaf-level adjoint transpose
  -- `(Sheaf.pullback _ q.base).obj 𝒪_{Spec A} ⟶ 𝒪_{Spec B}` of `q.toHom.c`);
  -- see PROGRESS.md iter-143 Lane D-sub for the closure recipe (≥150 LOC
  -- inverse-image-of-structure-sheaf scaffolding required).
  exact sorry

/-- **Substantive Stacks 096L content.** When both `A → B` and `A → C`
identify local rings, the forward map
`continuousMap_of_algHom : (B →ₐ[A] C) → HomOver A B C` is a bijection.

This is the formalisation pivot of Stacks 096L: the geometric content
(building a ring map `B → C` from a continuous map `Spec C → Spec B`
respecting the structure to `Spec A`, when both algebras identify local
rings) is concentrated here. The companion declarations
`algHomEquivContinuousMap` and `algHom_of_continuousMap` are mechanical
consequences via `Equiv.ofBijective` and its symmetric inverse.

The proof splits into `continuousMap_of_algHom_injective` (closed directly via
the per-prime `BijectiveOnStalks` identification `A_{q ∩ A} ≅ B_q` and the
injectivity of `C → ∏ p, Loc.AtPrime p.asIdeal`) and the substantive existence
half `exists_algHom_of_continuousMap` (which carries the genuinely
sheaf-theoretic content of Stacks 096L; see its docstring). -/
theorem continuousMap_of_algHom_bijective
    [Algebra.BijectiveOnStalks A B] [Algebra.BijectiveOnStalks A C] :
    Function.Bijective (continuousMap_of_algHom : (B →ₐ[A] C) → HomOver A B C) :=
  ⟨continuousMap_of_algHom_injective A B C,
    fun φ => exists_algHom_of_continuousMap A B C φ⟩

/-- The hom-set bijection
`(B →ₐ[A] C) ≃ HomOver A B C`
when both `A → B` and `A → C` identify local rings. Formalises Stacks 096L
(`thm:identifies-local-ring-to-top-fully-faithful`).

Constructed via `Equiv.ofBijective` from the forward direction
`continuousMap_of_algHom` and the bijectivity lemma
`continuousMap_of_algHom_bijective`. -/
noncomputable def algHomEquivContinuousMap
    [Algebra.BijectiveOnStalks A B] [Algebra.BijectiveOnStalks A C] :
    (B →ₐ[A] C) ≃ HomOver A B C :=
  Equiv.ofBijective continuousMap_of_algHom (continuousMap_of_algHom_bijective A B C)

/-- The `A`-algebra homomorphism `B →ₐ[A] C` induced by a continuous map
`Spec C → Spec B` over `Spec A`, when both `A → B` and `A → C` identify local
rings. This is the inverse direction of the hom-set bijection from Stacks
096L; its construction relies on the ringed-space identification
`𝒪_Y = p⁻¹ 𝒪_X` for `A → B` identifying local rings.

Defined as the inverse of `algHomEquivContinuousMap`. The substantive
content is concentrated in the bijectivity lemma
`continuousMap_of_algHom_bijective`. -/
noncomputable def algHom_of_continuousMap
    [Algebra.BijectiveOnStalks A B] [Algebra.BijectiveOnStalks A C]
    (φ : HomOver A B C) : B →ₐ[A] C :=
  (algHomEquivContinuousMap A B C).symm φ

end Algebra.BijectiveOnStalks
