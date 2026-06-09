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

/-- **LRS-route core for Stacks 096L existence (iter-155).**
Given the BijectiveOnStalks hypotheses on `A → B` and `A → C`, every
`φ : HomOver A B C` lifts to a ring map `f : B →+* C` which is `A`-linear and
realises `φ` as `PrimeSpectrum.comap f`.

Blueprint reference:
`lem:exists-algHom-of-continuousMap-via-LRS` in `local-structure.tex`
(iter-155 tightened). The intended proof follows the five-step LRS recipe:

1. Build `c : 𝒪_{Spec B} ⟶ φ_* 𝒪_{Spec C}` on a basic-open basis of `Spec B`
   via per-prime `IsLocalization.lift` and basic-open gluing on `Spec C`.
2. Verify the cocycle condition on basic-open intersections of `Spec B` by
   uniqueness of `IsLocalization.lift`.
3. Assemble via `TopCat.Sheaf.existsUnique_gluing` to land a single
   sheaf morphism `c` on `Spec B`.
4. Package `(φ.toContinuousMap, c)` as an LRS morphism `Φ` via
   `AlgebraicGeometry.LocallyRingedSpace.homMk` (the stalkwise-locality
   autoParam discharges via `Localization.isLocalHom_localRingHom`).
5. Extract `f : B →+* C` via
   `Spec.fullyFaithfulToLocallyRingedSpace.preimage Φ`. The round-trip
   identity certifies `Spec.map f = Φ` so `PrimeSpectrum.comap f = φ`. The
   over-`Spec A` structure forces `A`-linearity of `f`.

iter-153 counterexample (`B = ℚ[X]`, `C = ℚ[X, Y]`,
`φ p₁ = φ p₂ = (X)`, `α p₁ : X ↦ Y`, `α p₂ : X ↦ X`) refuted the
prior SSP-bypass helper that took independent per-prime `α p` data; the
present helper signature takes only the `HomOver` datum so coherence is
discharged automatically by factoring through the common base `A`. -/
private theorem exists_ringHom_of_homOver_lrs
    [Algebra.BijectiveOnStalks A B] [Algebra.BijectiveOnStalks A C]
    (φ : HomOver A B C) :
    ∃ f : B →+* C,
      (∀ a : A, f (algebraMap A B a) = algebraMap A C a) ∧
      (∀ p : PrimeSpectrum C, PrimeSpectrum.comap f p = φ p) := by
  classical
  -- ===== Step 0 (algebraic preparation, retained from iter-143) =====
  -- The over-Spec A compatibility gives the prime-contraction identity.
  have hcomap (p : PrimeSpectrum C) :
      (φ p).asIdeal.comap (algebraMap A B) = p.asIdeal.comap (algebraMap A C) :=
    congrArg PrimeSpectrum.asIdeal (φ.comp_comap_algebraMap p)
  -- Per-prime `BijectiveOnStalks A B` witness.
  have hKbij (p : PrimeSpectrum C) :
      Function.Bijective
        (Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) (φ p).asIdeal
          (algebraMap A B) rfl) :=
    Algebra.BijectiveOnStalks.bijective_localRingHom (R := A) (φ p).asIdeal
  -- Per-prime candidate ring map `M_p : B →+* C_p` via the chain
  --   `B → B_{φ p} ≅ A_{(φ p) ∩ A} = A_{p ∩ A} ≅⁻¹? B_{φ p} → C_p`.
  -- Concretely: `Lp ∘ Kinv ∘ algebraMap`, where `Kinv` inverts the
  -- `BijectiveOnStalks A B` localRingHom and `Lp` is the
  -- `localRingHom` of `algebraMap A C` for `φ p` ∩ A = p ∩ A`.
  let M : ∀ p : PrimeSpectrum C, B →+* Localization.AtPrime p.asIdeal := fun p =>
    haveI : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
    let Lp := Localization.localRingHom ((φ p).asIdeal.comap (algebraMap A B)) p.asIdeal
      (algebraMap A C) (hcomap p)
    let Kinv := (RingEquiv.ofBijective _ (hKbij p)).symm.toRingHom
    Lp.comp (Kinv.comp (algebraMap B (Localization.AtPrime (φ p).asIdeal)))
  -- Per-prime computation: `M p (algebraMap A B a) = algebraMap A C a` via
  -- the localRingHom chain. Useful both for A-linearity and the LRS step.
  have hM_alg (p : PrimeSpectrum C) (a : A) :
      M p (algebraMap A B a) = algebraMap A (Localization.AtPrime p.asIdeal) a := by
    haveI : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
    simp only [M, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [← Localization.localRingHom_to_map ((φ p).asIdeal.comap (algebraMap A B))
          (φ p).asIdeal (algebraMap A B) rfl a,
      ← RingEquiv.ofBijective_apply _ (hKbij p) (algebraMap A _ a),
      RingEquiv.symm_apply_apply,
      Localization.localRingHom_to_map,
      ← IsScalarTower.algebraMap_apply A C (Localization.AtPrime p.asIdeal) a]
  -- The bundled lift `B →+* ∏ p, C_p`.
  let lift : B →+* PrimeSpectrum.PiLocalization C := Pi.ringHom M
  -- ===== Steps 1-5 (LRS construction) =====
  --
  -- The substantive existence claim is the existence of a single ring map
  -- `f : B →+* C` such that
  --     `(toPiLocalization C).comp f = lift`,
  -- i.e. the per-prime family `M p` is the localisation of a single
  -- global section.
  --
  -- Per the blueprint, the LRS recipe constructs such an `f` as follows:
  -- Step 1: For each basic open `D(s) ⊆ Spec B` and basic-open cover
  --   `{D(t_i)}` of `φ⁻¹ D(s) ⊆ Spec C`, lift each composite
  --   `B → C → C[t_i⁻¹]` (which sends `s` to a unit) through
  --   `IsLocalization.lift` to a ring map `c_i : B[s⁻¹] → C[t_i⁻¹]`.
  -- Step 2: Cocycle on `D(t_i) ∩ D(t_j) = D(t_i t_j)` via uniqueness of
  --   `IsLocalization.lift`.
  -- Step 3: Glue via `TopCat.Sheaf.existsUnique_gluing` on the basic-open
  --   cover `{D(t_i)}` of `φ⁻¹ D(s)`, then assemble across `D(s)` ranging
  --   over basic opens of `Spec B`.
  -- Step 4: Package as an LRS morphism
  --   `Φ : Spec C ⟶ Spec B`
  --   via `AlgebraicGeometry.LocallyRingedSpace.homMk`. The stalkwise
  --   locality autoParam discharges via the chain
  --   `Localization.isLocalHom_localRingHom` instances at each prime.
  -- Step 5: Extract `f : B →+* C` via
  --   `Spec.fullyFaithfulToLocallyRingedSpace.preimage` applied to `Φ`.
  --   Round-trip identity:
  --     `Spec.map f = Φ`     (Functor.FullyFaithful.map_preimage)
  --   so the base topological component reads off as
  --     `PrimeSpectrum.comap f = φ.toContinuousMap`.
  --   A-linearity follows because each per-basic-open `c_{D(s)}` factors
  --   through `algebraMap A C` by construction in Step 1.
  --
  -- TYPED SORRY (iter-155): the residual obstruction is the construction
  -- of the basic-open `c` component (Steps 1-3) and its packaging through
  -- `LocallyRingedSpace.homMk` (Step 4). Steps 0 and 5 are mechanical
  -- given Step 4: the per-prime data above provides Step 1's per-prime
  -- ring maps and the A-linearity certificate.
  --
  -- The substantive content sits in:
  --   * `AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen`
  --     (for both `Γ(D(s), 𝒪_Spec B) = B[s⁻¹]` and
  --     `Γ(D(t_i), 𝒪_Spec C) = C[t_i⁻¹]`);
  --   * `IsLocalization.lift` (per-basic-open descent of `B → C[t_i⁻¹]`
  --     through `s ↦ unit`);
  --   * `TopCat.Sheaf.existsUnique_gluing` (basic-open cover of
  --     `φ⁻¹ D(s)`);
  --   * `AlgebraicGeometry.LocallyRingedSpace.homMk` (LRS packaging);
  --   * `Spec.fullyFaithfulToLocallyRingedSpace.preimage` /
  --     `Functor.FullyFaithful.map_preimage` (Step 5 extraction).
  --
  -- All Mathlib carriers are verified to exist; the missing piece is the
  -- Lean-level basic-open `c` construction and the LRS round-trip
  -- assembly (≈300-400 LOC of sheaf-condition + AffineScheme API
  -- bookkeeping). See blueprint chapter `lem:exists-algHom-of-continuousMap-via-LRS`
  -- and the iter-155 PROGRESS.md objective for the full recipe.
  --
  -- The per-prime preparation above (`M`, `hM_alg`) is the algebraic
  -- substrate of Step 1 and is reused in the consumer's verification.
  --
  -- Step 1 substrate (iter-156): the per-prime ring map `M p` sends every
  -- `s : B` with `s ∉ (φ p).asIdeal` to a unit in `Localization.AtPrime
  -- p.asIdeal`. This is the input that `IsLocalization.Away.lift` needs to
  -- descend `M p` along `B → B[s⁻¹]`, producing the per-prime ring map
  -- `B[s⁻¹] →+* C_p` invoked in the blueprint's basic-open construction.
  have hM_unit (p : PrimeSpectrum C) (s : B) (hs : s ∉ (φ p).asIdeal) :
      IsUnit (M p s) := by
    haveI : ((φ p).asIdeal.comap (algebraMap A B)).IsPrime := Ideal.IsPrime.comap _
    -- Unfold `M p s = Lp (Kinv (algebraMap B (Loc (φ p)) s))`.
    simp only [M, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    -- The image of `s` in `Loc (φ p)` is a unit because `s ∉ (φ p).asIdeal`.
    have hs1 : IsUnit (algebraMap B (Localization.AtPrime (φ p).asIdeal) s) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (Localization.AtPrime (φ p).asIdeal) (φ p).asIdeal s).mpr hs
    -- `RingEquiv` and any `RingHom` preserve units.
    exact (Localization.localRingHom _ _ (algebraMap A C) (hcomap p)).isUnit_map
      ((RingEquiv.ofBijective _ (hKbij p)).symm.toRingHom.isUnit_map hs1)
  -- Per-prime descent: `M p` factors as `B → B[s⁻¹] → C_p` via
  -- `IsLocalization.Away.lift`. This is the per-prime piece of Step 1,
  -- now available as a ring map (parameterised over `s` and the
  -- membership witness). Its uniqueness on the algebraic substrate is
  -- enforced by `IsLocalization.Away.lift_eq`.
  let cAtPrime : ∀ (p : PrimeSpectrum C) (s : B) (_ : s ∉ (φ p).asIdeal),
      Localization.Away s →+* Localization.AtPrime p.asIdeal := fun p s hs =>
    IsLocalization.Away.lift (S := Localization.Away s) s (hM_unit p s hs)
  -- The defining equation: `cAtPrime p s hs` extends `M p` along
  -- `B → B[s⁻¹]`. Used in Step 1 to identify the basic-open component
  -- pointwise with the per-prime maps.
  have cAtPrime_apply (p : PrimeSpectrum C) (s : B) (hs : s ∉ (φ p).asIdeal)
      (b : B) :
      cAtPrime p s hs (algebraMap B (Localization.Away s) b) = M p b :=
    IsLocalization.Away.lift_eq s (hM_unit p s hs) b
  -- The A-linearity reading on the per-prime descent: for `a : A`, the
  -- composite `A → B → B[s⁻¹] → C_p` equals `algebraMap A C_p`. This is
  -- the A-coherence input that propagates through Step 1's gluing and
  -- ultimately certifies A-linearity of the final `f`.
  have cAtPrime_alg (p : PrimeSpectrum C) (s : B) (hs : s ∉ (φ p).asIdeal)
      (a : A) :
      cAtPrime p s hs (algebraMap B (Localization.Away s) (algebraMap A B a)) =
        algebraMap A (Localization.AtPrime p.asIdeal) a := by
    rw [cAtPrime_apply p s hs, hM_alg]
  -- The remaining Step 1-3 work (basic-open gluing, cocycle, sheaf
  -- assembly) and Steps 4-5 (LRS packaging + `Spec.preimage`) are not
  -- yet discharged at the Lean level; see blueprint chapter
  -- `lem:exists-algHom-of-continuousMap-via-LRS`. The above `cAtPrime`
  -- substrate is the load-bearing per-prime ring map invoked in the
  -- blueprint's Step 1 construction; it is retained here so subsequent
  -- iterations can graft the basic-open gluing layer on top without
  -- redeveloping the per-prime descent.
  -- Retain the substrate names visible to elaboration for downstream use.
  let _cAtPrime := cAtPrime
  have _cAtPrime_apply := cAtPrime_apply
  have _cAtPrime_alg := cAtPrime_alg
  sorry

/-- **Substantive existence (Stacks 096L)**: every `(φ, h) : HomOver A B C`
arises from an `A`-algebra homomorphism `f : B →ₐ[A] C`.

iter-155: rewritten against the LRS-route recipe in blueprint chapter
`lem:exists-algHom-of-continuousMap-via-LRS`. The substantive content is
extracted to the typed helper `exists_ringHom_of_homOver_lrs`; this
consumer just promotes the resulting `f` to a `B →ₐ[A] C` and verifies
`continuousMap_of_algHom f = φ` via `HomOver.ext`. -/
private theorem exists_algHom_of_continuousMap
    [Algebra.BijectiveOnStalks A B] [Algebra.BijectiveOnStalks A C]
    (φ : HomOver A B C) : ∃ f : B →ₐ[A] C, continuousMap_of_algHom f = φ := by
  -- iter-155: rewrite against the LRS-route recipe in blueprint chapter
  -- `lem:exists-algHom-of-continuousMap-via-LRS`. The substantive LRS-route
  -- existence claim is concentrated in the typed helper
  -- `exists_ringHom_of_homOver_lrs`. This consumer extracts `f`, promotes it
  -- to a `B →ₐ[A] C` via the A-linearity witness, and discharges
  -- `continuousMap_of_algHom f = φ` via `HomOver.ext` and the
  -- `PrimeSpectrum.comap f = φ` witness.
  obtain ⟨f, hfA, hcomapf⟩ := exists_ringHom_of_homOver_lrs A B C φ
  refine ⟨{ f with commutes' := hfA }, ?_⟩
  apply HomOver.ext
  intro p
  -- (continuousMap_of_algHom { f with commutes' := hfA }) p
  --   = PrimeSpectrum.comap f p = φ p.
  exact hcomapf p

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
