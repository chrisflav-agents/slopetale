/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Proetale.Algebra.LocalIso
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-!
# Spreading of local isomorphisms

This file develops descent (`PreIndSpreads`) and base change stability for the
property `RingHom.IsLocalIso`. The main results are:

- `Algebra.IsLocalIso.baseChange`: base change of a local iso is local iso.
- `(RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderCobaseChange`: the
  categorical form of base change stability.
- `(RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderComposition`: from
  `Algebra.IsLocalIso.trans`.
- `PreIndSpreads (RingHom.toMorphismProperty RingHom.IsLocalIso)`: the spreading
  lemma — descent reduces to an `Algebra.IsLocalIso.exists_subalgebra_fg` analogue.

These instances allow `Algebra.IndZariski.trans` to be proved by appealing to
`MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads`. The strategies
for each are documented above each declaration.
-/

universe u

open CategoryTheory Limits TensorProduct

namespace Algebra.IsLocalIso

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    {T : Type u} [CommRing T] [Algebra R T]

/-- `algebraMap T (Localization.Away (1 ⊗ g)) g` is a unit. -/
private lemma isUnit_algebraMap_T_localizationAway_oneTmul (g : T) :
    IsUnit (algebraMap T (Localization.Away ((1 : S) ⊗ₜ[R] g)) g) := by
  show IsUnit ((algebraMap (S ⊗[R] T) (Localization.Away ((1 : S) ⊗ₜ[R] g)))
    ((algebraMap T (S ⊗[R] T)) g))
  rw [show (algebraMap T (S ⊗[R] T)) g = (1 : S) ⊗ₜ[R] g from rfl]
  exact IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away ((1 : S) ⊗ₜ[R] g)) ((1 : S) ⊗ₜ[R] g)

/-- The natural `R`-algebra hom `S ⊗[R] T → S ⊗[R] Localization.Away g`. -/
private noncomputable def baseChangeToLocalization (g : T) :
    (S ⊗[R] T) →ₐ[R] (S ⊗[R] Localization.Away g) :=
  Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R T (Localization.Away g))

private lemma baseChangeToLocalization_tmul (g : T) (s : S) (t : T) :
    baseChangeToLocalization S g (s ⊗ₜ[R] t) =
      s ⊗ₜ[R] algebraMap T (Localization.Away g) t := by
  show Algebra.TensorProduct.map _ _ (s ⊗ₜ t) = _
  rw [Algebra.TensorProduct.map_tmul]; rfl

private lemma baseChangeToLocalization_oneTmul_isUnit (g : T) :
    IsUnit (baseChangeToLocalization S g ((1 : S) ⊗ₜ[R] g)) := by
  rw [show baseChangeToLocalization S g ((1 : S) ⊗ₜ[R] g) =
    1 ⊗ₜ[R] algebraMap T (Localization.Away g) g from baseChangeToLocalization_tmul S g 1 g]
  exact (Algebra.TensorProduct.includeRight (R := R) (A := S)
    (B := Localization.Away g)).isUnit_map (IsLocalization.Away.algebraMap_isUnit g)

/-- The `R`-algebra hom `Loc g →ₐ[R] Loc ((1:S) ⊗ₜ g)` lifting the algebra map
`T → Loc ((1:S) ⊗ₜ g)` (which sends `g` to a unit). -/
private noncomputable def liftAwayAlgHomR (g : T) :
    Localization.Away g →ₐ[R] Localization.Away ((1 : S) ⊗ₜ[R] g) :=
  IsLocalization.liftAlgHom (A := R)
    (M := Submonoid.powers g) (S := Localization.Away g)
    (P := Localization.Away ((1 : S) ⊗ₜ[R] g))
    (f := IsScalarTower.toAlgHom R T (Localization.Away ((1 : S) ⊗ₜ[R] g)))
    (fun y => by
      obtain ⟨n, hn⟩ := y.2
      show IsUnit ((algebraMap T (Localization.Away ((1 : S) ⊗ₜ[R] g))) (y : T))
      rw [show (y : T) = g ^ n from hn.symm, map_pow]
      exact (isUnit_algebraMap_T_localizationAway_oneTmul S g).pow n)

private lemma liftAwayAlgHomR_algebraMap (g : T) (t : T) :
    liftAwayAlgHomR S g (algebraMap T (Localization.Away g) t) =
      algebraMap T (Localization.Away ((1 : S) ⊗ₜ[R] g)) t := by
  show IsLocalization.lift (M := Submonoid.powers g)
    (S := Localization.Away g) (P := Localization.Away ((1 : S) ⊗ₜ[R] g))
    _ (algebraMap T (Localization.Away g) t) = _
  rw [IsLocalization.lift_eq]
  rfl

/-- `baseChangeToLocalization` as an `S`-algebra hom. -/
private noncomputable def baseChangeAlg (g : T) :
    (S ⊗[R] T) →ₐ[S] (S ⊗[R] Localization.Away g) :=
  Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom R T (Localization.Away g))

private lemma baseChangeAlg_tmul (g : T) (s : S) (t : T) :
    baseChangeAlg S g (s ⊗ₜ[R] t) = s ⊗ₜ[R] algebraMap T (Localization.Away g) t :=
  Algebra.TensorProduct.map_tmul _ _ _ _

private lemma baseChangeAlg_oneTmul_isUnit (g : T) :
    IsUnit (baseChangeAlg S g ((1 : S) ⊗ₜ[R] g)) := by
  rw [baseChangeAlg_tmul]
  exact (Algebra.TensorProduct.includeRight (R := R) (A := S)
    (B := Localization.Away g)).isUnit_map (IsLocalization.Away.algebraMap_isUnit g)

/-- The backward `S`-algebra hom of the tensor-localization equivalence. -/
private noncomputable def bwdAlgHom (g : T) :
    Localization.Away ((1 : S) ⊗ₜ[R] g) →ₐ[S] (S ⊗[R] Localization.Away g) :=
  IsLocalization.liftAlgHom (A := S)
    (M := Submonoid.powers ((1 : S) ⊗ₜ[R] g))
    (S := Localization.Away ((1 : S) ⊗ₜ[R] g))
    (f := baseChangeAlg S g)
    (fun y => by
      obtain ⟨n, hn⟩ := y.2
      rw [show (y : S ⊗[R] T) = ((1 : S) ⊗ₜ[R] g) ^ n from hn.symm, map_pow]
      exact (baseChangeAlg_oneTmul_isUnit S g).pow n)

private lemma bwdAlgHom_algebraMap (g : T) (x : S ⊗[R] T) :
    bwdAlgHom S g (algebraMap (S ⊗[R] T) _ x) = baseChangeAlg S g x := by
  show IsLocalization.lift (M := Submonoid.powers ((1 : S) ⊗ₜ[R] g))
    (S := Localization.Away ((1 : S) ⊗ₜ[R] g)) _ (algebraMap (S ⊗[R] T) _ x) = _
  rw [IsLocalization.lift_eq]
  rfl

/-- The forward `S`-algebra hom of the tensor-localization equivalence. -/
private noncomputable def fwdAlgHom (g : T) :
    (S ⊗[R] Localization.Away g) →ₐ[S] Localization.Away ((1 : S) ⊗ₜ[R] g) :=
  Algebra.TensorProduct.lift
    (Algebra.ofId S (Localization.Away ((1 : S) ⊗ₜ[R] g)))
    (liftAwayAlgHomR S g)
    (fun _ _ => Commute.all _ _)

private lemma fwdAlgHom_tmul (g : T) (s : S) (ℓ : Localization.Away g) :
    fwdAlgHom S g (s ⊗ₜ ℓ) =
      algebraMap S (Localization.Away ((1 : S) ⊗ₜ[R] g)) s * liftAwayAlgHomR S g ℓ :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

private lemma fwd_bwd_algebraMap (g : T) (x : S ⊗[R] T) :
    fwdAlgHom S g (bwdAlgHom S g (algebraMap (S ⊗[R] T) _ x)) =
      algebraMap (S ⊗[R] T) (Localization.Away ((1 : S) ⊗ₜ[R] g)) x := by
  rw [bwdAlgHom_algebraMap]
  induction x with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, ← map_add]
  | tmul s t =>
    rw [baseChangeAlg_tmul, fwdAlgHom_tmul, liftAwayAlgHomR_algebraMap]
    rw [show ((s ⊗ₜ[R] t) : S ⊗[R] T) = (s ⊗ₜ[R] (1 : T)) * ((1 : S) ⊗ₜ[R] t) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    rw [map_mul,
      show ((s ⊗ₜ[R] (1 : T)) : S ⊗[R] T) = algebraMap S (S ⊗[R] T) s from rfl,
      show (((1 : S) ⊗ₜ[R] t) : S ⊗[R] T) = algebraMap T (S ⊗[R] T) t from rfl,
      ← IsScalarTower.algebraMap_apply S (S ⊗[R] T),
      ← IsScalarTower.algebraMap_apply T (S ⊗[R] T)]

/-- Key intermediate: `bwd ∘ liftAwayAlgHomR ℓ = 1 ⊗ ℓ`. -/
private lemma bwd_comp_liftAwayAlgHomR (g : T) (ℓ : Localization.Away g) :
    bwdAlgHom (R := R) S g (liftAwayAlgHomR (R := R) S g ℓ) = (1 : S) ⊗ₜ[R] ℓ := by
  have key (t : T) : bwdAlgHom (R := R) S g (liftAwayAlgHomR (R := R) S g
        (algebraMap T (Localization.Away g) t)) =
      ((1 : S) ⊗ₜ[R] algebraMap T (Localization.Away g) t) := by
    rw [liftAwayAlgHomR_algebraMap]
    show bwdAlgHom S g (algebraMap (S ⊗[R] T) _ (1 ⊗ₜ[R] t)) = _
    rw [bwdAlgHom_algebraMap, baseChangeAlg_tmul]
  -- Lift to all ℓ via ringHom_ext on Submonoid.powers g
  have hext : (bwdAlgHom (R := R) S g).toRingHom.comp
        (liftAwayAlgHomR (R := R) S g).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R) (A := S)
        (B := Localization.Away g)).toRingHom :=
    IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext key)
  exact DFunLike.congr_fun hext ℓ

private lemma bwd_fwd_tmul (g : T) (s : S) (ℓ : Localization.Away g) :
    bwdAlgHom (R := R) S g (fwdAlgHom (R := R) S g (s ⊗ₜ[R] ℓ)) = s ⊗ₜ[R] ℓ := by
  rw [fwdAlgHom_tmul, map_mul]
  -- bwd on algebraMap S → Loc.Away ((1:S)⊗ₜg) sends s ↦ s ⊗ 1
  have h₁ : bwdAlgHom (R := R) S g
        (algebraMap S (Localization.Away ((1 : S) ⊗ₜ[R] g)) s) =
      s ⊗ₜ[R] (1 : Localization.Away g) := by
    rw [show algebraMap S (Localization.Away ((1 : S) ⊗ₜ[R] g)) s =
      algebraMap (S ⊗[R] T) _ (s ⊗ₜ[R] (1 : T)) from rfl,
      bwdAlgHom_algebraMap, baseChangeAlg_tmul, map_one]
  rw [h₁, bwd_comp_liftAwayAlgHomR, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private lemma fwd_comp_bwd_eq (g : T) :
    (fwdAlgHom (R := R) S g).comp (bwdAlgHom (R := R) S g) =
      AlgHom.id S (Localization.Away ((1 : S) ⊗ₜ[R] g)) := by
  apply AlgHom.coe_ringHom_injective
  show ((fwdAlgHom (R := R) S g).comp (bwdAlgHom (R := R) S g)).toRingHom = (RingHom.id _)
  refine IsLocalization.ringHom_ext (M := Submonoid.powers ((1 : S) ⊗ₜ[R] g))
    (S := Localization.Away ((1 : S) ⊗ₜ[R] g)) ?_
  refine RingHom.ext (fun x => ?_)
  show fwdAlgHom S g (bwdAlgHom S g (algebraMap _ _ x)) = algebraMap _ _ x
  exact fwd_bwd_algebraMap S g x

private lemma bwd_comp_fwd_eq (g : T) :
    (bwdAlgHom (R := R) S g).comp (fwdAlgHom (R := R) S g) =
      AlgHom.id S (S ⊗[R] Localization.Away g) :=
  Algebra.TensorProduct.ext' fun s ℓ => bwd_fwd_tmul S g s ℓ

/-- The `S`-algebra equivalence `S ⊗[R] Loc.Away g ≃ₐ[S] Loc.Away ((1:S) ⊗ₜ g)`. -/
private noncomputable def tensorLocAwayAlgEquiv (g : T) :
    (S ⊗[R] Localization.Away g) ≃ₐ[S] Localization.Away ((1 : S) ⊗ₜ[R] g) :=
  AlgEquiv.ofAlgHom (fwdAlgHom (R := R) S g) (bwdAlgHom (R := R) S g)
    (fwd_comp_bwd_eq S g) (bwd_comp_fwd_eq S g)

/-- Helper for `Algebra.IsLocalIso.baseChange`: if `R → T[1/g]` is a standard open immersion,
then so is `S → (S ⊗[R] T)[1/(1 ⊗ g)]`.

Strategy: transfer the Mathlib instance
`Algebra.IsStandardOpenImmersion S (S ⊗[R] Localization.Away g)` along the `S`-algebra
equivalence `tensorLocAwayAlgEquiv : (S ⊗[R] Loc g) ≃ₐ[S] Loc ((1:S) ⊗ₜ g)`. -/
lemma isStandardOpenImmersion_localization_away_includeRight (g : T)
    [Algebra.IsStandardOpenImmersion R (Localization.Away g)] :
    Algebra.IsStandardOpenImmersion S
      (Localization.Away ((Algebra.TensorProduct.includeRight
        (R := R) (A := S) (B := T)).toRingHom g)) := by
  show Algebra.IsStandardOpenImmersion S (Localization.Away ((1 : S) ⊗ₜ[R] g))
  have h : Algebra.IsStandardOpenImmersion S (S ⊗[R] Localization.Away g) := inferInstance
  exact Algebra.IsStandardOpenImmersion.of_algEquiv S _ _ (tensorLocAwayAlgEquiv S g)

/-- Base change of a local isomorphism is a local isomorphism.

Strategy: cover `T` by `{g_α : T}` with `R → T[1/g_α]` standard open immersion.
For each `α`, the base change `(S ⊗[R] T)[1/(1 ⊗ g_α)] ≅ S ⊗[R] T[1/g_α]` is a
standard open immersion of `S` (base change of `IsStandardOpenImmersion`).
Since the `1 ⊗ g_α` span the top ideal of `S ⊗[R] T`, this gives the local iso
structure on `S → S ⊗[R] T`. -/
instance baseChange [Algebra.IsLocalIso R T] :
    Algebra.IsLocalIso S (S ⊗[R] T) := by
  refine (Algebra.IsLocalIso.iff_span_isStandardOpenImmersion_eq_top S (S ⊗[R] T)).mpr ?_
  rw [_root_.eq_top_iff]
  -- The image of the standard-open-immersion elements of `T` under `includeRight`
  -- generates `⊤` in `S ⊗[R] T`.
  let φ : T →+* S ⊗[R] T :=
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)).toRingHom
  have hspan_T :
      Ideal.span {g : T | Algebra.IsStandardOpenImmersion R (Localization.Away g)} = ⊤ :=
    Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top R T
  calc (⊤ : Ideal (S ⊗[R] T))
      = Ideal.map φ ⊤ := (Ideal.map_top φ).symm
    _ = Ideal.map φ
          (Ideal.span {g : T | Algebra.IsStandardOpenImmersion R (Localization.Away g)}) := by
            rw [hspan_T]
    _ = Ideal.span (φ '' {g : T | Algebra.IsStandardOpenImmersion R (Localization.Away g)}) :=
        Ideal.map_span _ _
    _ ≤ Ideal.span
          {g' : S ⊗[R] T | Algebra.IsStandardOpenImmersion S (Localization.Away g')} := by
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨g, hg, rfl⟩
        apply Ideal.subset_span
        show Algebra.IsStandardOpenImmersion S (Localization.Away (φ g))
        haveI : Algebra.IsStandardOpenImmersion R (Localization.Away g) := hg
        exact isStandardOpenImmersion_localization_away_includeRight S g

end Algebra.IsLocalIso

namespace CategoryTheory.MorphismProperty

open CategoryTheory Limits

/-- `RingHom.IsLocalIso` is stable under base change (in the ring-hom sense): if `R → T`
is a local iso, the base change `S → S ⊗[R] T` is also a local iso. -/
lemma _root_.RingHom.IsLocalIso.isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange (fun {_ _} _ _ f => f.IsLocalIso) := by
  refine RingHom.IsStableUnderBaseChange.mk RingHom.IsLocalIso.respectsIso ?_
  intro R S T _ _ _ _ _ hRT
  rw [RingHom.isLocalIso_algebraMap] at hRT ⊢
  letI : Algebra.IsLocalIso R T := hRT
  exact Algebra.IsLocalIso.baseChange S

/-- The morphism property `RingHom.IsLocalIso` is stable under cobase change.

Strategy: convert the pushout square in `CommRingCat` to an `Algebra.IsPushout`,
then use `Algebra.IsLocalIso.baseChange` to transport the local iso structure
through the iso `A' ⊗[A] B ≃ B'`. -/
instance isLocalIso_isStableUnderCobaseChange :
    (RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderCobaseChange := by
  rw [show (RingHom.toMorphismProperty RingHom.IsLocalIso) =
      RingHom.toMorphismProperty (fun {_ _} _ _ f => f.IsLocalIso) from rfl,
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.IsLocalIso.isStableUnderBaseChange

/-- The morphism property `RingHom.IsLocalIso` is stable under composition. This
follows from `Algebra.IsLocalIso.trans`. -/
instance isLocalIso_isStableUnderComposition :
    (RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderComposition where
  comp_mem f g hf hg := by
    show (g.hom.comp f.hom).IsLocalIso
    exact hg.comp hf

/-- Helper for the descent of a partition of unity from `S` to `S₀`. Given an `R`-algebra
iso `e : S ≃ₐ[R] R ⊗[R₀et] S₀et`, an injective inclusion `R₀ → R` of an `R₀et`-subalgebra
of `R`, and a flat `R₀et`-module `S₀et`, the map `x ↦ e.symm (cancelBaseChange (1 ⊗ x))`
from `R₀ ⊗[R₀et] S₀et → S` is injective. -/
private lemma _root_.Algebra.IsLocalIso.descent_oneTmul_injective
    {R₀et : Type u} [CommRing R₀et] {R₀ R : Type u} [CommRing R₀] [CommRing R]
    [Algebra R₀et R₀] [Algebra R₀ R] [Algebra R₀et R] [IsScalarTower R₀et R₀ R]
    (hinj : Function.Injective (algebraMap R₀ R))
    (S₀et : Type u) [CommRing S₀et] [Algebra R₀et S₀et] [Module.Flat R₀et S₀et]
    {S : Type u} [CommRing S] [Algebra R S] (e : S ≃ₐ[R] R ⊗[R₀et] S₀et) :
    Function.Injective
      (fun x : R₀ ⊗[R₀et] S₀et =>
        e.symm
          (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et ((1 : R) ⊗ₜ[R₀] x))) := by
  let valR₀ : R₀ →ₐ[R₀et] R := IsScalarTower.toAlgHom R₀et R₀ R
  have hval_inj : Function.Injective (valR₀.toLinearMap : R₀ →ₗ[R₀et] R) := hinj
  have hθ_inj : Function.Injective (valR₀.toLinearMap.rTensor S₀et) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hval_inj
  have hθ_eq : ∀ z : R₀ ⊗[R₀et] S₀et,
      Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et ((1 : R) ⊗ₜ[R₀] z) =
        valR₀.toLinearMap.rTensor S₀et z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, ha, hb, map_add]
    | tmul a b =>
      rw [Algebra.TensorProduct.cancelBaseChange_tmul, LinearMap.rTensor_tmul]
      congr 1
      show a • (1 : R) = (algebraMap R₀ R) a
      rw [Algebra.smul_def, mul_one]
  intro x y hxy
  exact hθ_inj (by rw [← hθ_eq, ← hθ_eq]; exact e.symm.injective hxy)

/-- Helper for `exists_subalgebra_fg_descent`: if `r` makes `Localization.Away g` an
`IsLocalization.Away r` over `R`, then `(algebraMap R S) r` divides some power of `g`. -/
private lemma _root_.Algebra.IsLocalIso.divisibility_witness
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (g : S) (r : R) [IsLocalization.Away r (Localization.Away g)] :
    ∃ n : ℕ, ∃ c : S, g ^ n = (algebraMap R S) r * c := by
  have h1 : IsUnit ((algebraMap R (Localization.Away g)) r) :=
    IsLocalization.Away.algebraMap_isUnit r
  have h2 : IsUnit ((algebraMap S (Localization.Away g)) ((algebraMap R S) r)) := by
    rw [← IsScalarTower.algebraMap_apply]; exact h1
  have h3 : ∃ n, (algebraMap R S) r ∣ g ^ n :=
    (IsLocalization.Away.algebraMap_isUnit_iff g).mp h2
  obtain ⟨n, c, hc⟩ := h3
  exact ⟨n, c, hc⟩

/-- Helper for `exists_subalgebra_fg_descent`: the bridge equation. If `e x ∈ R ⊗[R₀et] S₀et`
has a finite tensor representation whose R-coefficients lift to `R₀`, the corresponding lift
in `R₀ ⊗[R₀et] S₀et` maps back to `x` under `e.symm ∘ cancelBaseChange ∘ (1 ⊗ ·)`. -/
private lemma _root_.Algebra.IsLocalIso.descent_bridge
    {R₀et : Type u} [CommRing R₀et] {R₀ R : Type u} [CommRing R₀] [CommRing R]
    [Algebra R₀et R₀] [Algebra R₀ R] [Algebra R₀et R] [IsScalarTower R₀et R₀ R]
    (S₀et : Type u) [CommRing S₀et] [Algebra R₀et S₀et]
    {S : Type u} [CommRing S] [Algebra R S] (e : S ≃ₐ[R] R ⊗[R₀et] S₀et)
    {T : Finset (R × S₀et)} (lift : ∀ ab ∈ T, R₀)
    (hlift : ∀ ab (hab : ab ∈ T), (algebraMap R₀ R (lift ab hab) : R) = ab.1)
    {x : S} (hxT : e x = ∑ ab ∈ T, ab.1 ⊗ₜ[R₀et] ab.2) :
    e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
      ((1 : R) ⊗ₜ[R₀]
        ∑ ab ∈ T.attach, lift ab.1 ab.2 ⊗ₜ[R₀et] ab.1.2)) = x := by
  have hcancel :
      Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
        ((1 : R) ⊗ₜ[R₀] ∑ ab ∈ T.attach, lift ab.1 ab.2 ⊗ₜ[R₀et] ab.1.2) = e x := by
    rw [TensorProduct.tmul_sum, map_sum, hxT, ← Finset.sum_attach T]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [Algebra.TensorProduct.cancelBaseChange_tmul]
    congr 1
    rw [Algebra.smul_def, mul_one]
    exact hlift ab.1 ab.2
  rw [hcancel, AlgEquiv.symm_apply_apply]

/-- Helper for `exists_subalgebra_fg_descent`: lift a partition of unity from `S` to `S₀`.

Given:
- An `R`-algebra iso `e : S ≃ₐ[R] R ⊗[R₀et] S₀et`,
- An injective inclusion `algebraMap R₀ R` of an `R₀et`-subalgebra of `R`,
- Flatness of `S₀et` over `R₀et` (e.g. from `Algebra.Etale R₀et S₀et`),
- A finite cover `t` with partition of unity `∑ a ∈ t, f a • a = 1` in `S`,
- Lifts `g₀, fg₀ : ∀ g ∈ t, R₀ ⊗[R₀et] S₀et` such that the descent iso
  sends `1 ⊗ g₀ g hg ↦ g` and `1 ⊗ fg₀ g hg ↦ f g`,

then the lifted partition of unity holds in `S₀ = R₀ ⊗[R₀et] S₀et`. -/
private lemma _root_.Algebra.IsLocalIso.descent_partition_of_unity_lift
    {R₀et : Type u} [CommRing R₀et] {R₀ R : Type u} [CommRing R₀] [CommRing R]
    [Algebra R₀et R₀] [Algebra R₀ R] [Algebra R₀et R] [IsScalarTower R₀et R₀ R]
    (hinj : Function.Injective (algebraMap R₀ R))
    (S₀et : Type u) [CommRing S₀et] [Algebra R₀et S₀et] [Module.Flat R₀et S₀et]
    {S : Type u} [CommRing S] [Algebra R S] (e : S ≃ₐ[R] R ⊗[R₀et] S₀et)
    {t : Finset S} {f : S → S} (hsum : ∑ a ∈ t, f a • a = (1 : S))
    (g₀ fg₀ : ∀ (g : S), g ∈ t → R₀ ⊗[R₀et] S₀et)
    (hbridge : ∀ (g : S) (hg : g ∈ t),
      e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
        ((1 : R) ⊗ₜ[R₀] g₀ g hg)) = g)
    (hbridge_f : ∀ (g : S) (hg : g ∈ t),
      e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
        ((1 : R) ⊗ₜ[R₀] fg₀ g hg)) = f g) :
    ∑ g ∈ t.attach, fg₀ g.1 g.2 • g₀ g.1 g.2 = (1 : R₀ ⊗[R₀et] S₀et) := by
  -- Define ψ : R₀ ⊗ S₀et →+* S as `x ↦ e.symm (cancelBaseChange (1 ⊗ x))`.
  -- It's a ring hom (composition of ring homs).
  let ψ : R₀ ⊗[R₀et] S₀et →+* S :=
    e.symm.toAlgHom.toRingHom.comp
      ((Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := R₀) (A := R) (B := R₀ ⊗[R₀et] S₀et)).toRingHom)
  have hψ_inj : Function.Injective ψ :=
    Algebra.IsLocalIso.descent_oneTmul_injective hinj S₀et e
  have hψg : ∀ (g : S) (hg : g ∈ t), ψ (g₀ g hg) = g := hbridge
  have hψfg : ∀ (g : S) (hg : g ∈ t), ψ (fg₀ g hg) = f g := hbridge_f
  apply hψ_inj
  rw [map_one, map_sum]
  rw [show (1 : S) = ∑ a ∈ t, f a • a from hsum.symm]
  rw [← Finset.sum_attach (s := t) (f := fun a => f a • a)]
  refine Finset.sum_congr rfl fun ⟨g, hg⟩ _ => ?_
  rw [smul_eq_mul, map_mul, hψg g hg, hψfg g hg, smul_eq_mul]

/-- Helper for `exists_subalgebra_fg_descent`, sub-lemma (C): the lifted divisibility relation
in `S₀ = R₀ ⊗[R₀et] S₀et`.

Given:
- The descent setup: `R₀et ≤ R₀ ≤ R`, `e : S ≃ₐ[R] R ⊗[R₀et] S₀et`, with `Module.Flat R₀et S₀et`
  and injective `algebraMap R₀ R`.
- A divisibility witness in `S`: `g ^ n = (algebraMap R S)(algebraMap R₀ R r₀) * cg`.
- Lifts `g₀, c₀ : R₀ ⊗[R₀et] S₀et` of `g, cg` along
  `ψ := e.symm ∘ cancelBaseChange ∘ (1 ⊗ ·)`.

Then the lifted divisibility holds in `R₀ ⊗[R₀et] S₀et`:
`g₀ ^ n = (algebraMap R₀ (R₀ ⊗[R₀et] S₀et)) r₀ * c₀`. -/
private lemma _root_.Algebra.IsLocalIso.descent_lifted_divisibility
    {R₀et : Type u} [CommRing R₀et] {R₀ R : Type u} [CommRing R₀] [CommRing R]
    [Algebra R₀et R₀] [Algebra R₀ R] [Algebra R₀et R] [IsScalarTower R₀et R₀ R]
    (hinj : Function.Injective (algebraMap R₀ R))
    {S₀et : Type u} [CommRing S₀et] [Algebra R₀et S₀et] [Module.Flat R₀et S₀et]
    {S : Type u} [CommRing S] [Algebra R S] (e : S ≃ₐ[R] R ⊗[R₀et] S₀et)
    (g : S) (r₀ : R₀) (cg : S) (n : ℕ)
    (hdvd_S : g ^ n = (algebraMap R S) ((algebraMap R₀ R) r₀) * cg)
    (g₀ c₀ : R₀ ⊗[R₀et] S₀et)
    (hbridge_g : e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
      ((1 : R) ⊗ₜ[R₀] g₀)) = g)
    (hbridge_c : e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
      ((1 : R) ⊗ₜ[R₀] c₀)) = cg) :
    g₀ ^ n = (algebraMap R₀ (R₀ ⊗[R₀et] S₀et)) r₀ * c₀ := by
  let ψ : R₀ ⊗[R₀et] S₀et →+* S :=
    e.symm.toAlgHom.toRingHom.comp
      ((Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et).toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := R₀) (A := R) (B := R₀ ⊗[R₀et] S₀et)).toRingHom)
  have hψ_inj : Function.Injective ψ :=
    Algebra.IsLocalIso.descent_oneTmul_injective hinj S₀et e
  have hψg : ψ g₀ = g := hbridge_g
  have hψc : ψ c₀ = cg := hbridge_c
  have hψr : ψ ((algebraMap R₀ (R₀ ⊗[R₀et] S₀et)) r₀) =
      (algebraMap R S) ((algebraMap R₀ R) r₀) := by
    show e.symm
      (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
        ((1 : R) ⊗ₜ[R₀] ((algebraMap R₀ (R₀ ⊗[R₀et] S₀et)) r₀))) = _
    rw [show ((algebraMap R₀ (R₀ ⊗[R₀et] S₀et)) r₀) = r₀ ⊗ₜ[R₀et] (1 : S₀et) from rfl,
      Algebra.TensorProduct.cancelBaseChange_tmul R₀et R₀ R R S₀et (1 : R) r₀ (1 : S₀et)]
    -- (r₀ • 1 : R) ⊗ₜ[R₀et] (1 : S₀et) = (algebraMap R₀ R r₀) ⊗ₜ[R₀et] 1
    rw [show (r₀ • (1 : R)) ⊗ₜ[R₀et] (1 : S₀et) =
        (algebraMap R (R ⊗[R₀et] S₀et)) ((algebraMap R₀ R) r₀) by
      show _ = ((algebraMap R₀ R) r₀) ⊗ₜ[R₀et] (1 : S₀et)
      rw [Algebra.smul_def, mul_one]]
    exact e.symm.commutes ((algebraMap R₀ R) r₀)
  apply hψ_inj
  rw [map_mul, map_pow, hψg, hψr, hψc]
  exact hdvd_S

/-- **Round 23 R[1/r]-level section.** Standalone helper for
`descent_etale_section_after_localization`: builds an `R₀et`-algebra
homomorphism `S₀et →ₐ[R₀et] Localization.Away r` from the descent iso
`e : S ≃ₐ[R] R ⊗[R₀et] S₀et` together with `IsLocalization.Away r
(Localization.Away g)`.

This step is purely formal: it does NOT depend on the descent question
to `R₀`. The composition is

    S₀et --includeRight--> R ⊗[R₀et] S₀et --e.symm--> S
         --algebraMap--> Localization.Away g --algEquiv--> Localization.Away r.

The `R₀et`-algebra structures on `S` and `Localization.Away r` are
installed locally via the scalar tower `R₀et → R → ·`.

The arguments `n`, `cg`, `hcg` are not used in this construction; they
record the divisibility context that justifies the resulting section
mathematically. -/
private lemma _root_.Algebra.IsLocalIso.descent_section_at_R_inv_r
    {R : Type u} [CommRing R]
    {R₀et : Type u} [CommRing R₀et] [Algebra R₀et R]
    {S₀et : Type u} [CommRing S₀et] [Algebra R₀et S₀et]
    [Algebra.Etale R₀et S₀et]
    {S : Type u} [CommRing S] [Algebra R S] (e : S ≃ₐ[R] R ⊗[R₀et] S₀et)
    (g : S) (r : R)
    (hr : IsLocalization.Away r (Localization.Away g))
    (n : ℕ) (cg : S)
    (hcg : g ^ n = (algebraMap R S) r * cg) :
    Nonempty (S₀et →ₐ[R₀et] Localization.Away r) := by
  -- The hypotheses `n`, `cg`, `hcg` are not used in the construction; they
  -- record the divisibility context that justifies the resulting section.
  let _ : g ^ n = (algebraMap R S) r * cg := hcg
  -- `Algebra R₀et (Localization.Away r)` is automatic via
  -- `OreLocalization.instAlgebra` (from `[Algebra R₀et R]`). We only need to
  -- install `Algebra R₀et S` (locally) plus the corresponding scalar towers.
  letI algR₀etS : Algebra R₀et S :=
    ((algebraMap R S).comp (algebraMap R₀et R)).toAlgebra
  haveI : IsScalarTower R₀et R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R₀et R (Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Step (1): `R₀et`-algebra hom `S₀et → S` via `includeRight` and `e.symm`.
  let iotaR : R ⊗[R₀et] S₀et →ₐ[R₀et] S := e.symm.toAlgHom.restrictScalars R₀et
  let iota : S₀et →ₐ[R₀et] S :=
    iotaR.comp (Algebra.TensorProduct.includeRight (R := R₀et) (A := R) (B := S₀et))
  -- Step (2): `R`-algebra hom `S → Localization.Away g` (canonical).
  let toLocG : S →ₐ[R] Localization.Away g :=
    IsScalarTower.toAlgHom R S (Localization.Away g)
  -- Step (3): identify `Localization.Away g` with `Localization.Away r` as
  -- `R`-algebras using `IsLocalization`-uniqueness on `Submonoid.powers r`.
  let algEqGR : Localization.Away g ≃ₐ[R] Localization.Away r :=
    IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away g)
      (Localization.Away r)
  -- Step (4): compose to get the `R₀et`-algebra section.
  let toLocR : S →ₐ[R] Localization.Away r := algEqGR.toAlgHom.comp toLocG
  exact ⟨(toLocR.restrictScalars R₀et).comp iota⟩

/-- **Round 24 R₀-to-R bridge.** The canonical `R₀`-algebra map from the
localization of the subalgebra `R₀ ⊆ R` at the powers of `r₀` to the
localization of `R` at `r := algebraMap R₀ R r₀`.

This step is purely formal: by the universal property of localization
(`IsLocalization.liftAlgHom`), it suffices to verify that `r₀` becomes a unit
in `Localization.Away (algebraMap R₀ R r₀)`. This is automatic via the
scalar tower `R₀ → R → Loc.Away r`, since `algebraMap R₀ (Loc.Away r) r₀ =
algebraMap R (Loc.Away r) r` is a unit by `IsLocalization.Away.algebraMap_isUnit`.

Together with `descent_section_at_R_inv_r`, this assembles the
`R₀`-algebra hom `Loc.Away r₀ → Loc.Away r` whose pushout along
`R₀ → R₀ ⊗[R₀et] S₀et` lands in the étale-trivialisation target. -/
private noncomputable def _root_.Algebra.IsLocalIso.algebraMap_localization_R₀_to_R
    {R : Type u} [CommRing R] {R₀ : Subalgebra ℤ R} (r₀ : R₀) :
    Localization.Away r₀ →ₐ[R₀] Localization.Away (algebraMap R₀ R r₀) := by
  -- `Algebra R₀ (Localization.Away (algebraMap R₀ R r₀))` is automatic via
  -- `OreLocalization.instAlgebra` and the inclusion `R₀ → R`.
  refine IsLocalization.liftAlgHom (A := R₀) (R := R₀) (M := Submonoid.powers r₀)
    (S := Localization.Away r₀)
    (P := Localization.Away (algebraMap R₀ R r₀))
    (f := Algebra.ofId R₀ (Localization.Away (algebraMap R₀ R r₀))) ?_
  intro y
  obtain ⟨n, hn⟩ := y.2
  show IsUnit ((algebraMap R₀ (Localization.Away (algebraMap R₀ R r₀))) (y : R₀))
  rw [show (y : R₀) = r₀ ^ n from hn.symm, map_pow,
    IsScalarTower.algebraMap_apply R₀ R (Localization.Away (algebraMap R₀ R r₀))]
  exact (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (algebraMap R₀ R r₀)) (algebraMap R₀ R r₀)).pow n

/-- **Bridge injectivity (round 31, L1 step 1).** Under `Function.Injective
(algebraMap R₀ R)`, the canonical bridge
`algebraMap_localization_R₀_to_R r₀ : Loc.Away r₀ →ₐ[R₀] Loc.Away (algebraMap R₀ R r₀)`
is injective.

This is the building block for the Stacks 04D1 descent: it ensures that any
candidate descended section `sec₀ : S₀et →ₐ[R₀et] Loc.Away r₀` is uniquely
determined by its bridge image in `Loc.Away (algebraMap R₀ R r₀)`, and that
relations between descended generators may be verified after pushing forward
along the bridge. -/
private lemma _root_.Algebra.IsLocalIso.algebraMap_localization_R₀_to_R_injective
    {R : Type u} [CommRing R] {R₀ : Subalgebra ℤ R}
    (hval_inj : Function.Injective (algebraMap R₀ R)) (r₀ : R₀) :
    Function.Injective
      (Algebra.IsLocalIso.algebraMap_localization_R₀_to_R r₀) := by
  -- Reduce to injectivity at the RingHom level, then use
  -- `IsLocalization.injective_iff_map_algebraMap_eq` to descend to an `R₀`-level iff.
  suffices h : Function.Injective
      ((Algebra.IsLocalIso.algebraMap_localization_R₀_to_R r₀).toRingHom) from h
  rw [IsLocalization.injective_iff_map_algebraMap_eq (M := Submonoid.powers r₀)
    (S := Localization.Away r₀)]
  intro x y
  -- The bridge commutes with `algebraMap R₀ (·)` on both sides, so the inner
  -- iff is symmetric and reduces to `algebraMap_R x = algebraMap_R y in R₀ ↔ in R`.
  have h1 : ((Algebra.IsLocalIso.algebraMap_localization_R₀_to_R r₀).toRingHom)
      ((algebraMap R₀ (Localization.Away r₀)) x) =
      algebraMap R₀ (Localization.Away (algebraMap R₀ R r₀)) x :=
    (Algebra.IsLocalIso.algebraMap_localization_R₀_to_R r₀).commutes x
  have h2 : ((Algebra.IsLocalIso.algebraMap_localization_R₀_to_R r₀).toRingHom)
      ((algebraMap R₀ (Localization.Away r₀)) y) =
      algebraMap R₀ (Localization.Away (algebraMap R₀ R r₀)) y :=
    (Algebra.IsLocalIso.algebraMap_localization_R₀_to_R r₀).commutes y
  rw [h1, h2]
  constructor
  · -- Equality in `Loc.Away r₀` ⇒ equality in `Loc.Away (algMap r₀)`.
    -- Just apply the bridge ring hom to both sides.
    intro hxy
    have := congrArg
      ((Algebra.IsLocalIso.algebraMap_localization_R₀_to_R r₀).toRingHom) hxy
    rwa [h1, h2] at this
  · -- Equality in `Loc.Away (algMap r₀)` ⇒ equality in `Loc.Away r₀`.
    intro hxy
    rw [IsScalarTower.algebraMap_apply R₀ R (Localization.Away (algebraMap R₀ R r₀)),
      IsScalarTower.algebraMap_apply R₀ R (Localization.Away (algebraMap R₀ R r₀))] at hxy
    rw [IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R₀ R r₀))] at hxy
    obtain ⟨⟨c, k, hck⟩, hc⟩ := hxy
    -- Unfold the Subtype coercion: `(⟨c, _⟩ : Submonoid.powers _) = c` as elements of R.
    have hc' : (algebraMap R₀ R r₀) ^ k * (algebraMap R₀ R) x =
        (algebraMap R₀ R r₀) ^ k * (algebraMap R₀ R) y := by
      have : (((⟨c, k, hck⟩ : Submonoid.powers (algebraMap R₀ R r₀)) : R)) =
          (algebraMap R₀ R r₀) ^ k := hck.symm
      rw [this] at hc
      exact hc
    have hcR : (algebraMap R₀ R) (r₀ ^ k * x) = (algebraMap R₀ R) (r₀ ^ k * y) := by
      simpa [map_mul, map_pow] using hc'
    have heq₀ : r₀ ^ k * x = r₀ ^ k * y := hval_inj hcR
    rw [IsLocalization.eq_iff_exists (Submonoid.powers r₀)]
    exact ⟨⟨r₀ ^ k, k, rfl⟩, heq₀⟩

/-- **Per-generator decomposition (round 31, L1 step 3).** For any element
`s : S₀et` and any `R₀et`-algebra section
`secR : S₀et →ₐ[R₀et] Loc.Away ((algebraMap R₀ R) r₀)`,
`secR s` can be cleared of denominators with respect to the multiplicative subset
`Submonoid.powers ((algebraMap R₀ R) r₀)`. Concretely, there exists a numerator
`n : R` and an exponent `k : ℕ` such that

  `secR s * algebraMap R (Loc.Away (algMap r₀)) ((algMap r₀) ^ k) =
    algebraMap R (Loc.Away (algMap r₀)) n`.

This is the "clear denominator" form supplied directly by `IsLocalization.surj`
and is the foundation for descending each generator of `S₀et` from `R` back to
`R₀` (see step 4 of the round-31 L1 plan). -/
private lemma _root_.Algebra.IsLocalIso.section_descends_to_R0_per_gen_decomp
    {R : Type u} [CommRing R] {R₀ : Subalgebra ℤ R}
    {R₀et : Type u} [CommRing R₀et] [Algebra R₀et R]
    {S₀et : Type u} [CommRing S₀et] [Algebra R₀et S₀et]
    (r₀ : R₀)
    (secR : S₀et →ₐ[R₀et] Localization.Away ((algebraMap R₀ R) r₀))
    (s : S₀et) :
    ∃ (n : R) (k : ℕ),
      secR s *
          (algebraMap R (Localization.Away ((algebraMap R₀ R) r₀)))
            ((algebraMap R₀ R) r₀ ^ k) =
        (algebraMap R (Localization.Away ((algebraMap R₀ R) r₀))) n := by
  -- `IsLocalization.surj` on the powers of `algMap r₀` gives us a numerator
  -- and a denominator in `Submonoid.powers (algMap r₀)`. We unpack the
  -- denominator into an explicit exponent.
  obtain ⟨⟨x, ⟨c, hc⟩⟩, hxc⟩ :=
    IsLocalization.surj (M := Submonoid.powers ((algebraMap R₀ R) r₀))
      (S := Localization.Away ((algebraMap R₀ R) r₀)) (secR s)
  obtain ⟨k, hk⟩ := hc
  -- The Subtype coercion `(⟨c, _⟩ : Submonoid.powers _).val = c = (algMap r₀)^k`.
  have hval : ((⟨c, k, hk⟩ : Submonoid.powers ((algebraMap R₀ R) r₀)) : R) =
      (algebraMap R₀ R) r₀ ^ k := hk.symm
  refine ⟨x, k, ?_⟩
  rw [← hval]
  exact hxc

/-- **Section descent helper (round 26).** Given an étale `R₀et`-algebra section
`secR : S₀et →ₐ[R₀et] Loc.Away ((algebraMap R₀ R) r₀)` at the `R`-level
(produced by `descent_section_at_R_inv_r` from `e : S ≃ R ⊗[R₀et] S₀et`,
`g : S`, `r := algebraMap R₀ R r₀`, and `IsLocalization.Away r (Loc.Away g)`),
descend it to an `R₀et`-algebra section `sec₀ : S₀et →ₐ[R₀et] Loc.Away r₀`
at the `R₀`-level, compatible via the bridge
`algebraMap_localization_R₀_to_R r₀ : Loc.Away r₀ →ₐ[R₀] Loc.Away (algebraMap R₀ R r₀)`.

**Mathematical content** (Stacks 04D1 / 02JL "limit descent of étale algebras"):
`S₀et` is finitely presented over `R₀et` (étale ⇒ fp). Write
`S₀et = R₀et[x₁,…,xₙ]/(f₁,…,fₘ)`. The section `secR` sends each `xᵢ` to some
`aᵢ ∈ Loc.Away ((algebraMap R₀ R) r₀)`. Via base-change-of-localization,
`Loc.Away ((algebraMap R₀ R) r₀) = R ⊗_{R₀} Loc.Away r₀` (as `R`-algebras).
Each `aᵢ` decomposes as `∑ⱼ ρᵢⱼ ⊗ ξᵢⱼ` with `ρᵢⱼ ∈ R, ξᵢⱼ ∈ Loc.Away r₀`.
The defining equations `f_j(secR(x₁),…,secR(xₙ)) = 0` have coefficients in
`R₀et ⊆ R₀`, so by injectivity of `R₀ → R` (`hval_inj`) and faithful-flatness
of `R` as a (specifically constructed) module over the relevant subalgebra,
the equations descend to `Loc.Away r₀`. This gives `sec₀`.

**Currently unformalized** — this is the genuine mathematical content of
the round-26 OBJ A. The helper exposes the descent as a standalone lemma so
the surrounding assembly (`descent_etale_section_after_localization`) can be
written modulo this step. Estimated 80–150 LOC when expanded; requires
the `Algebra.FinitePresentation`/`Algebra.Presentation.exists_lift` API and
careful manipulation of `IsLocalization.mk'_eq_iff_eq`. -/
private lemma _root_.Algebra.IsLocalIso.section_descends_to_R0
    {R : Type u} [CommRing R] {R₀ : Subalgebra ℤ R}
    {R₀et : Type u} [CommRing R₀et] [Algebra R₀et R₀] [Algebra R₀et R]
    [IsScalarTower R₀et R₀ R]
    (hval_inj : Function.Injective (algebraMap R₀ R))
    {S₀et : Type u} [CommRing S₀et] [Algebra R₀et S₀et] [Algebra.Etale R₀et S₀et]
    {S : Type u} [CommRing S] [Algebra R S] (e : S ≃ₐ[R] R ⊗[R₀et] S₀et)
    (g : S) (r₀ : R₀)
    (hr : IsLocalization.Away ((algebraMap R₀ R) r₀) (Localization.Away g))
    (n : ℕ) (cg : S)
    (hcg : g ^ n = (algebraMap R S) ((algebraMap R₀ R) r₀) * cg)
    (g₀ c₀ : R₀ ⊗[R₀et] S₀et)
    (hbridge_g : e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
      ((1 : R) ⊗ₜ[R₀] g₀)) = g)
    (hbridge_c : e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
      ((1 : R) ⊗ₜ[R₀] c₀)) = cg)
    (hunit_pow : ∀ y : Submonoid.powers r₀,
      IsUnit ((algebraMap R₀ (Localization.Away g₀)) y))
    (secR : S₀et →ₐ[R₀et] Localization.Away ((algebraMap R₀ R) r₀)) :
    letI : IsScalarTower R₀et R₀ (Localization.Away r₀) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    ∃ sec₀ : S₀et →ₐ[R₀et] Localization.Away r₀,
      (∀ s : S₀et,
        (Algebra.IsLocalIso.algebraMap_localization_R₀_to_R r₀) (sec₀ s) = secR s) ∧
      IsUnit
        ((Algebra.TensorProduct.lift (Algebra.ofId R₀ (Localization.Away r₀)) sec₀
          (fun _ _ => Commute.all _ _) :
            R₀ ⊗[R₀et] S₀et →ₐ[R₀] Localization.Away r₀) g₀) ∧
      (∀ s : S₀et,
        (IsLocalization.liftAlgHom (A := R₀) (R := R₀) (M := Submonoid.powers r₀)
          (S := Localization.Away r₀) (P := Localization.Away g₀)
          (f := Algebra.ofId R₀ (Localization.Away g₀)) hunit_pow) (sec₀ s) =
        algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) ((1 : R₀) ⊗ₜ[R₀et] s)) := by
  letI : IsScalarTower R₀et R₀ (Localization.Away r₀) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Pin down all the data so it survives elaboration into the (currently unfilled) descent.
  let _h1 := hval_inj
  let _h2 := e
  let _h3 := g
  let _h4 := hr
  let _h5 := n
  let _h6 := cg
  let _h7 := hcg
  let _h8 := g₀
  let _h9 := c₀
  let _h10 := hbridge_g
  let _h11 := hbridge_c
  let _h12 := hunit_pow
  let _h13 := secR
  haveI : Algebra.FinitePresentation R₀et S₀et := inferInstance
  -- **Round 31 progress**: the bridge injectivity helper
  -- `algebraMap_localization_R₀_to_R_injective` has been extracted as a standalone
  -- lemma (proved above). This closes step (1) of L1; the remaining L1 content
  -- (constructing `sec₀` on generators + verifying relations) is Stacks 04D1 / 02JL.
  --
  -- The bridge `Loc.Away r₀ → Loc.Away (algMap r₀)` is INJECTIVE under `hval_inj`.
  -- This is recorded as `hbridge_inj` below and is the key tool for both:
  -- (a) uniqueness of the descended section, and
  -- (b) verifying that relations evaluate to zero in `Loc.Away r₀` (after pushing to R).
  have hbridge_inj : Function.Injective
      (Algebra.IsLocalIso.algebraMap_localization_R₀_to_R r₀) :=
    Algebra.IsLocalIso.algebraMap_localization_R₀_to_R_injective hval_inj r₀
  -- Pin the bridge injectivity into the closure for downstream consumption.
  let _hbridge := hbridge_inj
  --
  -- **Descent strategy** (Stacks 04D1 / 02JL):
  --
  -- (L1) Construct `sec₀ : S₀et →ₐ[R₀et] Loc.Away r₀` such that
  --      `bridge(sec₀ s) = secR s` in `Loc.Away (algMap r₀)`, where
  --      `bridge := algebraMap_localization_R₀_to_R r₀`.
  --
  --    KEY OBSERVATION: With `hval_inj`, the bridge `Loc.Away r₀ → Loc.Away (algMap r₀)`
  --    is INJECTIVE (proved as `algebraMap_localization_R₀_to_R_injective` above).
  --    So if `sec₀` exists, it is uniquely determined.
  --
  --    EXISTENCE: pick a presentation `pres : Algebra.Presentation R₀et S₀et`.
  --    For each generator `xᵢ`, write `secR(xᵢ) = IsLocalization.mk' nᵢ (algMap r₀)^kᵢ`
  --    via `IsLocalization.surj`. To descend, we must find `mᵢ ∈ R₀` with `algMap mᵢ = nᵢ`
  --    (modulo `(algMap r₀)^Nᵢ`). The base-change `Loc.Away r₀ ⊗[R₀] R ≃ Loc.Away (algMap r₀)`
  --    (standard) lets us identify `nᵢ ∈ R` with an element of `R₀ ⊗[R₀] R`-image; the
  --    extra structure (`e`, `g`, `hbridge_g`) factors the relevant elements through
  --    `R₀ ⊗[R₀et] S₀et[1/g₀]`, where the numerator IS in `R₀ ⊗ S₀et` by hbridge.
  --
  -- (L2) Unit witness: given `sec₀` from L1, `φ(g₀)` is a unit in `Loc.Away r₀` where
  --      `φ := Algebra.TensorProduct.lift _ sec₀ _`.
  --
  --    Note: this is NOT mechanical from `g₀^n = algMap r₀ * c₀` alone (the spec's
  --    suggested argument doesn't close: `(unit)·x = unit` requires `x` to be a unit).
  --    The correct argument: `bridge ∘ φ = ψ` where `ψ : R₀ ⊗ S₀et → Loc.Away (algMap r₀)`
  --    is the natural map factoring through `S → Loc.Away g → Loc.Away (algMap r₀)`.
  --    `ψ(g₀) = (algEquiv: Loc.Away g ≃ Loc.Away (algMap r₀))(g/1)` is a unit (since `g`
  --    is a unit in `Loc.Away g`). So `bridge(φ(g₀))` is a unit. Since `bridge` is a
  --    LOCALIZATION map (Loc.Away r₀ → Loc.Away (algMap r₀)), a unit in the codomain
  --    has the form `bridge(y)·u` for some `y` and unit `u`; combined with injectivity
  --    (now available as `hbridge_inj`), `φ(g₀)` is itself a unit.
  --
  -- (L3) Consistency: `fwdAH(sec₀ s) = algMap (1 ⊗ s)` in `Loc.Away g₀`.
  --
  --    By the construction of `sec₀` in L1, both sides agree after applying any map
  --    `Loc.Away g₀ → Loc.Away g` (when one exists, e.g., via the canonical extension).
  --    Injectivity of this auxiliary map (under the bridge data) yields equality.
  --
  -- **Round 31 status**: L1 step 1 (bridge injectivity) is now CLOSED. L1 steps 2-7
  -- (presentation, numerator descent, relation descent, sec₀ construction), L2
  -- (unit witness), and L3 (consistency) remain. See
  -- `task_results/Mathlib_Algebra_LocalIso_Spreads.lean.md` for the round-31 analysis.
  sorry

/-- Per-tensor identity for the forward lift composed with the tensor lift.
Given the consistency `fwdAH (sec₀ s) = algMap (1 ⊗ s)` and the description
of `φ` on simple tensors, this proves the analogous equation on any `r ⊗ s`. -/
private lemma _root_.Algebra.IsLocalIso.fwdAH_phi_tmul_eq_algebraMap
    {R₀et : Type u} [CommRing R₀et]
    {R₀ : Type u} [CommRing R₀] [Algebra R₀et R₀]
    {S₀et : Type u} [CommRing S₀et] [Algebra R₀et S₀et]
    (r₀ : R₀) (g₀ : R₀ ⊗[R₀et] S₀et)
    (sec₀ : S₀et →ₐ[R₀et] Localization.Away r₀)
    (fwdAH : Localization.Away r₀ →ₐ[R₀] Localization.Away g₀)
    (hcanon : ∀ s : S₀et,
      fwdAH (sec₀ s) =
      algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) ((1 : R₀) ⊗ₜ[R₀et] s))
    (r : R₀) (s : S₀et) :
    fwdAH ((algebraMap R₀ (Localization.Away r₀)) r * sec₀ s) =
    algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) (r ⊗ₜ[R₀et] s) := by
  rw [map_mul, fwdAH.commutes, hcanon s]
  rw [show (r ⊗ₜ[R₀et] s : R₀ ⊗[R₀et] S₀et) =
    (r ⊗ₜ[R₀et] (1 : S₀et)) * ((1 : R₀) ⊗ₜ[R₀et] s) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
  rw [map_mul]
  rw [show (r ⊗ₜ[R₀et] (1 : S₀et) : R₀ ⊗[R₀et] S₀et) =
    algebraMap R₀ (R₀ ⊗[R₀et] S₀et) r from rfl]
  rw [← IsScalarTower.algebraMap_apply R₀ (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀)]

/-- Helper for `descent_etale_section_after_localization`: the forward lift
`fwdAH` precomposed with the tensor lift `φ` (which extends `sec₀` to all of
`R₀ ⊗[R₀et] S₀et`) equals the canonical algebra map. This is the key consistency
identity used to show that `fwdAH ∘ bwdAH = id` on `Loc.Away g₀`.

Extracted into its own lemma so that the heavy typeclass / `whnf` work done by
`Algebra.TensorProduct.lift_tmul` and `tmul_mul_tmul` rewrites does not exhaust
the heartbeat budget of the surrounding (already long) assembly. The signature
takes `fwdAH` and `φ` as explicit parameters with their key properties as
hypotheses, avoiding the need to unfold their definitions inside the proof. -/
private lemma _root_.Algebra.IsLocalIso.fwdAH_phi_eq_algebraMap
    {R₀et : Type u} [CommRing R₀et]
    {R₀ : Type u} [CommRing R₀] [Algebra R₀et R₀]
    {S₀et : Type u} [CommRing S₀et] [Algebra R₀et S₀et]
    (r₀ : R₀) (g₀ : R₀ ⊗[R₀et] S₀et)
    (sec₀ : S₀et →ₐ[R₀et] Localization.Away r₀)
    (fwdAH : Localization.Away r₀ →ₐ[R₀] Localization.Away g₀)
    (φ : R₀ ⊗[R₀et] S₀et →ₐ[R₀] Localization.Away r₀)
    (hφ_tmul : ∀ r : R₀, ∀ s : S₀et,
      φ (r ⊗ₜ[R₀et] s) = (algebraMap R₀ (Localization.Away r₀)) r * sec₀ s)
    (hcanon : ∀ s : S₀et,
      fwdAH (sec₀ s) =
      algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) ((1 : R₀) ⊗ₜ[R₀et] s)) :
    ∀ x : R₀ ⊗[R₀et] S₀et,
      fwdAH (φ x) =
      algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) x := fun x => by
  induction x with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, ← map_add]
  | tmul r s =>
    rw [hφ_tmul]
    exact Algebra.IsLocalIso.fwdAH_phi_tmul_eq_algebraMap r₀ g₀ sec₀ fwdAH hcanon r s

/-- Assembly helper: given the descended section `sec₀`, the unit witness
`hφg₀_unit`, and the consistency `hcanon`, build the `R₀`-algebra equivalence
`Loc.Away r₀ ≃ₐ[R₀] Loc.Away g₀`.

Extracted from `descent_etale_section_after_localization` to keep heartbeat
budgets manageable. -/
private lemma _root_.Algebra.IsLocalIso.alg_equiv_from_section_descent
    {R₀et : Type u} [CommRing R₀et]
    {R₀ : Type u} [CommRing R₀] [Algebra R₀et R₀]
    {S₀et : Type u} [CommRing S₀et] [Algebra R₀et S₀et]
    (r₀ : R₀) (g₀ : R₀ ⊗[R₀et] S₀et)
    (hunit_pow : ∀ y : Submonoid.powers r₀,
      IsUnit ((algebraMap R₀ (Localization.Away g₀)) y))
    (sec₀ : S₀et →ₐ[R₀et] Localization.Away r₀)
    (hφg₀_unit : IsUnit
      ((Algebra.TensorProduct.lift (Algebra.ofId R₀ (Localization.Away r₀)) sec₀
        (fun _ _ => Commute.all _ _) :
          R₀ ⊗[R₀et] S₀et →ₐ[R₀] Localization.Away r₀) g₀))
    (hcanon : ∀ s : S₀et,
      (IsLocalization.liftAlgHom (A := R₀) (R := R₀) (M := Submonoid.powers r₀)
        (S := Localization.Away r₀) (P := Localization.Away g₀)
        (f := Algebra.ofId R₀ (Localization.Away g₀)) hunit_pow) (sec₀ s) =
      algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) ((1 : R₀) ⊗ₜ[R₀et] s)) :
    Nonempty (Localization.Away r₀ ≃ₐ[R₀] Localization.Away g₀) := by
  -- Forward map.
  let fwdAH : Localization.Away r₀ →ₐ[R₀] Localization.Away g₀ :=
    IsLocalization.liftAlgHom (A := R₀) (R := R₀) (M := Submonoid.powers r₀)
      (S := Localization.Away r₀) (P := Localization.Away g₀)
      (f := Algebra.ofId R₀ (Localization.Away g₀)) hunit_pow
  let φ : R₀ ⊗[R₀et] S₀et →ₐ[R₀] Localization.Away r₀ :=
    Algebra.TensorProduct.lift
      (Algebra.ofId R₀ (Localization.Away r₀)) sec₀
      (fun _ _ => Commute.all _ _)
  -- Powers of `g₀` are units under `φ`.
  have hφ_pow_unit : ∀ y : Submonoid.powers g₀, IsUnit (φ y) := fun y => by
    obtain ⟨k, hk⟩ := y.2
    rw [show (y : R₀ ⊗[R₀et] S₀et) = g₀ ^ k from hk.symm, map_pow]
    exact hφg₀_unit.pow k
  -- Backward map.
  let bwdAH : Localization.Away g₀ →ₐ[R₀] Localization.Away r₀ :=
    IsLocalization.liftAlgHom (A := R₀) (M := Submonoid.powers g₀)
      (S := Localization.Away g₀) (P := Localization.Away r₀)
      (f := φ) hφ_pow_unit
  -- (f.1) `bwdAH ∘ fwdAH = id` on `Loc.Away r₀`.
  have h_bwd_comp_fwd : bwdAH.comp fwdAH = AlgHom.id R₀ (Localization.Away r₀) := by
    apply AlgHom.coe_ringHom_injective
    refine IsLocalization.ringHom_ext (M := Submonoid.powers r₀)
      (S := Localization.Away r₀) (RingHom.ext fun r => ?_)
    show bwdAH (fwdAH (algebraMap R₀ (Localization.Away r₀) r)) =
      (RingHom.id _) (algebraMap R₀ (Localization.Away r₀) r)
    rw [AlgHom.commutes, AlgHom.commutes, RingHom.id_apply]
  -- (f.2) `fwdAH ∘ bwdAH = id` on `Loc.Away g₀`. Uses the extracted helper.
  have hφ_tmul : ∀ r : R₀, ∀ s : S₀et,
      φ (r ⊗ₜ[R₀et] s) = (algebraMap R₀ (Localization.Away r₀)) r * sec₀ s := fun r s =>
    Algebra.TensorProduct.lift_tmul _ _ _ _ _
  have hkey_all : ∀ x : R₀ ⊗[R₀et] S₀et,
      fwdAH (φ x) =
      algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) x :=
    Algebra.IsLocalIso.fwdAH_phi_eq_algebraMap r₀ g₀ sec₀ fwdAH φ hφ_tmul hcanon
  have h_fwd_comp_bwd : fwdAH.comp bwdAH = AlgHom.id R₀ (Localization.Away g₀) := by
    apply AlgHom.coe_ringHom_injective
    refine IsLocalization.ringHom_ext (M := Submonoid.powers g₀)
      (S := Localization.Away g₀) (RingHom.ext fun x => ?_)
    show fwdAH (bwdAH (algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) x)) =
      (RingHom.id _) (algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) x)
    rw [RingHom.id_apply,
      show bwdAH (algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) x) = φ x by
        show IsLocalization.lift (M := Submonoid.powers g₀)
          (S := Localization.Away g₀) (g := φ.toRingHom) _
          (algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀) x) = _
        rw [IsLocalization.lift_eq]
        rfl]
    exact hkey_all x
  exact ⟨AlgEquiv.ofAlgHom fwdAH bwdAH h_fwd_comp_bwd h_bwd_comp_fwd⟩

/-- **Step (4) of `descent_one_isLocalIso_template`.** Packages the deep
"étale trivialises after inverting `r₀`" content into the existence of an
`R₀`-algebra equivalence `Loc.Away r₀ ≃ₐ[R₀] Loc.Away g₀`.

Mathematical content (currently left as a scoped `sorry`):
- After base-change to `R[1/r]`, the étale algebra `S₀et / R₀et` admits a canonical
  section because `R[1/r] ⊗_R S = S[1/r]` (via `e : S ≃ R ⊗[R₀et] S₀et`, this equals
  `R[1/r] ⊗[R₀et] S₀et`) and `S[1/r] = Loc.Away g` as `R[1/r]`-algebra
  (since `IsLocalization.Away r (Loc.Away g)` makes `S → S[1/r]` factor through
  `Loc.Away g`, AND `g^n = r·cg` gives the converse).
- Thus `R[1/r] ⊗[R₀et] S₀et ≃ R[1/r]` as `R[1/r]`-algebras, yielding a section
  `sec : S₀et →ₐ[R₀et] R[1/r]`.
- Descending via `Algebra.TensorProduct.cancelBaseChange` gives
  `Loc.Away r₀ ⊗[R₀et] S₀et ≃ Loc.Away r₀`, i.e.
  `Loc.Away r₀ ≃ₐ[R₀] Loc.Away g₀`. -/
private lemma _root_.Algebra.IsLocalIso.descent_etale_section_after_localization
    {R : Type u} [CommRing R] {R₀ : Subalgebra ℤ R}
    {R₀et : Type u} [CommRing R₀et] [Algebra R₀et R] [Algebra R₀et R₀]
    [IsScalarTower R₀et R₀ R]
    (hval_inj : Function.Injective (algebraMap R₀ R))
    {S₀et : Type u} [CommRing S₀et] [Algebra R₀et S₀et] [Algebra.Etale R₀et S₀et]
    {S : Type u} [CommRing S] [Algebra R S] (e : S ≃ₐ[R] R ⊗[R₀et] S₀et)
    (g : S) (r : R) (r_mem : r ∈ R₀)
    (hr : IsLocalization.Away r (Localization.Away g))
    (n : ℕ) (cg : S)
    (hcg : g ^ n = (algebraMap R S) r * cg)
    (g₀ c₀ : R₀ ⊗[R₀et] S₀et)
    (hbridge_g : e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
      ((1 : R) ⊗ₜ[R₀] g₀)) = g)
    (hbridge_c : e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
      ((1 : R) ⊗ₜ[R₀] c₀)) = cg) :
    letI : Algebra R₀ (R₀ ⊗[R₀et] S₀et) := Algebra.TensorProduct.leftAlgebra
    Nonempty (Localization.Away (⟨r, r_mem⟩ : R₀) ≃ₐ[R₀] Localization.Away g₀) := by
  letI : Algebra R₀ (R₀ ⊗[R₀et] S₀et) := Algebra.TensorProduct.leftAlgebra
  -- Setup: name `r₀ : R₀` and the underlying `r` agreement.
  set r₀ : R₀ := ⟨r, r_mem⟩ with hr₀_def
  have hr₀ : (algebraMap R₀ R) r₀ = r := rfl
  haveI : IsLocalization.Away ((algebraMap R₀ R) r₀) (Localization.Away g) := hr₀ ▸ hr
  haveI : Module.Flat R₀et S₀et := inferInstance
  -- (1) Lifted divisibility in `S₀ = R₀ ⊗[R₀et] S₀et`: `g₀^n = r₀ * c₀`.
  -- This follows from `hcg` via `descent_lifted_divisibility`.
  have hcg' : g ^ n = (algebraMap R S) ((algebraMap R₀ R) r₀) * cg := hr₀ ▸ hcg
  have hdvd₀ : g₀ ^ n = (algebraMap R₀ (R₀ ⊗[R₀et] S₀et)) r₀ * c₀ :=
    Algebra.IsLocalIso.descent_lifted_divisibility hval_inj e g r₀ cg n hcg' g₀ c₀
      hbridge_g hbridge_c
  -- (2) `r₀` becomes a unit in `Loc.Away g₀`: from `g₀^n = r₀ * c₀` and
  -- `IsLocalization.Away.algebraMap_isUnit_iff`.
  have hunit_r₀' : IsUnit ((algebraMap R₀ (Localization.Away g₀)) r₀) := by
    rw [IsScalarTower.algebraMap_apply R₀ (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀)]
    exact (IsLocalization.Away.algebraMap_isUnit_iff (S := Localization.Away g₀) g₀).mpr
      ⟨n, c₀, hdvd₀⟩
  have hunit_pow : ∀ y : Submonoid.powers r₀,
      IsUnit ((algebraMap R₀ (Localization.Away g₀)) y) := fun y => by
    obtain ⟨k, hk⟩ := y.2
    rw [show (y : R₀) = r₀ ^ k from hk.symm, map_pow]
    exact hunit_r₀'.pow k
  -- (3) Forward map: `Loc.Away r₀ →ₐ[R₀] Loc.Away g₀` via
  -- `IsLocalization.liftAlgHom` of `Algebra.ofId R₀ (Loc.Away g₀)`.
  let fwdAH : Localization.Away r₀ →ₐ[R₀] Localization.Away g₀ :=
    IsLocalization.liftAlgHom (A := R₀) (R := R₀) (M := Submonoid.powers r₀)
      (S := Localization.Away r₀) (P := Localization.Away g₀)
      (f := Algebra.ofId R₀ (Localization.Away g₀)) hunit_pow
  -- (4) Backward map (assembled via the `section_descends_to_R0` helper).
  --
  -- Pipeline:
  -- (a) `descent_section_at_R_inv_r hr n cg hcg` yields
  --     `secR : S₀et →ₐ[R₀et] Loc.Away r` (existing helper, fully proved).
  -- (b) `section_descends_to_R0 hval_inj r₀ secR'` descends `secR` to
  --     `sec₀ : S₀et →ₐ[R₀et] Loc.Away r₀` (NEW round-26 helper carrying the
  --     genuine `Stacks 04D1 / 02JL` content as a scoped `sorry`).
  -- (c) `Algebra.TensorProduct.lift` extends `(algebraMap R₀ (Loc.Away r₀),
  --     sec₀)` to `φ : R₀ ⊗[R₀et] S₀et →ₐ[R₀] Loc.Away r₀`.
  -- (d) `φ g₀` is a unit. Argument: `bridge ∘ φ` (i.e. composing with
  --     `algebraMap_localization_R₀_to_R r₀ : Loc.Away r₀ →ₐ[R₀] Loc.Away r`)
  --     equals the analogous extension built over Loc.Away r (using `secR`),
  --     which sends `g₀` to the image of `g` in `Loc.Away r`, a unit
  --     (since `IsLocalization.Away r (Loc.Away g)` makes `g` a unit in
  --     `Loc.Away g ≅ Loc.Away r`). Lift unit-ness back along the bridge.
  -- (e) `IsLocalization.liftAlgHom` of `φ` at `Submonoid.powers g₀` gives
  --     `bwdAH : Loc.Away g₀ →ₐ[R₀] Loc.Away r₀`.
  -- (f) Mutual inverses via `IsLocalization.ringHom_ext`.
  -- Obtain the R-level section.
  obtain ⟨secR⟩ : Nonempty (S₀et →ₐ[R₀et] Localization.Away r) :=
    Algebra.IsLocalIso.descent_section_at_R_inv_r e g r hr n cg hcg
  -- Reindex `secR` to `Loc.Away ((algebraMap R₀ R) r₀)` using `hr₀ : algebraMap R₀ R r₀ = r`.
  let secR' : S₀et →ₐ[R₀et] Localization.Away ((algebraMap R₀ R) r₀) := hr₀.symm ▸ secR
  -- Set up `IsScalarTower R₀et R₀ (Loc.Away r₀)`, required by the lift below.
  haveI hSTr₀ : IsScalarTower R₀et R₀ (Localization.Away r₀) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Descend the section using the enriched round-28 helper. The helper outputs
  -- `(sec₀, hcompat, hφg₀_unit, hcanon)` where `hφg₀_unit` is the unit witness
  -- for the lift applied to `g₀` and `hcanon` is the consistency
  -- `fwdAH (sec₀ s) = algMap (1 ⊗ s)` in `Loc.Away g₀`.
  -- Round 30: enriched signature; thread through the caller's structural data.
  have hr' : IsLocalization.Away ((algebraMap R₀ R) r₀) (Localization.Away g) := hr₀ ▸ hr
  have hcg' : g ^ n = (algebraMap R S) ((algebraMap R₀ R) r₀) * cg := hr₀ ▸ hcg
  obtain ⟨sec₀, _hcompat, hφg₀_unit, hcanon⟩ :=
    Algebra.IsLocalIso.section_descends_to_R0 (R₀ := R₀) hval_inj e g r₀ hr' n cg hcg'
      g₀ c₀ hbridge_g hbridge_c hunit_pow secR'
  -- (c)–(f) Assemble the AlgEquiv via the extracted helper. The helper performs:
  -- (c) build `φ` via `Algebra.TensorProduct.lift`,
  -- (d) extract unit witness for powers of `g₀`,
  -- (e) build `bwdAH` via `IsLocalization.liftAlgHom`,
  -- (f) prove mutual inverses (using the consistency `hcanon` and
  --     `fwdAH_phi_eq_algebraMap` for the harder direction).
  -- The `fwdAH` referenced by the helper is the SAME `IsLocalization.liftAlgHom`
  -- term used in our `let`-binding above (definitionally equal).
  exact Algebra.IsLocalIso.alg_equiv_from_section_descent
    r₀ g₀ hunit_pow sec₀ hφg₀_unit hcanon

/-- Helper for `exists_subalgebra_fg_descent`, sub-lemma (D): per-witness IsLocalIso
descent. Given the framework + one specific witness `(g, r₀, g₀)` with the bridge,
divisibility, and étaleness data, conclude `Algebra.IsLocalIso R₀ (Localization.Away g₀)`.

Extracting this from the main lemma frees heartbeat budget for the
`descent_lifted_divisibility` call and the AlgEquiv construction.

Proof skeleton:
1. Use `descent_lifted_divisibility` (with `hbridge_g`, `hbridge_c`, `hcg`) to obtain
   `g₀ ^ n = (algebraMap R₀ S₀) r₀ * c₀` in `S₀ := R₀ ⊗[R₀et] S₀et`.
2. Conclude `IsUnit ((algebraMap R₀ (Loc.Away g₀)) r₀)` via
   `IsLocalization.Away.algebraMap_isUnit_iff`.
3. Build forward `Loc.Away r₀ →ₐ[R₀] Loc.Away g₀` via `IsLocalization.Away.lift`.
4. **Deep step.** Obtain the AlgEquiv `Loc.Away r₀ ≃ₐ[R₀] Loc.Away g₀` via
   `descent_etale_section_after_localization` (this is the étale-trivialises step).
5. Transport `IsStandardOpenImmersion R₀ (Loc.Away r₀) ⇒
   IsStandardOpenImmersion R₀ (Loc.Away g₀)` via `IsStandardOpenImmersion.of_algEquiv`.
6. Conclude via the priority-100 instance `Algebra.IsLocalIso.instIsLocalIso`. -/
private lemma _root_.Algebra.IsLocalIso.descent_one_isLocalIso_template
    {R : Type u} [CommRing R] {R₀ : Subalgebra ℤ R}
    {R₀et : Type u} [CommRing R₀et] [Algebra R₀et R] [Algebra R₀et R₀]
    [IsScalarTower R₀et R₀ R]
    (hval_inj : Function.Injective (algebraMap R₀ R))
    {S₀et : Type u} [CommRing S₀et] [Algebra R₀et S₀et] [Algebra.Etale R₀et S₀et]
    {S : Type u} [CommRing S] [Algebra R S] (e : S ≃ₐ[R] R ⊗[R₀et] S₀et)
    (g : S) (r : R) (r_mem : r ∈ R₀)
    (hr : IsLocalization.Away r (Localization.Away g))
    (n : ℕ) (cg : S)
    (hcg : g ^ n = (algebraMap R S) r * cg)
    (g₀ c₀ : R₀ ⊗[R₀et] S₀et)
    (hbridge_g : e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
      ((1 : R) ⊗ₜ[R₀] g₀)) = g)
    (hbridge_c : e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
      ((1 : R) ⊗ₜ[R₀] c₀)) = cg) :
    letI : Algebra R₀ (R₀ ⊗[R₀et] S₀et) := Algebra.TensorProduct.leftAlgebra
    Algebra.IsLocalIso R₀ (Localization.Away g₀) := by
  letI : Algebra R₀ (R₀ ⊗[R₀et] S₀et) := Algebra.TensorProduct.leftAlgebra
  -- Witness `r₀ : R₀` from the membership.
  let r₀ : R₀ := ⟨r, r_mem⟩
  have hr₀ : (algebraMap R₀ R) r₀ = r := rfl
  haveI : IsLocalization.Away ((algebraMap R₀ R) r₀) (Localization.Away g) := hr₀ ▸ hr
  haveI : Module.Flat R₀et S₀et := inferInstance
  -- Step (1): lifted divisibility in S₀.
  have hcg' : g ^ n = (algebraMap R S) ((algebraMap R₀ R) r₀) * cg := hr₀ ▸ hcg
  have hdvd₀ : g₀ ^ n = (algebraMap R₀ (R₀ ⊗[R₀et] S₀et)) r₀ * c₀ :=
    Algebra.IsLocalIso.descent_lifted_divisibility hval_inj e g r₀ cg n hcg' g₀ c₀
      hbridge_g hbridge_c
  -- Step (2): the image of `r₀` in `Loc.Away g₀` (via `R₀ → R₀ ⊗ S₀et → Loc.Away g₀`)
  -- is a unit. We track the composite RingHom directly rather than registering a new
  -- `Algebra R₀ (Loc.Away g₀)` instance (which would clash with universe/structure
  -- inference).
  let φ : R₀ →+* Localization.Away g₀ :=
    (algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀)).comp
      (algebraMap R₀ (R₀ ⊗[R₀et] S₀et))
  have hunit_r₀ : IsUnit (φ r₀) := by
    show IsUnit ((algebraMap (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀))
        ((algebraMap R₀ (R₀ ⊗[R₀et] S₀et)) r₀))
    refine (IsLocalization.Away.algebraMap_isUnit_iff (S := Localization.Away g₀)
      g₀).mpr ⟨n, c₀, ?_⟩
    exact hdvd₀
  -- Step (2'): same unit property phrased via the inferred `algebraMap R₀ (Loc.Away g₀)`
  -- (which factors through `S₀ = R₀ ⊗[R₀et] S₀et` via the inferred `IsScalarTower`).
  have hunit_r₀' : IsUnit ((algebraMap R₀ (Localization.Away g₀)) r₀) := by
    rw [IsScalarTower.algebraMap_apply R₀ (R₀ ⊗[R₀et] S₀et) (Localization.Away g₀)]
    exact (IsLocalization.Away.algebraMap_isUnit_iff (S := Localization.Away g₀) g₀).mpr
      ⟨n, c₀, hdvd₀⟩
  -- Power of `r₀` is also a unit (used in Step (3)).
  have hunit_pow : ∀ y : Submonoid.powers r₀, IsUnit ((algebraMap R₀ (Localization.Away g₀)) y) :=
    fun y => by
      obtain ⟨k, hk⟩ := y.2
      rw [show (y : R₀) = r₀ ^ k from hk.symm, map_pow]
      exact hunit_r₀'.pow k
  -- Step (3): forward `R₀`-algebra hom `Loc.Away r₀ →ₐ[R₀] Loc.Away g₀`.
  -- Built via `IsLocalization.liftAlgHom` applied to `Algebra.ofId R₀ (Loc.Away g₀)`.
  let fwdAH : Localization.Away r₀ →ₐ[R₀] Localization.Away g₀ :=
    IsLocalization.liftAlgHom (A := R₀) (R := R₀) (M := Submonoid.powers r₀)
      (S := Localization.Away r₀) (P := Localization.Away g₀)
      (f := Algebra.ofId R₀ (Localization.Away g₀)) hunit_pow
  -- Step (4): the deep "étale trivialises after inverting `r`" content. Delegated to
  -- `descent_etale_section_after_localization`, which currently carries the only
  -- remaining scoped `sorry` in this file. `fwdAH` (built in step (3)) is preserved
  -- for context but is not used in the assembly below — the helper provides the full
  -- AlgEquiv directly.
  let _fwdAH_unused := fwdAH
  obtain ⟨algEquiv⟩ : Nonempty (Localization.Away r₀ ≃ₐ[R₀] Localization.Away g₀) :=
    Algebra.IsLocalIso.descent_etale_section_after_localization
      hval_inj e g r r_mem hr n cg hcg g₀ c₀ hbridge_g hbridge_c
  -- Step (5)/(6): use the AlgEquiv from the helper.
  -- Transport `IsStandardOpenImmersion R₀ (Loc.Away r₀)` (automatic from `IsLocalization.Away
  -- r₀ (Loc.Away r₀)`) along the `R₀`-algebra equivalence to `Loc.Away g₀`.
  haveI : Algebra.IsStandardOpenImmersion R₀ (Localization.Away r₀) := inferInstance
  haveI : Algebra.IsStandardOpenImmersion R₀ (Localization.Away g₀) :=
    Algebra.IsStandardOpenImmersion.of_algEquiv R₀ _ _ algEquiv
  -- Conclude via the priority-100 instance `Algebra.IsLocalIso.instIsLocalIso`.
  infer_instance

/-- A local isomorphism of commutative rings is étale. (Helper, repeated here from
`Proetale.Algebra.IndEtale` to avoid an import cycle.) -/
private lemma _root_.Algebra.IsLocalIso.etale_of {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsLocalIso R S] : Algebra.Etale R S := by
  rw [← RingHom.etale_algebraMap]
  let s : Set S := {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
  have hs : Ideal.span s = ⊤ := Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top R S
  refine RingHom.Etale.ofLocalizationSpanTarget (algebraMap R S) s hs fun ⟨g, hg⟩ => ?_
  obtain ⟨r, hr⟩ := hg.exists_away
  have : Algebra.Etale R (Localization.Away g) := Algebra.Etale.of_isLocalizationAway r
  rw [← IsScalarTower.algebraMap_eq R S (Localization.Away g)]
  exact RingHom.etale_algebraMap.mpr inferInstance

/-- **Descent of a local isomorphism over a finitely generated ℤ-subalgebra.**

Given `[Algebra.IsLocalIso R S]`, there exist:
- a fg ℤ-subalgebra `R₀ ⊆ R`,
- an `R₀`-algebra `S₀` with `[Algebra.IsLocalIso R₀ S₀]`,
- an `R`-algebra isomorphism `S ≃ₐ[R] R ⊗[R₀] S₀`.

This is the `IsLocalIso` analogue of `Algebra.Etale.exists_subalgebra_fg`.

Proof outline (full strategy in PROGRESS.md OBJ A):

1. **Étale descent** (`Algebra.Etale.exists_subalgebra_fg ℤ R S`) gives a fg
   ℤ-subalgebra `R₀^{et} ⊆ R` and an `R₀^{et}`-algebra `S₀^{et}` with
   `Etale R₀^{et} S₀^{et}` and `S ≃ₐ[R] R ⊗[R₀^{et}] S₀^{et}`.
2. **Witness extraction** (`Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top R S`
   + `Submodule.mem_span_finset` + `Algebra.IsStandardOpenImmersion.exists_away`)
   gives a finite cover `{g_i}_{i=1..n}` of `S` with `IsStandardOpenImmersion R
   (Loc.Away g_i)`, witnesses `r_i ∈ R` with `IsLocalization.Away r_i (Loc.Away g_i)`,
   and `s_i ∈ S` with `∑ s_i g_i = 1` in `S`.
3. **Enlargement**: lift `r_i ∈ R` and the `R`-coefficients of (some finite tensor
   representation of) `g_i, s_i ∈ S = R ⊗[R₀^{et}] S₀^{et}` to a fg `ℤ`-subalgebra
   `R₀ ⊇ R₀^{et}` of `R`. Set `S₀ := R₀ ⊗[R₀^{et}] S₀^{et}`.
4. **Descent**: by `Algebra.TensorProduct.cancelBaseChange`, `R ⊗[R₀] S₀ ≃
   R ⊗[R₀^{et}] S₀^{et} ≃ S`. The local-iso witnesses `r_i ∈ R₀` give standard-open
   immersions of `R₀` covering `S₀` via `IsLocalization.atUnits` + faithful-flat
   descent.

The current proof formalises steps 1-2 and sets up the framework; the descent
(step 3-4) is left as the structured sorry below. -/
private lemma _root_.Algebra.IsLocalIso.exists_subalgebra_fg_descent
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsLocalIso R S] :
    ∃ (R₀ : Subalgebra ℤ R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀),
      R₀.FG ∧ Algebra.IsLocalIso R₀ S₀ ∧ Nonempty (S ≃ₐ[R] R ⊗[R₀] S₀) := by
  classical
  -- Step 1. Étale descent.
  haveI : Algebra.Etale R S := Algebra.IsLocalIso.etale_of (R := R) (S := S)
  obtain ⟨R₀et, S₀et, _, _, hfg_et, hetale_S0et, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ R S
  -- Step 2. Witness extraction: from `Ideal.span {g | IsStandardOpenImmersion R (Loc g)} = ⊤`,
  -- get a finite subset summing to 1.
  have hspanS : Ideal.span
      {g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)} = ⊤ :=
    Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top R S
  -- Step 2a: convert the span = ⊤ to a finite partition of unity.
  -- We obtain a Finset `t ⊆ {g | IsStandardOpenImmersion R (Loc.Away g)}` and
  -- coefficients `f : S → S` so that `∑ a ∈ t, f a • a = 1`.
  have h1mem : (1 : S) ∈ Submodule.span S
      {g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)} := by
    show (1 : S) ∈ Ideal.span _
    rw [hspanS]
    trivial
  obtain ⟨f, t, ht_sub, _hfsupp, hsum⟩ :=
    (Submodule.mem_span_iff_exists_finset_subset
      (R := S) (M := S)
      (s := {g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)}) (x := 1)).mp
      h1mem
  -- For each `g ∈ t`, `g` is a standard open immersion witness.
  have hstd : ∀ g ∈ t, Algebra.IsStandardOpenImmersion R (Localization.Away g) := by
    intro g hg
    exact ht_sub hg
  -- Step 3. Witness extraction: for each `g ∈ t`, choose `r_g : R` with
  -- `IsLocalization.Away r_g (Localization.Away g)`.
  choose r hr using fun g hg => (hstd g hg).exists_away
  -- Step 4. Tensor expansions. For each `g ∈ t`, pick a finite representation of `e g`
  -- as `∑_{(a,b) ∈ T_g} a ⊗ₜ b` in `R ⊗[↥R₀et] S₀et`. Likewise for `e (f g)`.
  choose Tg hTg using fun g (_hg : g ∈ t) => TensorProduct.exists_finset (e g)
  choose Tfg hTfg using fun g (_hg : g ∈ t) => TensorProduct.exists_finset (e (f g))
  -- Step 4a. Divisibility witness: from `IsLocalization.Away (r g hg) (Loc.Away g)`
  -- over R, get `n` and `c ∈ S` with `g^n = (algebraMap R S r) * c`. This will be
  -- used in step 4b to descend the local-iso structure to R₀.
  have hr_pow : ∀ g (hg : g ∈ t),
      ∃ n : ℕ, ∃ c : S, g ^ n = (algebraMap R S) (r g hg) * c := fun g hg =>
    @Algebra.IsLocalIso.divisibility_witness R S _ _ _ g (r g hg) (hr g hg)
  choose ng cg hcg using hr_pow
  -- Step 4b. Tensor expansion of `e (cg g hg)`.
  choose Tc hTc using fun g (_hg : g ∈ t) => TensorProduct.exists_finset (e (cg g _hg))
  -- Step 5. Collect all relevant R-elements (the `r_g`'s and the R-coefficients of the
  -- tensor expansions, including those of `e (cg g hg)`) into a finite subset `F` of `R`.
  let F : Finset R :=
    ((t.attach.image (fun g => r g.1 g.2)) ∪
      (t.attach.biUnion fun g => (Tg g.1 g.2).image (fun ab => ab.1)) ∪
      (t.attach.biUnion fun g => (Tfg g.1 g.2).image (fun ab => ab.1))) ∪
    (t.attach.biUnion fun g => (Tc g.1 g.2).image (fun ab => ab.1))
  -- Step 6. Build the enlarged ℤ-subalgebra of `R`.
  let R₀ : Subalgebra ℤ R := R₀et ⊔ Algebra.adjoin ℤ (F : Set R)
  have hR₀_fg : R₀.FG :=
    Subalgebra.FG.sup hfg_et (Subalgebra.fg_adjoin_finset F)
  have hR₀et_le : R₀et ≤ R₀ := le_sup_left
  -- Step 7. Define `S₀ := ↥R₀ ⊗[↥R₀et] S₀et`. To form the tensor product we need an
  -- `↥R₀et`-algebra structure on `↥R₀`, obtained from the inclusion `R₀et ≤ R₀`.
  letI algR₀et_R₀ : Algebra R₀et R₀ :=
    (Subalgebra.inclusion hR₀et_le).toRingHom.toAlgebra
  haveI : IsScalarTower R₀et R₀ R := IsScalarTower.of_algebraMap_eq fun x => by
    show (Subalgebra.inclusion hR₀et_le x).val = (algebraMap R₀et R) x
    rfl
  let S₀ : Type u := R₀ ⊗[R₀et] S₀et
  letI : CommRing S₀ := inferInstance
  -- `S₀` is an `R₀`-algebra via `leftAlgebra` (the left factor of the tensor product).
  letI algR₀_S₀ : Algebra R₀ S₀ := Algebra.TensorProduct.leftAlgebra
  -- Step 8. The descent iso `S ≃ₐ[R] R ⊗[↥R₀] S₀`.
  haveI : IsScalarTower R₀et R₀ S₀ :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show (algebraMap R₀ S₀) (Subalgebra.inclusion hR₀et_le x) = _
      rfl
  -- We need `Algebra R₀ R` (from R₀ subalgebra), `Algebra R₀et R` (already there),
  -- and the scalar tower `IsScalarTower R₀et R₀ R` (provided above).
  let eR : R ⊗[R₀et] S₀et ≃ₐ[R] R ⊗[R₀] (R₀ ⊗[R₀et] S₀et) :=
    (Algebra.TensorProduct.cancelBaseChange (R := R₀et) (S := R₀) (T := R)
      (A := R) (B := S₀et)).symm
  let edesc : S ≃ₐ[R] R ⊗[R₀] S₀ := e.trans eR
  -- Step 9. Assemble the descent data. The remaining nontrivial obligation is the
  -- `Algebra.IsLocalIso R₀ S₀` property; see the discussion in the proof body.
  -- Membership lemmas for F → R₀: the construction of F guarantees that every
  -- `r_g` and every R-coefficient of `e g`, `e (f g)` lies in `R₀`.
  have hF_le : (F : Set R) ⊆ (R₀ : Set R) := by
    intro x hx
    exact le_sup_right (α := Subalgebra ℤ R) (Algebra.subset_adjoin hx)
  have hr_mem : ∀ g (hg : g ∈ t), r g hg ∈ R₀ := by
    intro g hg
    apply hF_le
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
    exact Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩
  have hTg_mem : ∀ g (hg : g ∈ t) (ab : R × S₀et) (_ : ab ∈ Tg g hg), ab.1 ∈ R₀ := by
    intro g hg ab hab
    apply hF_le
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
    exact Finset.mem_biUnion.mpr
      ⟨⟨g, hg⟩, Finset.mem_attach _ _, Finset.mem_image.mpr ⟨ab, hab, rfl⟩⟩
  have hTfg_mem : ∀ g (hg : g ∈ t) (ab : R × S₀et) (_ : ab ∈ Tfg g hg), ab.1 ∈ R₀ := by
    intro g hg ab hab
    apply hF_le
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    exact Finset.mem_biUnion.mpr
      ⟨⟨g, hg⟩, Finset.mem_attach _ _, Finset.mem_image.mpr ⟨ab, hab, rfl⟩⟩
  have hTc_mem : ∀ g (hg : g ∈ t) (ab : R × S₀et) (_ : ab ∈ Tc g hg), ab.1 ∈ R₀ := by
    intro g hg ab hab
    apply hF_le
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_biUnion.mpr
      ⟨⟨g, hg⟩, Finset.mem_attach _ _, Finset.mem_image.mpr ⟨ab, hab, rfl⟩⟩
  -- Canonical lifts: for each `g ∈ t`, define `g₀ : S₀` as the tensor expansion of `e g`,
  -- but with the R-coefficients lifted to R₀ (using `hTg_mem`). Similarly for `(f g)₀`.
  let g₀ : ∀ (g : S) (hg : g ∈ t), S₀ := fun g hg =>
    ∑ ab ∈ (Tg g hg).attach,
      (⟨ab.1.1, hTg_mem g hg ab.1 ab.2⟩ : R₀) ⊗ₜ[R₀et] ab.1.2
  let fg₀ : ∀ (g : S) (hg : g ∈ t), S₀ := fun g hg =>
    ∑ ab ∈ (Tfg g hg).attach,
      (⟨ab.1.1, hTfg_mem g hg ab.1 ab.2⟩ : R₀) ⊗ₜ[R₀et] ab.1.2
  -- Canonical lift `c₀` for the divisibility witness `cg`.
  let c₀ : ∀ (g : S) (hg : g ∈ t), S₀ := fun g hg =>
    ∑ ab ∈ (Tc g hg).attach,
      (⟨ab.1.1, hTc_mem g hg ab.1 ab.2⟩ : R₀) ⊗ₜ[R₀et] ab.1.2
  -- Bridge: under the descent iso `edesc`, the lift `g₀ g hg` matches `e g`. Concretely,
  -- `eR (e g) = 1 ⊗ g₀ g hg` in `R ⊗[R₀] S₀`. This follows from the `cancelBaseChange`
  -- definition acting on simple tensors: `eR (a ⊗ b) = a ⊗ (1 ⊗ b)` after coercion.
  -- We will need this later to lift the partition-of-unity `hsum` from `S` to `S₀`.
  refine ⟨R₀, S₀, ‹_›, ‹_›, hR₀_fg, ?_, ⟨edesc⟩⟩
  -- Goal: `Algebra.IsLocalIso ↥R₀ S₀`.
  --
  -- Strategy: For each `g ∈ t`, the canonical lift `g^{(0)} := ∑ ⟨a, hₐ⟩ ⊗ₜ b` of
  -- `e g ∈ R ⊗[R₀et] S₀et` to `S₀ = ↥R₀ ⊗[R₀et] S₀et` (where each `a ∈ Tg g hg` lies in
  -- R₀ by construction of `F`; see `hTg_mem`) yields a partition-of-unity in `S₀`:
  -- `∑_{g ∈ t} (f g)^{(0)} • g^{(0)} = 1` (lifting `hsum` from `S`). Moreover, the
  -- witness `r_g ∈ R₀` (see `hr_mem`) makes `Localization.Away g^{(0)}` an `R₀`-standard
  -- open immersion via a faithful-flat / pushout descent of `IsLocalization.Away r_g
  -- (Localization.Away g)`.
  --
  -- Apply `Algebra.IsLocalIso.of_span_eq_top` to the set `{g₀ g hg | g ∈ t}`.
  -- (A) Generic bridge helper: for any finite tensor representation of `e x` whose
  -- R-coefficients lift to `R₀`, the corresponding lift in `R₀ ⊗[R₀et] S₀et` maps back
  -- to `x` under `edesc.symm ∘ (1 ⊗ ·)`. This is the common pattern for `g₀`, `fg₀`,
  -- `c₀`. Proving once and specializing avoids tripling the heartbeat cost.
  have bridge_aux : ∀ (T : Finset (R × S₀et)) (Tmem : ∀ ab ∈ T, ab.1 ∈ R₀)
      (x : S) (heq : e x = ∑ ab ∈ T, ab.1 ⊗ₜ[R₀et] ab.2),
      edesc.symm ((1 : R) ⊗ₜ[R₀]
        (∑ ab ∈ T.attach, (⟨ab.1.1, Tmem ab.1 ab.2⟩ : R₀) ⊗ₜ[R₀et] ab.1.2)) = x := by
    intro T Tmem x heq
    show e.symm (eR.symm ((1 : R) ⊗ₜ[R₀] _)) = x
    have heR : eR.symm ((1 : R) ⊗ₜ[R₀]
        (∑ ab ∈ T.attach, (⟨ab.1.1, Tmem ab.1 ab.2⟩ : R₀) ⊗ₜ[R₀et] ab.1.2)) = e x := by
      show Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
        ((1 : R) ⊗ₜ[R₀] (∑ ab ∈ T.attach,
          (⟨ab.1.1, Tmem ab.1 ab.2⟩ : R₀) ⊗ₜ[R₀et] ab.1.2)) = e x
      rw [TensorProduct.tmul_sum, map_sum, heq, ← Finset.sum_attach T]
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [Algebra.TensorProduct.cancelBaseChange_tmul]
      congr 1
      show (algebraMap R₀ R) ⟨ab.1.1, Tmem ab.1 ab.2⟩ • (1 : R) = ab.1.1
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [heR, AlgEquiv.symm_apply_apply]
  -- Specialize for `g₀`, `fg₀`, `c₀` — cheap function applications.
  have hbridge (g : S) (hg : g ∈ t) :
      edesc.symm ((1 : R) ⊗ₜ[R₀] (g₀ g hg : S₀)) = g :=
    bridge_aux (Tg g hg) (hTg_mem g hg) g (hTg g hg)
  have hbridge_f (g : S) (hg : g ∈ t) :
      edesc.symm ((1 : R) ⊗ₜ[R₀] (fg₀ g hg : S₀)) = f g :=
    bridge_aux (Tfg g hg) (hTfg_mem g hg) (f g) (hTfg g hg)
  have hbridge_c (g : S) (hg : g ∈ t) :
      edesc.symm ((1 : R) ⊗ₜ[R₀] (c₀ g hg : S₀)) = cg g hg :=
    bridge_aux (Tc g hg) (hTc_mem g hg) (cg g hg) (hTc g hg)
  -- (B) Lifted partition of unity in `S₀`, via `descent_partition_of_unity_lift` applied
  -- to the bridges. The bridges are first restated in the `e.symm (cancelBaseChange ...)`
  -- form expected by the helper (the `edesc.symm` form is definitionally the same).
  haveI : Algebra.Etale R₀et S₀et := hetale_S0et
  haveI : Module.Flat R₀et S₀et := inferInstance
  have hbridge' : ∀ (g : S) (hg : g ∈ t),
      e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
        ((1 : R) ⊗ₜ[R₀] (g₀ g hg : S₀))) = g := hbridge
  have hbridge_f' : ∀ (g : S) (hg : g ∈ t),
      e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
        ((1 : R) ⊗ₜ[R₀] (fg₀ g hg : S₀))) = f g := hbridge_f
  have hbridge_c' : ∀ (g : S) (hg : g ∈ t),
      e.symm (Algebra.TensorProduct.cancelBaseChange R₀et R₀ R R S₀et
        ((1 : R) ⊗ₜ[R₀] (c₀ g hg : S₀))) = cg g hg := hbridge_c
  have hval_inj : Function.Injective (algebraMap R₀ R) :=
    fun _ _ h => Subtype.ext h
  have hsum₀ : ∑ g ∈ t.attach, fg₀ g.1 g.2 • g₀ g.1 g.2 = (1 : S₀) :=
    Algebra.IsLocalIso.descent_partition_of_unity_lift hval_inj S₀et e hsum g₀ fg₀
      hbridge' hbridge_f'
  -- Span = ⊤: from (B), `1 ∈ Ideal.span (Set.range (fun g : t.attach => g₀ g.1 g.2))`,
  -- hence the span equals ⊤.
  let gs : {g // g ∈ t} → S₀ := fun g => g₀ g.1 g.2
  have hspan₀ : Ideal.span (Set.range gs) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    rw [← hsum₀]
    refine Ideal.sum_mem _ fun g _ => ?_
    rw [smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, rfl⟩)
  -- (C) Standard-open-immersion descent for each lift `g₀ g hg`. The per-witness
  -- argument is encapsulated in `descent_one_isLocalIso_template` (above this lemma);
  -- here we just plug in the per-`(g, hg)` data. The template body currently bottoms
  -- out at the étale-trivializes-after-localization deep step (round 21 target).
  have hstd₀ : ∀ (g : S) (hg : g ∈ t),
      Algebra.IsLocalIso R₀ (Localization.Away (g₀ g hg)) := fun g hg =>
    Algebra.IsLocalIso.descent_one_isLocalIso_template hval_inj e g (r g hg) (hr_mem g hg)
      (hr g hg) (ng g hg) (cg g hg) (hcg g hg) (g₀ g hg) (c₀ g hg)
      (hbridge' g hg) (hbridge_c' g hg)
  -- (D) Conclude using `of_span_eq_top`.
  refine Algebra.IsLocalIso.of_span_eq_top (R := R₀) (S := S₀)
    (s := Set.range gs) hspan₀ ?_
  rintro x ⟨⟨g, hg⟩, rfl⟩
  exact hstd₀ g hg

/-- **The spreading lemma for local isomorphisms.** If `S = colim D_j` is a filtered
colimit of commutative rings and `f : S → T` is a local isomorphism, then `f` descends
to a local isomorphism `D_j → T'` at some stage `j` with `T ≅ S ⊗_{D_j} T'`.

This is the analogue of `Algebra.Etale.exists_subalgebra_fg` for `IsLocalIso`. The
reduction uses `PreIndSpreads.of_isInitial`: given any local iso `f : R → S`, build a
finitely-presented descent `R₀ → S₀` (over `ULift ℤ`) via
`Algebra.IsLocalIso.exists_subalgebra_fg_descent`, and exhibit the pushout square. -/
instance isLocalIso_preIndSpreads :
    MorphismProperty.PreIndSpreads.{u}
      ((RingHom.toMorphismProperty RingHom.IsLocalIso) : MorphismProperty CommRingCat.{u}) := by
  refine MorphismProperty.PreIndSpreads.of_isInitial CommRingCat.isInitial fun R S f hf ↦ ?_
  algebraize [f.hom]
  have hf_eq : f = CommRingCat.ofHom (algebraMap R S) := rfl
  have hLocIso : Algebra.IsLocalIso R S := hf
  obtain ⟨R₀, S₀, _, _, hfg, hLocIso₀, ⟨e⟩⟩ :=
    Algebra.IsLocalIso.exists_subalgebra_fg_descent R S
  letI : Algebra S₀ (↑R ⊗[↥R₀] S₀) := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower R₀ S₀ (↑R ⊗[↥R₀] S₀) := Algebra.TensorProduct.right_isScalarTower
  let g : S₀ →+* S := e.symm.toRingHom.comp <| Algebra.TensorProduct.includeRight.toRingHom
  algebraize [g]
  have hST : IsScalarTower R₀ S₀ ↑S := .of_algebraMap_eq fun x ↦ by
    simpa [RingHom.algebraMap_toAlgebra, g] using (e.symm.toAlgHom.commutes x.val).symm
  refine ⟨.of R₀, .of S₀, CommRingCat.ofHom (algebraMap R₀ R),
      CommRingCat.ofHom g, CommRingCat.ofHom (algebraMap R₀ S₀), ?_, ?_, ?_⟩
  · -- R₀ is finitely presented over ULift ℤ.
    unfold MorphismProperty.isFinitelyPresentable ObjectProperty.isFinitelyPresentable
    apply CommRingCat.isFinitelyPresentable_under
    dsimp
    have heq : CommRingCat.isInitial.to (.of R₀) =
        CommRingCat.ofHom ((algebraMap ℤ R₀).comp ULift.ringEquiv.toRingHom) :=
      CommRingCat.isInitial.hom_ext _ _
    rw [heq]
    refine RingHom.FinitePresentation.comp ?_ ?_
    · have hft : Algebra.FiniteType ℤ R₀ := R₀.fg_iff_finiteType.mp hfg
      have hfp : Algebra.FinitePresentation ℤ R₀ :=
        Algebra.FinitePresentation.of_finiteType.mp hft
      exact (RingHom.finitePresentation_algebraMap (A := ℤ) (B := R₀)).mpr hfp
    · exact .of_bijective ULift.ringEquiv.bijective
  · -- f' : R₀ → S₀ is a local iso.
    show (algebraMap R₀ S₀).IsLocalIso
    rw [RingHom.isLocalIso_algebraMap]
    exact hLocIso₀
  · -- The pushout square.
    rw [hf_eq, ← RingHom.algebraMap_toAlgebra g, CommRingCat.isPushout_iff_isPushout]
    haveI : Algebra.IsPushout R₀ R S₀ (↑R ⊗[↥R₀] S₀) := TensorProduct.isPushout
    exact Algebra.IsPushout.of_equiv (S' := ↑R ⊗[↥R₀] S₀) e.symm rfl

end CategoryTheory.MorphismProperty
