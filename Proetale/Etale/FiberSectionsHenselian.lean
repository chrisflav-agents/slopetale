/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Proetale.Algebra.EtaleSectionSplit
import Proetale.Etale.FinitePushforwardStalkIso

/-!
# Strict henselianity of the fiber localizations of a finite morphism

Let `f : Y ⟶ X` be a finite morphism of schemes and `x : Spec Ω ⟶ X` a geometric point
(`Ω` separably closed). This file instantiates the abstract henselianity package of
`Proetale.Algebra.EtaleSectionSplit` at the localizations of the fiber sections
`S = fiberSections f x` at their maximal ideals, completing the "finite local algebras
over a henselian local ring are henselian" step (Stacks 04GH) of the dévissage for
finite morphisms (blueprint `lemma:pbc-finite`, stage C prerequisite).

## Main results

For a maximal ideal `m` of the fiber sections write `L = Localization.AtPrime m.asIdeal`.

- `AlgebraicGeometry.Scheme.Etale.module_finite_localization_atPrime_fiberSections`:
  `L` is a finite module over the fiber sections.
- `AlgebraicGeometry.Scheme.Etale.forall_module_finite_bijective_pi_localization_fiberSections`:
  every module-finite `L`-algebra splits as the product of its localizations at maximal
  ideals (Stacks 04GG (10) for `L`). This is the splitting hypothesis consumed by the
  results of `Proetale.Algebra.EtaleSectionSplit`.
- `AlgebraicGeometry.Scheme.Etale.isSepClosed_residueField_localization_atPrime_fiberSections`:
  the residue field of `L` is separably closed: it is finite, hence algebraic, over the
  separably closed residue field of the strict localization.
- `AlgebraicGeometry.Scheme.Etale.isStrictlyHenselianLocalRing_localization_atPrime_fiberSections`:
  **`L` is strictly henselian** (Stacks 04GH).
- `AlgebraicGeometry.Scheme.Etale.exists_retraction_of_etale_localization_fiberSections`
  and `AlgebraicGeometry.Scheme.Etale.retraction_eq_of_comp_eq_localization_fiberSections`:
  existence and uniqueness of retractions of étale `L`-algebras compatible with a
  character whose restriction to `L` cuts out the maximal ideal (Stacks 04GG (8) for
  `L`), for downstream cofinality use.

## Proof sketch

The fiber sections `S` split as the finite product of their localizations at maximal
ideals (`bijective_pi_localization_fiberSections`), so `L` is a direct factor of `S`,
hence module-finite over `S`, hence module-finite over the strict localization
`A = strictLocalization x`. Consequently every module-finite `L`-algebra `T` is
module-finite over `A` and therefore splits by the splitting property of the strictly
henselian ring `A` (`finite_maximalSpectrum_and_bijective_pi_localization_of_finite`);
the splitting of `T` is intrinsic to `T`, so it holds over `L` as well. The residue
field of `L` is the residue field of `S` at `m`, a finite extension of the separably
closed residue field of `A`, hence separably closed. Now
`IsStrictlyHenselianLocalRing.of_forall_module_finite_bijective_pi` applies.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X) [IsFinite f]
  (m : MaximalSpectrum (fiberSections f x))

/-- The localization of the fiber sections of a finite morphism at a maximal ideal is a
finite module over the fiber sections: it is a direct factor of the splitting into local
factors. -/
theorem module_finite_localization_atPrime_fiberSections :
    Module.Finite (fiberSections f x) (Localization.AtPrime m.asIdeal) :=
  module_finite_localization_atPrime_of_bijective_pi
    (bijective_pi_localization_fiberSections f x) m.asIdeal

/-- **The splitting hypothesis for the fiber localizations** (Stacks 04GG (10) for the
localization of the fiber sections at a maximal ideal): every module-finite algebra over
the localization of the fiber sections at a maximal ideal splits as the product of its
localizations at maximal ideals. Such an algebra is module-finite over the strict
localization, and the splitting is intrinsic to the algebra. -/
theorem forall_module_finite_bijective_pi_localization_fiberSections :
    ∀ (T : Type u) [CommRing T] [Algebra (Localization.AtPrime m.asIdeal) T],
      Module.Finite (Localization.AtPrime m.asIdeal) T →
      Function.Bijective (Pi.ringHom
        (fun n : MaximalSpectrum T => algebraMap T (Localization.AtPrime n.asIdeal))) := by
  intro T _ _ hT
  haveI : Module.Finite (fiberSections f x) (Localization.AtPrime m.asIdeal) :=
    module_finite_localization_atPrime_fiberSections f x m
  -- `T` is module-finite over the fiber sections
  letI : Algebra (fiberSections f x) T :=
    ((algebraMap (Localization.AtPrime m.asIdeal) T).comp
      (algebraMap (fiberSections f x) (Localization.AtPrime m.asIdeal))).toAlgebra
  haveI : IsScalarTower (fiberSections f x) (Localization.AtPrime m.asIdeal) T :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Module.Finite (fiberSections f x) T :=
    Module.Finite.trans (Localization.AtPrime m.asIdeal) T
  -- hence module-finite over the strict localization
  letI : Algebra (strictLocalization x) T :=
    ((algebraMap (fiberSections f x) T).comp
      (algebraMap (strictLocalization x) (fiberSections f x))).toAlgebra
  haveI : IsScalarTower (strictLocalization x) (fiberSections f x) T :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Module.Finite (strictLocalization x) T :=
    Module.Finite.trans (fiberSections f x) T
  -- the splitting over the strict localization is intrinsic to `T`
  exact (finite_maximalSpectrum_and_bijective_pi_localization_of_finite x T).2

/-- **The residue field of a fiber localization is separably closed**: the residue field
of the localization of the fiber sections at a maximal ideal `m` is the residue field
`S ⧸ m` of the fiber sections at `m`, a finite — hence algebraic — extension of the
separably closed residue field of the strict localization. -/
theorem isSepClosed_residueField_localization_atPrime_fiberSections :
    IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) := by
  -- `m` lies over the maximal ideal of the strict localization
  have hover : m.asIdeal.comap
      (algebraMap (strictLocalization x) (fiberSections f x)) =
      IsLocalRing.maximalIdeal (strictLocalization x) :=
    IsLocalRing.comap_algebraMap_eq_maximalIdeal (fiberSections f x) m.asIdeal
  -- the residue fields, as quotients
  letI K : Type u :=
    strictLocalization x ⧸ IsLocalRing.maximalIdeal (strictLocalization x)
  letI L' : Type u := fiberSections f x ⧸ m.asIdeal
  letI : Field K := Ideal.Quotient.field _
  letI : Field L' := Ideal.Quotient.field _
  letI : Algebra K L' := Ideal.Quotient.algebraQuotientOfLEComap hover.ge
  haveI : IsScalarTower (strictLocalization x) K L' :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.quotientMap_mk).symm
  -- the residue extension is finite, hence algebraic
  haveI : Module.Finite (strictLocalization x) L' :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ (strictLocalization x) m.asIdeal).toLinearMap
      (Ideal.Quotient.mkₐ_surjective (strictLocalization x) m.asIdeal)
  haveI : Module.Finite K L' :=
    Module.Finite.of_restrictScalars_finite (strictLocalization x) K L'
  haveI : Algebra.IsAlgebraic K L' := Algebra.IsAlgebraic.of_finite K L'
  -- `K` is the separably closed residue field of the strict localization
  haveI : IsSepClosed K :=
    inferInstanceAs (IsSepClosed (IsLocalRing.ResidueField (strictLocalization x)))
  haveI : IsSepClosed L' := Algebra.IsAlgebraic.isSepClosed (F := K)
  -- transfer along the canonical isomorphism `S ⧸ m ≃ κ(m)`
  exact IsSepClosed.of_ringEquiv
    (RingEquiv.ofBijective (algebraMap L' m.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField m.asIdeal))

/-- **The localization of the fiber sections of a finite morphism at a maximal ideal is
strictly henselian** (Stacks 04GH): a finite local algebra over the strictly henselian
strict localization is strictly henselian. -/
theorem isStrictlyHenselianLocalRing_localization_atPrime_fiberSections :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m.asIdeal) :=
  haveI : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) :=
    isSepClosed_residueField_localization_atPrime_fiberSections f x m
  IsStrictlyHenselianLocalRing.of_forall_module_finite_bijective_pi
    (forall_module_finite_bijective_pi_localization_fiberSections f x m)

/-- **Retractions of étale algebras over the fiber localizations, existence**
(Stacks 04GG (8) for the localization of the fiber sections at a maximal ideal): every
character `χ : B →+* Ω''` of an étale algebra `B` over the localization of the fiber
sections at a maximal ideal, whose restriction has kernel the maximal ideal, is
compatible with a retraction `σ : B →+* L`. -/
theorem exists_retraction_of_etale_localization_fiberSections
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime m.asIdeal) B]
    (hB : Algebra.Etale (Localization.AtPrime m.asIdeal) B)
    {Ω'' : Type u} [Field Ω''] (χ : B →+* Ω'')
    (hker : RingHom.ker (χ.comp (algebraMap (Localization.AtPrime m.asIdeal) B)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal)) :
    ∃ σ : B →+* Localization.AtPrime m.asIdeal,
      σ.comp (algebraMap (Localization.AtPrime m.asIdeal) B) =
        RingHom.id (Localization.AtPrime m.asIdeal) ∧
      (χ.comp (algebraMap (Localization.AtPrime m.asIdeal) B)).comp σ = χ :=
  haveI : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) :=
    isSepClosed_residueField_localization_atPrime_fiberSections f x m
  IsLocalRing.exists_retraction_of_etale_of_ker_comp_eq
    (forall_module_finite_bijective_pi_localization_fiberSections f x m) B hB χ hker

/-- **Retractions of étale algebras over the fiber localizations, uniqueness**: the
retraction compatible with a character `χ` as in
`AlgebraicGeometry.Scheme.Etale.exists_retraction_of_etale_localization_fiberSections`
is unique. -/
theorem retraction_eq_of_comp_eq_localization_fiberSections
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime m.asIdeal) B]
    (hB : Algebra.Etale (Localization.AtPrime m.asIdeal) B)
    {Ω'' : Type u} [Field Ω''] (χ : B →+* Ω'')
    (hker : RingHom.ker (χ.comp (algebraMap (Localization.AtPrime m.asIdeal) B)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal))
    {σ₁ σ₂ : B →+* Localization.AtPrime m.asIdeal}
    (h₁ : σ₁.comp (algebraMap (Localization.AtPrime m.asIdeal) B) =
      RingHom.id (Localization.AtPrime m.asIdeal))
    (h₂ : σ₂.comp (algebraMap (Localization.AtPrime m.asIdeal) B) =
      RingHom.id (Localization.AtPrime m.asIdeal))
    (hc₁ : (χ.comp (algebraMap (Localization.AtPrime m.asIdeal) B)).comp σ₁ = χ)
    (hc₂ : (χ.comp (algebraMap (Localization.AtPrime m.asIdeal) B)).comp σ₂ = χ) :
    σ₁ = σ₂ :=
  haveI : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) :=
    isSepClosed_residueField_localization_atPrime_fiberSections f x m
  IsLocalRing.retraction_eq_of_comp_eq
    (forall_module_finite_bijective_pi_localization_fiberSections f x m) B hB χ hker
    h₁ h₂ hc₁ hc₂

end AlgebraicGeometry.Scheme.Etale
