/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Proetale.Etale.FinitePushforwardStalkFormula

/-!
# The dictionary between lifts of a geometric point and maximal ideals of the fiber

Let `f : Y ⟶ X` be a finite morphism of schemes, `x : Spec Ω ⟶ X` a geometric point and
`ψ : Ω →+* Ω'` an extension of separably closed fields, with associated morphism
`σ = Spec ψ : Spec Ω' ⟶ Spec Ω`. Write `R = 𝒪^sh_{X, x}` for the strict localization of
`X` at `x` (a strictly henselian local ring) and `T = Γ(Y ×_X Spec R)` for the fiber
sections (`AlgebraicGeometry.Scheme.Etale.fiberSections`), a finite `R`-algebra.

This file identifies the lifts of `x` to `Y` along `σ` with the maximal ideals of `T`,
and deduces the stalk formula for pushforwards along finite morphisms for *any* family
of lifts indexed bijectively by the maximal ideals.

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.charOfLift`: the character `T →+* Ω'` of a lift `y` of
  `x`, namely the evaluation at `y` of the germs of the fiber sections.
- `AlgebraicGeometry.Scheme.Etale.maximalSpectrumOfLift`: the maximal ideal `ker (χ_y)`
  of `T` attached to a lift `y`.
- `AlgebraicGeometry.Scheme.Etale.liftEquivMaximalSpectrum`: the resulting bijection
  between the lifts of `x` to `Y` with values in the algebraic closure of `Ω` and the
  maximal spectrum of `T`.

## Main results

- `AlgebraicGeometry.Scheme.Etale.charOfLift_comp_strictLocalizationToFiberSections`: the
  character of a lift extends the evaluation of the strict localization at `x`.
- `AlgebraicGeometry.Scheme.Etale.charOfLift_liftOfRingHom` and
  `AlgebraicGeometry.Scheme.Etale.liftOfRingHom_charOfLift`: the character of the lift
  associated to a compatible character is the character itself, and conversely a lift is
  reconstructed from its character. So lifts and compatible characters correspond.
- `AlgebraicGeometry.Scheme.Etale.isMaximal_ker_charOfLift`: the kernel of the character
  of a lift is a maximal ideal; the residue field `T ⧸ ker χ` is a finite domain over the
  residue field of `R`, hence a field.
- `AlgebraicGeometry.Scheme.Etale.ringHom_ext_of_ker_eq`: two compatible characters with
  the same kernel agree. Indeed `T ⧸ m` is a finite, hence algebraic, extension of the
  separably closed residue field `K` of `R`, therefore purely inseparable over `K`, and a
  purely inseparable extension admits at most one embedding into `Ω'` over `K`.
- `AlgebraicGeometry.Scheme.Etale.maximalSpectrumOfLift_injective` and
  `AlgebraicGeometry.Scheme.Etale.liftEquivMaximalSpectrum`: the dictionary.
- `AlgebraicGeometry.Scheme.Etale.isIso_pushforwardStalkToPiStalk_of_bijective`: **the
  stalk formula for an arbitrary family of lifts**: if a finite family `y : ι → Y(Ω')` of
  lifts of `x` induces a bijection onto the maximal spectrum of `T`, then the comparison
  map `(f_* F)_x̄ ⟶ ∏ᵢ F_{y i}` is an isomorphism for every abelian sheaf `F`.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme.Etale

attribute [local instance] finite_maximalSpectrum_fiberSections

/-- Transporting a product projection along an equality of indices. -/
private lemma pi_π_comp_eqToHom {C : Type*} [Category C] {α : Type*} (B : α → C)
    [HasProduct B] {a b : α} (h : a = b) :
    Pi.π B a ≫ eqToHom (congrArg B h) = Pi.π B b := by
  subst h
  simp

/-- The top-level sections of the inverse of `isoSpec` are the inverse of `ΓSpecIso`. -/
private lemma isoSpec_inv_appTop''' (Z : Scheme.{u}) [IsAffine Z] :
    Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
  rw [← Iso.comp_hom_eq_id (Scheme.ΓSpecIso Γ(Z, ⊤)), ← Scheme.toSpecΓ_appTop,
    ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop]

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X) {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
  (ψ : Ω →+* Ω')

/-!
### The character of a lift
-/

/-- **The character of a lift of the geometric point**: for a geometric point
`y : Spec Ω' ⟶ Y` of `Y` lying over `x` along the extension `ψ : Ω →+* Ω'`, evaluation at
`y` of the germs of the fiber sections is a character `T →+* Ω'` of the fiber sections. -/
noncomputable def charOfLift (y : Spec (CommRingCat.of Ω') ⟶ Y)
    (hy : y ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x) : fiberSections f x →+* Ω' :=
  (fiberSectionsToStrictLocalization f x (Spec.map (CommRingCat.ofHom ψ)) y hy ≫
    strictLocalizationEval y).hom

/-- The defining equation of the character of a lift: it is the evaluation at `y` of the
comparison map from the fiber sections to the strict localization of `Y` at `y`. This is
the evaluation compatibility consumed by the results of
`Proetale.Etale.FinitePushforwardStalkCofinal`. -/
lemma fiberSectionsToStrictLocalization_charOfLift_eval (y : Spec (CommRingCat.of Ω') ⟶ Y)
    (hy : y ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x) :
    fiberSectionsToStrictLocalization f x (Spec.map (CommRingCat.ofHom ψ)) y hy ≫
      strictLocalizationEval y = CommRingCat.ofHom (charOfLift f x ψ y hy) :=
  rfl

/-- **The character of a lift extends evaluation at `x`**: the composition of the
character of a lift `y` with the algebra structure `R ⟶ T` of the fiber sections is the
evaluation of the strict localization at `x`, followed by the field extension `ψ`. -/
lemma charOfLift_comp_strictLocalizationToFiberSections (y : Spec (CommRingCat.of Ω') ⟶ Y)
    (hy : y ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x) :
    (charOfLift f x ψ y hy).comp (strictLocalizationToFiberSections f x).hom =
      ψ.comp (strictLocalizationEval x).hom := by
  have hnat : Scheme.Γ.map (Spec.map (CommRingCat.ofHom ψ)).op ≫
      (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom ψ := by
    rw [Scheme.Γ_map_op]
    exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  have hcat : strictLocalizationToFiberSections f x ≫
      fiberSectionsToStrictLocalization f x (Spec.map (CommRingCat.ofHom ψ)) y hy ≫
        strictLocalizationEval y =
      strictLocalizationEval x ≫ CommRingCat.ofHom ψ := by
    refine colimit.hom_ext fun P => ?_
    obtain ⟨p⟩ := P
    change toStrictLocalization x p ≫ _ = toStrictLocalization x p ≫ _
    have hfst : (pullbackFiberLift f x (Spec.map (CommRingCat.ofHom ψ)) y hy p.1 p.2).val ≫
        pullback.fst p.1.hom f = Spec.map (CommRingCat.ofHom ψ) ≫ p.2.val :=
      pullbackFiberLift_val_fst f x (Spec.map (CommRingCat.ofHom ψ)) y hy p.1 p.2
    calc toStrictLocalization x p ≫ strictLocalizationToFiberSections f x ≫
            fiberSectionsToStrictLocalization f x (Spec.map (CommRingCat.ofHom ψ)) y hy ≫
              strictLocalizationEval y
        = Scheme.Γ.map (pullback.fst p.1.hom f).op ≫
            Scheme.Γ.map ((pullbackFiberLift f x (Spec.map (CommRingCat.ofHom ψ)) y hy
              p.1 p.2).val).op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom := by
          rw [toStrictLocalization_strictLocalizationToFiberSections_assoc,
            toFiberSections_fiberSectionsToStrictLocalization_assoc,
            toStrictLocalization_strictLocalizationEval]
          rfl
      _ = Scheme.Γ.map ((Spec.map (CommRingCat.ofHom ψ) ≫ p.2.val).op) ≫
            (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom := by
          rw [← Category.assoc, ← Functor.map_comp, ← op_comp, hfst]
      _ = Scheme.Γ.map p.2.val.op ≫ Scheme.Γ.map (Spec.map (CommRingCat.ofHom ψ)).op ≫
            (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom := by
          rw [op_comp, Functor.map_comp, Category.assoc]
      _ = Scheme.Γ.map p.2.val.op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫
            CommRingCat.ofHom ψ := by rw [hnat]
      _ = toStrictLocalization x p ≫ strictLocalizationEval x ≫ CommRingCat.ofHom ψ :=
          (toStrictLocalization_strictLocalizationEval_assoc x p
            (CommRingCat.ofHom ψ)).symm
  have h := congrArg CommRingCat.Hom.hom hcat
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h
  exact h

/-!
### Lifts and compatible characters correspond
-/

variable [IsFinite f]

/-- **The character of the lift associated to a character is the character itself**: a
restatement of
`AlgebraicGeometry.Scheme.Etale.fiberSectionsToStrictLocalization_liftOfRingHom_eval`. -/
theorem charOfLift_liftOfRingHom (p₀ : (geometricPoint x).fiber.Elements)
    (hp₀ : IsAffine p₀.1.left) (χ : fiberSections f x →+* Ω')
    (hχ : χ.comp (strictLocalizationToFiberSections f x).hom =
      ψ.comp (strictLocalizationEval x).hom) :
    charOfLift f x ψ (liftOfRingHom f x p₀ hp₀ χ)
      (liftOfRingHom_comp f x p₀ hp₀ χ hχ) = χ :=
  congrArg CommRingCat.Hom.hom
    (fiberSectionsToStrictLocalization_liftOfRingHom_eval f x χ p₀ hp₀ hχ)

/-- **A lift is reconstructed from its character**: the lift associated to the character
of a geometric point `y` of `Y` over `x` is `y` again. Together with
`AlgebraicGeometry.Scheme.Etale.charOfLift_liftOfRingHom` this identifies the lifts of `x`
with the characters of the fiber sections extending evaluation at `x`. -/
theorem liftOfRingHom_charOfLift (p₀ : (geometricPoint x).fiber.Elements)
    (hp₀ : IsAffine p₀.1.left) (y : Spec (CommRingCat.of Ω') ⟶ Y)
    (hy : y ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x) :
    liftOfRingHom f x p₀ hp₀ (charOfLift f x ψ y hy) = y := by
  haveI := hp₀
  haveI : IsAffine ((𝟭 Scheme.{u}).obj p₀.1.left) := hp₀
  haveI hT : IsAffine (pullback p₀.1.hom f) := inferInstance
  haveI : IsAffine ((CategoryTheory.Over.forget Y).obj
      ((Etale.forget Y).obj ((Over.pullback @Etale ⊤ f).obj p₀.1))) := hT
  -- the value of a fiber section at `y` is its value under the character
  have key := eval_pullbackFiberLift_apply f x (Spec.map (CommRingCat.ofHom ψ)) y hy
    (charOfLift f x ψ y hy)
    (fiberSectionsToStrictLocalization_charOfLift_eval f x ψ y hy) p₀
  -- hence the lifted point of the fiber is the point associated to the character
  have hval : (pullbackFiberLift f x (Spec.map (CommRingCat.ofHom ψ)) y hy p₀.1 p₀.2).val =
      Spec.map (CommRingCat.ofHom
          ((charOfLift f x ψ y hy).comp (toFiberSections f x p₀).hom)) ≫
        (pullback p₀.1.hom f).isoSpec.inv := by
    apply ext_of_isAffine
    have e1 : (Spec.map (CommRingCat.ofHom
          ((charOfLift f x ψ y hy).comp (toFiberSections f x p₀).hom))).appTop =
        (Scheme.ΓSpecIso Γ(pullback p₀.1.hom f, ⊤)).hom ≫
          CommRingCat.ofHom ((charOfLift f x ψ y hy).comp (toFiberSections f x p₀).hom) ≫
          (Scheme.ΓSpecIso (CommRingCat.of Ω')).inv := by
      rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [Scheme.Hom.comp_appTop, isoSpec_inv_appTop''', e1, Iso.inv_hom_id_assoc,
      Iso.eq_comp_inv]
    ext a
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using key a
  change Spec.map (CommRingCat.ofHom
      ((charOfLift f x ψ y hy).comp (toFiberSections f x p₀).hom)) ≫
    (pullback p₀.1.hom f).isoSpec.inv ≫ pullback.snd p₀.1.hom f = y
  rw [← Category.assoc, ← hval]
  exact pullbackFiberLift_val_snd f x (Spec.map (CommRingCat.ofHom ψ)) y hy p₀.1 p₀.2

/-!
### The kernel of a compatible character is a maximal ideal

A character `χ : T →+* Ω'` extending the evaluation of the strict localization `R` at `x`
kills the maximal ideal of `R`, so `T ⧸ ker χ` is a module over the residue field `K` of
`R`, finite since `T` is finite over `R`. It is a domain since it embeds into `Ω'`, hence
a field.
-/

omit [IsSepClosed Ω'] [IsFinite f] in
/-- A character of the fiber sections extending the evaluation of the strict localization
kills the maximal ideal of the strict localization. -/
private lemma maximalIdeal_le_comap_ker (χ : fiberSections f x →+* Ω')
    (hχ : χ.comp (strictLocalizationToFiberSections f x).hom =
      ψ.comp (strictLocalizationEval x).hom) :
    IsLocalRing.maximalIdeal (strictLocalization x) ≤
      (RingHom.ker χ).comap (algebraMap (strictLocalization x) (fiberSections f x)) := by
  intro z hz
  rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_fiberSections_eq]
  have h1 : χ ((strictLocalizationToFiberSections f x).hom z) =
      ψ ((strictLocalizationEval x).hom z) := RingHom.congr_fun hχ z
  rw [h1, (mem_maximalIdeal_strictLocalization_iff x z).mp hz, map_zero]

omit [IsSepClosed Ω'] in
/-- **The kernel of a compatible character of the fiber sections is maximal**: for a
finite morphism, the quotient of the fiber sections by the kernel of a character
extending the evaluation of the strict localization is a finite domain over the residue
field of the strict localization, hence a field. -/
theorem isMaximal_ker_of_comp_eq (χ : fiberSections f x →+* Ω')
    (hχ : χ.comp (strictLocalizationToFiberSections f x).hom =
      ψ.comp (strictLocalizationEval x).hom) :
    (RingHom.ker χ).IsMaximal := by
  letI K : Type u :=
    strictLocalization x ⧸ IsLocalRing.maximalIdeal (strictLocalization x)
  letI Q : Type u := fiberSections f x ⧸ RingHom.ker χ
  letI : Field K := Ideal.Quotient.field _
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  haveI : IsDomain Q := Ideal.Quotient.isDomain _
  letI : Algebra K Q :=
    Ideal.Quotient.algebraQuotientOfLEComap (maximalIdeal_le_comap_ker f x ψ χ hχ)
  haveI : IsScalarTower (strictLocalization x) K Q :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.quotientMap_mk).symm
  haveI : Module.Finite (strictLocalization x) Q :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ (strictLocalization x) (RingHom.ker χ)).toLinearMap
      (Ideal.Quotient.mkₐ_surjective (strictLocalization x) (RingHom.ker χ))
  haveI : Module.Finite K Q :=
    Module.Finite.of_restrictScalars_finite (strictLocalization x) K Q
  haveI : Algebra.IsIntegral K Q := Algebra.IsIntegral.of_finite K Q
  exact Ideal.Quotient.maximal_of_isField _
    (isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K))

/-- **The kernel of the character of a lift is a maximal ideal of the fiber sections.** -/
theorem isMaximal_ker_charOfLift (y : Spec (CommRingCat.of Ω') ⟶ Y)
    (hy : y ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x) :
    (RingHom.ker (charOfLift f x ψ y hy)).IsMaximal :=
  isMaximal_ker_of_comp_eq f x ψ _
    (charOfLift_comp_strictLocalizationToFiberSections f x ψ y hy)

/-- **The maximal ideal of the fiber sections attached to a lift of the geometric
point**: the kernel of the character of the lift. -/
noncomputable def maximalSpectrumOfLift (y : Spec (CommRingCat.of Ω') ⟶ Y)
    (hy : y ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x) :
    MaximalSpectrum (fiberSections f x) :=
  ⟨RingHom.ker (charOfLift f x ψ y hy), isMaximal_ker_charOfLift f x ψ y hy⟩

@[simp]
lemma maximalSpectrumOfLift_asIdeal (y : Spec (CommRingCat.of Ω') ⟶ Y)
    (hy : y ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x) :
    (maximalSpectrumOfLift f x ψ y hy).asIdeal = RingHom.ker (charOfLift f x ψ y hy) :=
  rfl

/-!
### Uniqueness of compatible characters with a given kernel

The residue field `T ⧸ m` at a maximal ideal `m` of the fiber sections is a finite, hence
algebraic, extension of the residue field `K` of the strict localization, which is
separably closed by strict henselianity. So `T ⧸ m` is purely inseparable over `K`, and a
purely inseparable extension admits at most one embedding into `Ω'` over `K`.
-/

omit [IsSepClosed Ω'] in
/-- **Two compatible characters of the fiber sections with the same kernel agree.** -/
theorem ringHom_ext_of_ker_eq {χ₁ χ₂ : fiberSections f x →+* Ω'}
    (h₁ : χ₁.comp (strictLocalizationToFiberSections f x).hom =
      ψ.comp (strictLocalizationEval x).hom)
    (h₂ : χ₂.comp (strictLocalizationToFiberSections f x).hom =
      ψ.comp (strictLocalizationEval x).hom)
    (hker : RingHom.ker χ₁ = RingHom.ker χ₂) : χ₁ = χ₂ := by
  set I : Ideal (fiberSections f x) := RingHom.ker χ₁ with hI
  haveI : I.IsMaximal := isMaximal_ker_of_comp_eq f x ψ χ₁ h₁
  letI K : Type u :=
    strictLocalization x ⧸ IsLocalRing.maximalIdeal (strictLocalization x)
  letI L : Type u := fiberSections f x ⧸ I
  letI : Field K := Ideal.Quotient.field _
  letI : Field L := Ideal.Quotient.field _
  letI : Algebra K L :=
    Ideal.Quotient.algebraQuotientOfLEComap (maximalIdeal_le_comap_ker f x ψ χ₁ h₁)
  haveI : IsScalarTower (strictLocalization x) K L :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.quotientMap_mk).symm
  haveI : Module.Finite (strictLocalization x) L :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ (strictLocalization x) I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective (strictLocalization x) I)
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite (strictLocalization x) K L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  haveI : IsSepClosed K :=
    inferInstanceAs (IsSepClosed (IsLocalRing.ResidueField (strictLocalization x)))
  -- the residue field of the strict localization embeds into `Ω'` via `ψ`
  letI evalK : K →+* Ω := Ideal.Quotient.lift _ (strictLocalizationEval x).hom
    fun a ha => (mem_maximalIdeal_strictLocalization_iff x a).mp ha
  letI : Algebra K Ω' := (ψ.comp evalK).toAlgebra
  -- the two characters induce `K`-algebra embeddings of `L` into `Ω'`
  have hcomm : ∀ (χ : fiberSections f x →+* Ω')
      (hχ : χ.comp (strictLocalizationToFiberSections f x).hom =
        ψ.comp (strictLocalizationEval x).hom) (hz : ∀ z ∈ I, χ z = 0) (k : K),
      (Ideal.Quotient.lift I χ hz) (algebraMap K L k) = algebraMap K Ω' k := by
    intro χ hχ hz k
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal
      (strictLocalization x)) k
    have hmk : Ideal.Quotient.mk I ((strictLocalizationToFiberSections f x).hom a) =
        algebraMap K L (Ideal.Quotient.mk _ a) := (Ideal.quotientMap_mk).symm
    calc (Ideal.Quotient.lift I χ hz) (algebraMap K L (Ideal.Quotient.mk _ a))
        = (Ideal.Quotient.lift I χ hz)
            (Ideal.Quotient.mk I ((strictLocalizationToFiberSections f x).hom a)) := by
          rw [hmk]
      _ = χ ((strictLocalizationToFiberSections f x).hom a) := Ideal.Quotient.lift_mk _ _ _
      _ = ψ ((strictLocalizationEval x).hom a) := RingHom.congr_fun hχ a
      _ = algebraMap K Ω' (Ideal.Quotient.mk _ a) := rfl
  have hz₁ : ∀ z ∈ I, χ₁ z = 0 := fun z hz => RingHom.mem_ker.mp hz
  have hz₂ : ∀ z ∈ I, χ₂ z = 0 := fun z hz => RingHom.mem_ker.mp (hker ▸ hz)
  letI e₁ : L →ₐ[K] Ω' :=
    { toRingHom := Ideal.Quotient.lift I χ₁ hz₁
      commutes' := hcomm χ₁ h₁ hz₁ }
  letI e₂ : L →ₐ[K] Ω' :=
    { toRingHom := Ideal.Quotient.lift I χ₂ hz₂
      commutes' := hcomm χ₂ h₂ hz₂ }
  have he : e₁ = e₂ := Subsingleton.elim _ _
  refine RingHom.ext fun z => ?_
  exact congrArg (fun e : L →ₐ[K] Ω' => e (Ideal.Quotient.mk I z)) he

/-!
### The dictionary between lifts and maximal ideals
-/

/-- **The maximal ideal attached to a lift determines the lift**: a lift of `x` to `Y` is
reconstructed from its character, and a compatible character is determined by its
kernel. -/
theorem maximalSpectrumOfLift_injective :
    Function.Injective (fun yy : {y : Spec (CommRingCat.of Ω') ⟶ Y //
        y ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x} =>
      maximalSpectrumOfLift f x ψ yy.1 yy.2) := by
  rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ h
  obtain ⟨p₀, hp₀⟩ := exists_elements_isAffine x
  have hker : RingHom.ker (charOfLift f x ψ y₁ hy₁) =
      RingHom.ker (charOfLift f x ψ y₂ hy₂) := congrArg MaximalSpectrum.asIdeal h
  have hchar : charOfLift f x ψ y₁ hy₁ = charOfLift f x ψ y₂ hy₂ :=
    ringHom_ext_of_ker_eq f x ψ
      (charOfLift_comp_strictLocalizationToFiberSections f x ψ y₁ hy₁)
      (charOfLift_comp_strictLocalizationToFiberSections f x ψ y₂ hy₂) hker
  refine Subtype.ext ((liftOfRingHom_charOfLift f x ψ p₀ hp₀ y₁ hy₁).symm.trans ?_)
  rw [hchar]
  exact liftOfRingHom_charOfLift f x ψ p₀ hp₀ y₂ hy₂

/-- The lifts of a geometric point along a finite morphism are finite in number. -/
theorem finite_lifts : Finite {y : Spec (CommRingCat.of Ω') ⟶ Y //
    y ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x} :=
  Finite.of_injective _ (maximalSpectrumOfLift_injective f x ψ)

/-- **Every maximal ideal of the fiber sections is the kernel of the character of a
lift**, provided the extension field is the algebraic closure of `Ω`: the residue
extension at the maximal ideal may be inseparable, so the algebraic closure is necessary
in general. -/
theorem exists_lift_maximalSpectrumOfLift_eq (m : MaximalSpectrum (fiberSections f x)) :
    ∃ (y : Spec (CommRingCat.of (AlgebraicClosure Ω)) ⟶ Y)
      (hy : y ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))) ≫ x),
      maximalSpectrumOfLift f x (algebraMap Ω (AlgebraicClosure Ω)) y hy = m := by
  obtain ⟨p₀, hp₀⟩ := exists_elements_isAffine x
  obtain ⟨χ, hker, hcomp⟩ := exists_ringHom_ker_eq f x m
  refine ⟨liftOfRingHom f x p₀ hp₀ χ, liftOfRingHom_comp f x p₀ hp₀ χ hcomp,
    MaximalSpectrum.ext ?_⟩
  change RingHom.ker (charOfLift f x (algebraMap Ω (AlgebraicClosure Ω))
    (liftOfRingHom f x p₀ hp₀ χ) _) = m.asIdeal
  rw [charOfLift_liftOfRingHom f x (algebraMap Ω (AlgebraicClosure Ω)) p₀ hp₀ χ hcomp]
  exact hker

/-- **The dictionary between lifts of a geometric point and maximal ideals of the fiber
sections**: for a finite morphism `f : Y ⟶ X` and a geometric point `x : Spec Ω ⟶ X`, the
lifts of `x` to `Y` with values in the algebraic closure of `Ω` are in bijection with the
maximal ideals of the fiber sections over the strict localization, via the kernel of the
character of the lift. -/
noncomputable def liftEquivMaximalSpectrum :
    {y : Spec (CommRingCat.of (AlgebraicClosure Ω)) ⟶ Y //
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))) ≫ x} ≃
      MaximalSpectrum (fiberSections f x) :=
  Equiv.ofBijective
    (fun yy => maximalSpectrumOfLift f x (algebraMap Ω (AlgebraicClosure Ω)) yy.1 yy.2)
    ⟨maximalSpectrumOfLift_injective f x (algebraMap Ω (AlgebraicClosure Ω)), fun m => by
      obtain ⟨y, hy, h⟩ := exists_lift_maximalSpectrumOfLift_eq f x m
      exact ⟨⟨y, hy⟩, h⟩⟩

@[simp]
lemma liftEquivMaximalSpectrum_apply
    (yy : {y : Spec (CommRingCat.of (AlgebraicClosure Ω)) ⟶ Y //
      y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))) ≫ x}) :
    liftEquivMaximalSpectrum f x yy =
      maximalSpectrumOfLift f x (algebraMap Ω (AlgebraicClosure Ω)) yy.1 yy.2 :=
  rfl

/-!
### The stalk formula for an arbitrary family of lifts
-/

/-- **The stalk formula for pushforwards along finite morphisms, for an arbitrary family
of lifts**: let `f : Y ⟶ X` be a finite morphism, `x : Spec Ω ⟶ X` a geometric point and
`y : ι → Y(Ω')` a finite family of lifts of `x` along an extension `ψ : Ω →+* Ω'` of
separably closed fields. If the associated maximal ideals of the fiber sections exhaust
the maximal spectrum bijectively — i.e. the family is exactly the family of *all* lifts,
without repetitions — then for every abelian sheaf `F` on the small étale site of `Y` the
comparison map `(f_* F)_x̄ ⟶ ∏ᵢ F_{y i}` is an isomorphism. -/
theorem isIso_pushforwardStalkToPiStalk_of_bijective {ι : Type u} [Finite ι]
    (y : ι → (Spec (CommRingCat.of Ω') ⟶ Y))
    (hy : ∀ i, y i ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x)
    (hb : Function.Bijective (fun i ↦ maximalSpectrumOfLift f x ψ (y i) (hy i)))
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    IsIso (pushforwardStalkToPiStalk f x (Spec.map (CommRingCat.ofHom ψ)) y hy F) := by
  classical
  haveI : Fintype (MaximalSpectrum (fiberSections f x)) := Fintype.ofFinite _
  set σ : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω) :=
    Spec.map (CommRingCat.ofHom ψ) with hσ
  set e : ι ≃ MaximalSpectrum (fiberSections f x) := Equiv.ofBijective _ hb with he
  obtain ⟨p₁, es, hes, hnot, hmem, -⟩ := exists_elements_isColimit_cofanOfIdempotents f x
  have hy' : ∀ m : MaximalSpectrum (fiberSections f x), y (e.symm m) ≫ f = σ ≫ x :=
    fun m => hy (e.symm m)
  have hker : ∀ m : MaximalSpectrum (fiberSections f x),
      RingHom.ker (charOfLift f x ψ (y (e.symm m)) (hy' m)) = m.asIdeal :=
    fun m => congrArg MaximalSpectrum.asIdeal (e.apply_symm_apply m)
  -- the stalk formula for the reindexed family
  haveI hiso : IsIso (pushforwardStalkToPiStalk f x σ (fun m => y (e.symm m)) hy' F) :=
    isIso_pushforwardStalkToPiStalk_of_data f x p₁ σ es hes hnot hmem
      (fun m => y (e.symm m)) hy' (fun m => charOfLift f x ψ (y (e.symm m)) (hy' m)) hker
      (fun m => fiberSectionsToStrictLocalization_charOfLift_eval f x ψ
        (y (e.symm m)) (hy' m)) F
  -- transfer back along the reindexing isomorphism
  set B : ι → Ab.{u + 1} := fun i => (geometricPoint (y i)).sheafFiber.obj F with hB
  set φ : (∏ᶜ B : Ab.{u + 1}) ⟶ ∏ᶜ fun m => B (e.symm m) :=
    Pi.map' e.symm (fun m => 𝟙 (B (e.symm m))) with hφ
  haveI : IsIso φ := by
    refine ⟨Pi.map' e (fun i => eqToHom (congrArg B (e.symm_apply_apply i))), ?_, ?_⟩
    · refine Pi.hom_ext _ _ fun i => ?_
      rw [Category.assoc, hφ, Pi.map'_comp_π, ← Category.assoc, Pi.map'_comp_π,
        Category.comp_id, Category.id_comp]
      exact pi_π_comp_eqToHom B (e.symm_apply_apply i)
    · refine Pi.hom_ext _ _ fun m => ?_
      rw [Category.assoc, hφ, Pi.map'_comp_π, Category.comp_id, Pi.map'_comp_π,
        Category.id_comp]
      exact pi_π_comp_eqToHom (fun m => B (e.symm m)) (e.apply_symm_apply m)
  have hcomp : pushforwardStalkToPiStalk f x σ y hy F ≫ φ =
      pushforwardStalkToPiStalk f x σ (fun m => y (e.symm m)) hy' F := by
    refine Pi.hom_ext _ _ fun m => ?_
    rw [Category.assoc, hφ, Pi.map'_comp_π, Category.comp_id,
      pushforwardStalkToPiStalk_π, pushforwardStalkToPiStalk_π]
  haveI : IsIso (pushforwardStalkToPiStalk f x σ y hy F ≫ φ) := hcomp ▸ hiso
  exact IsIso.of_isIso_comp_right _ φ

end AlgebraicGeometry.Scheme.Etale
