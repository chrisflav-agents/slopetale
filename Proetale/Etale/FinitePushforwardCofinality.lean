/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Maps
import Proetale.Etale.FinitePushforwardSummandLocal

/-!
# Cofinality of the summand system and the fiber localization comparison

This file completes stage C of the program towards the stalk formula for pushforwards
along finite morphisms (blueprint `lemma:pbc-finite`), building on
`Proetale.Etale.FinitePushforwardSummandSystem` and
`Proetale.Etale.FinitePushforwardSummandLocal`, and closing the goal recorded in the
docstring of `Proetale.Etale.FinitePushforwardStalkCofinal`.

Let `f : Y ⟶ X` be a finite morphism of schemes, `x : Spec Ω ⟶ X` a geometric point,
`p₁` a splitting stage carrying a complete orthogonal family of idempotents `es`, `i` a
distinguished index and `y : Spec Ω' ⟶ Y` a geometric point over `x` with compatible
character `χ` of the fiber sections cutting out the maximal ideal `m` avoiding the
distinguished idempotent.

## Main results

- `AlgebraicGeometry.Scheme.Etale.exists_summandFunctor_hom`: **dominance of the
  summand system**: every étale neighbourhood of `y` is dominated by a split summand.
  An affine common refinement of the neighbourhood and a base summand is étale over the
  summand, so its ring of functions is an étale algebra over the strictly henselian
  summand sections after base change; the retraction of
  `Proetale.Etale.FinitePushforwardSummandLocal` maps it back to the summand sections,
  and the resulting homomorphism descends to a finite stage of the summand system by
  finite presentation.
- `AlgebraicGeometry.Scheme.Etale.initial_summandFunctor`: together with the equalizing
  condition `AlgebraicGeometry.Scheme.Etale.exists_summandFunctor_map_comp_eq`, the
  summand system is initial among the étale neighbourhoods of `y`.
- `AlgebraicGeometry.Scheme.Etale.isIso_summandSectionsToStrictLocalization`: the germ
  comparison from the summand sections to the strict localization of `Y` at `y` is an
  isomorphism.
- `AlgebraicGeometry.Scheme.Etale.bijective_localizationAtPrimeToStrictLocalization`:
  **the stage C closure**: the comparison map
  `AlgebraicGeometry.Scheme.Etale.localizationAtPrimeToStrictLocalization` from the
  localization of the fiber sections at `m` to the strict localization of `Y` at `y` is
  bijective.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

open scoped TensorProduct

/-!
### Retraction-compatible homomorphisms out of étale algebras

For a local ring `Λ` admitting retractions of étale algebras compatibly with a
character `χΛ` cutting out the maximal ideal, every étale `R`-algebra `B` with a
character compatible with `χΛ` over `R` maps to `Λ` over `R`, compatibly with the
characters: base change `B` to the étale `Λ`-algebra `Λ ⊗[R] B`, lift the characters to
the tensor product and retract.
-/

section EtaleRetraction

variable {R Λ B : Type u} [CommRing R] [CommRing Λ] [CommRing B]
  [Algebra R Λ] [Algebra R B] {Ω'' : Type u} [Field Ω'']

private lemma exists_comp_eq_of_etale [IsLocalRing Λ] (hB : Algebra.Etale R B)
    (χΛ : Λ →+* Ω'') (χB : B →+* Ω'')
    (hcomm : ∀ r : R, χB (algebraMap R B r) = χΛ (algebraMap R Λ r))
    (hkerΛ : RingHom.ker χΛ = IsLocalRing.maximalIdeal Λ)
    (hret : ∀ (T : Type u) [CommRing T] [Algebra Λ T], Algebra.Etale Λ T →
      ∀ χT : T →+* Ω'',
      RingHom.ker (χT.comp (algebraMap Λ T)) = IsLocalRing.maximalIdeal Λ →
      ∃ τ : T →+* Λ, τ.comp (algebraMap Λ T) = RingHom.id Λ ∧
        (χT.comp (algebraMap Λ T)).comp τ = χT) :
    ∃ s : B →+* Λ, s.comp (algebraMap R B) = algebraMap R Λ ∧ χΛ.comp s = χB := by
  haveI := hB
  letI : Algebra R Ω'' := (χΛ.comp (algebraMap R Λ)).toAlgebra
  haveI hTet : Algebra.Etale Λ (Λ ⊗[R] B) := inferInstance
  set χT : (Λ ⊗[R] B) →ₐ[R] Ω'' := Algebra.TensorProduct.lift
    ⟨χΛ, fun _ => rfl⟩ ⟨χB, fun r => hcomm r⟩ (fun _ _ => Commute.all _ _) with hχT
  have hχT1 : χT.toRingHom.comp (algebraMap Λ (Λ ⊗[R] B)) = χΛ := by
    refine RingHom.ext fun l => ?_
    have h1 : algebraMap Λ (Λ ⊗[R] B) l = l ⊗ₜ[R] (1 : B) := rfl
    rw [RingHom.comp_apply, h1]
    have h2 : χT.toRingHom (l ⊗ₜ[R] (1 : B)) = χΛ l * χB 1 := by
      rw [hχT]
      exact Algebra.TensorProduct.lift_tmul _ _ _ l 1
    have h3 : χΛ l * χB 1 = χΛ l := by rw [map_one, mul_one]
    exact h2.trans h3
  have hkerT : RingHom.ker (χT.toRingHom.comp (algebraMap Λ (Λ ⊗[R] B))) =
      IsLocalRing.maximalIdeal Λ := by
    rw [hχT1]
    exact hkerΛ
  obtain ⟨τ, hτ1, hτ2⟩ := hret (Λ ⊗[R] B) hTet χT.toRingHom hkerT
  rw [hχT1] at hτ2
  refine ⟨τ.comp Algebra.TensorProduct.includeRight.toRingHom, ?_, ?_⟩
  · refine RingHom.ext fun r => ?_
    have h1 : (Algebra.TensorProduct.includeRight : B →ₐ[R] Λ ⊗[R] B)
        (algebraMap R B r) = algebraMap R (Λ ⊗[R] B) r :=
      Algebra.TensorProduct.includeRight.commutes r
    have h2 : algebraMap R (Λ ⊗[R] B) r =
        algebraMap Λ (Λ ⊗[R] B) (algebraMap R Λ r) := rfl
    have h3 : τ (algebraMap Λ (Λ ⊗[R] B) (algebraMap R Λ r)) = algebraMap R Λ r :=
      RingHom.congr_fun hτ1 (algebraMap R Λ r)
    calc (τ.comp Algebra.TensorProduct.includeRight.toRingHom) (algebraMap R B r)
        = τ ((Algebra.TensorProduct.includeRight : B →ₐ[R] Λ ⊗[R] B)
            (algebraMap R B r)) := rfl
      _ = τ (algebraMap Λ (Λ ⊗[R] B) (algebraMap R Λ r)) := by rw [h1, h2]
      _ = algebraMap R Λ r := h3
  · refine RingHom.ext fun β => ?_
    have h1 : χΛ (τ ((Algebra.TensorProduct.includeRight : B →ₐ[R] Λ ⊗[R] B) β)) =
        χT.toRingHom ((Algebra.TensorProduct.includeRight : B →ₐ[R] Λ ⊗[R] B) β) :=
      RingHom.congr_fun hτ2 _
    have h4 : (Algebra.TensorProduct.includeRight : B →ₐ[R] Λ ⊗[R] B) β =
        (1 : Λ) ⊗ₜ[R] β :=
      Algebra.TensorProduct.includeRight_apply β
    have h2 : χT.toRingHom ((1 : Λ) ⊗ₜ[R] β) = χΛ 1 * χB β := by
      rw [hχT]
      exact Algebra.TensorProduct.lift_tmul _ _ _ 1 β
    have h3 : χΛ (1 : Λ) * χB β = χB β := by rw [map_one, one_mul]
    calc (χΛ.comp (τ.comp Algebra.TensorProduct.includeRight.toRingHom)) β
        = χΛ (τ ((Algebra.TensorProduct.includeRight : B →ₐ[R] Λ ⊗[R] B) β)) := rfl
      _ = χT.toRingHom ((Algebra.TensorProduct.includeRight : B →ₐ[R] Λ ⊗[R] B) β) := h1
      _ = χT.toRingHom ((1 : Λ) ⊗ₜ[R] β) := by rw [h4]
      _ = χΛ 1 * χB β := h2
      _ = χB β := h3

end EtaleRetraction

namespace AlgebraicGeometry.Scheme.Etale

/-!
### Affine helpers

Global sections of the conjugation of `Spec` of a ring map by the `isoSpec`
isomorphisms recover the ring map. The two `isoSpec` lemmas are copies of the private
helpers of `Proetale.Etale.StrictLocalization`.
-/

/-- The top-level sections of the inverse of `isoSpec` are the inverse of `ΓSpecIso`. -/
private lemma isoSpec_inv_appTop (W : Scheme.{u}) [IsAffine W] :
    W.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(W, ⊤)).inv := by
  rw [← Iso.comp_hom_eq_id (Scheme.ΓSpecIso Γ(W, ⊤)), ← Scheme.toSpecΓ_appTop,
    ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop]

/-- Global sections of the conjugation of `Spec` of a ring map by the `isoSpec`
isomorphisms recover the ring map. -/
private lemma isoSpec_hom_specMap_isoSpec_inv_appTop {W V : Scheme.{u}} [IsAffine W]
    [IsAffine V] (q : Γ(V, ⊤) ⟶ Γ(W, ⊤)) :
    (W.isoSpec.hom ≫ Spec.map q ≫ V.isoSpec.inv).appTop = q := by
  have e1 : (Spec.map q).appTop =
      (Scheme.ΓSpecIso Γ(V, ⊤)).hom ≫ q ≫ (Scheme.ΓSpecIso Γ(W, ⊤)).inv := by
    rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have e2 : W.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(W, ⊤)).hom := by
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, isoSpec_inv_appTop, e1, e2]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X) (p₁ : (geometricPoint x).fiber.Elements)
  {ι : Type u} (es : ι → Γ(((Over.pullback @Etale ⊤ f).obj p₁.1).left, ⊤)) (i : ι)
  {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
  (σ : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))
  (y : Spec (CommRingCat.of Ω') ⟶ Y) (hy : y ≫ f = σ ≫ x)
  (χ : fiberSections f x →+* Ω')
  (heval : fiberSectionsToStrictLocalization f x σ y hy ≫ strictLocalizationEval y =
    CommRingCat.ofHom χ)
  (hi : χ ((toFiberSections f x p₁).hom (es i)) ≠ 0)

/-!
### Morphisms of étale neighbourhoods of `y` into summands

A morphism from an étale neighbourhood of `y` to a summand is an étale morphism of
schemes, and evaluation of functions at the point of the neighbourhood computes the
evaluation character of the summand sections on the restricted functions.
-/

/-- The underlying scheme morphism of a morphism of étale neighbourhoods of `y` into a
summand is étale: both schemes are étale over `Y`. -/
private lemma etale_elements_hom_left (g₂ : SummandIndex x p₁)
    {V' : (geometricPoint y).fiber.Elements}
    (b : V' ⟶ (summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂) :
    Etale b.val.left := by
  have h : Etale (b.val.left ≫
      ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂).1.hom) := by
    rw [MorphismProperty.Over.w b.val]
    exact V'.1.prop
  exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _
    ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂).1.hom
    ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂).1.prop h

/-- Evaluation at the point of an étale neighbourhood of `y` mapping to a summand
computes the evaluation character of the summand sections on the germs of restricted
functions: the point of the neighbourhood is mapped to the lifted point of the
summand. -/
private lemma eval_elements_hom_appTop (g₂ : SummandIndex x p₁)
    {V' : (geometricPoint y).fiber.Elements}
    (b : V' ⟶ (summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂)
    (r : Γ((summand f x p₁ es i g₂).left, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom
        ((V'.2.val.appTop).hom ((b.val.left.appTop).hom r)) =
      summandSectionsEval f x p₁ es i σ y hy χ heval hi
        ((toSummandSections f x p₁ es i σ y hy χ heval hi g₂).hom r) := by
  have hbp : V'.2.val ≫ b.val.left =
      (summandPoint f x p₁ es i σ y hy χ heval hi g₂).val :=
    congrArg Subtype.val b.property
  have h2 := congrArg (fun t => (Scheme.Hom.appTop t).hom r) hbp
  have h3 := congrArg (fun t => CommRingCat.Hom.hom t r)
    (Scheme.Hom.comp_appTop V'.2.val b.val.left)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
  have h4 : (V'.2.val.appTop).hom ((b.val.left.appTop).hom r) =
      (((summandPoint f x p₁ es i σ y hy χ heval hi g₂).val).appTop).hom r :=
    h3.symm.trans h2
  rw [h4]
  exact (eval_toSummandSections f x p₁ es i σ y hy χ heval hi g₂ r).symm

/-!
### Descent of homomorphisms out of the summand sections colimit

A homomorphism from a finitely presented algebra over the sections of a base summand to
the summand sections colimit descends to the sections of a finer summand: the summand
sections are the filtered colimit of the sections over the slice of stages refining the
base stage, since the forgetful functor of the slice is initial.
-/

/-- The restriction maps from the sections of the summand at the base stage `g₂`, as a
transformation from the constant functor to the summand sections diagram restricted to
the stages over `g₂`. -/
private noncomputable def overDiagramTransform (g₂ : SummandIndex x p₁) :
    (Functor.const (Over g₂)ᵒᵖ).obj (Γ((summand f x p₁ es i g₂).left, ⊤)) ⟶
      (Over.forget g₂).op ⋙ summandSectionsDiagram f x p₁ es i σ y hy χ heval hi where
  app j := (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map (op j.unop.hom)
  naturality j j' t := by
    have h1 : (Over.forget g₂).map t.unop ≫ j.unop.hom = j'.unop.hom := Over.w t.unop
    have h2 : (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map
          (op j.unop.hom) ≫
          (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map
            ((Over.forget g₂).map t.unop).op =
        (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map (op j'.unop.hom) := by
      rw [← Functor.map_comp]
      exact congrArg (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map
        (congrArg Quiver.Hom.op h1)
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
      Functor.comp_map, Functor.op_obj, Functor.op_map]
    exact h2.symm

/-- **Descent of homomorphisms to a stage of the summand system**: a homomorphism from
a finitely presented algebra over the sections of the summand at a stage `g₂` to the
summand sections colimit factors through the sections of the summand at a finer
stage. -/
private lemma exists_comp_toSummandSections_eq (g₂ : SummandIndex x p₁)
    {B : CommRingCat.{u}} (rmap : Γ((summand f x p₁ es i g₂).left, ⊤) ⟶ B)
    (hfp : rmap.hom.FinitePresentation)
    (s : B ⟶ summandSections f x p₁ es i σ y hy χ heval hi)
    (hs : rmap ≫ s = toSummandSections f x p₁ es i σ y hy χ heval hi g₂) :
    ∃ (g₃ : SummandIndex x p₁) (t₃ : g₃ ⟶ g₂)
      (q : B ⟶ Γ((summand f x p₁ es i g₃).left, ⊤)),
      rmap ≫ q = (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map (op t₃) ∧
      s = q ≫ toSummandSections f x p₁ es i σ y hy χ heval hi g₃ := by
  haveI : PreservesColimit ((Over.forget g₂).op ⋙
      summandSectionsDiagram f x p₁ es i σ y hy χ heval hi)
      (CategoryTheory.forget CommRingCat.{u}) := inferInstance
  have hc : IsColimit ((colimit.cocone
      (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi)).whisker
      (Over.forget g₂).op) :=
    (Functor.Final.isColimitWhiskerEquiv (Over.forget g₂).op _).symm
      (colimit.isColimit (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi))
  have hg : ∀ j : (Over g₂)ᵒᵖ, rmap ≫ s =
      (overDiagramTransform f x p₁ es i σ y hy χ heval hi g₂).app j ≫
        ((colimit.cocone (summandSectionsDiagram f x p₁ es i σ y hy χ
          heval hi)).whisker (Over.forget g₂).op).ι.app j := by
    intro j
    rw [hs]
    exact (toSummandSections_w f x p₁ es i σ y hy χ heval hi j.unop.hom).symm
  obtain ⟨j, q, hq1, hq2⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (Γ((summand f x p₁ es i g₂).left, ⊤))
    ((Over.forget g₂).op ⋙ summandSectionsDiagram f x p₁ es i σ y hy χ heval hi)
    (overDiagramTransform f x p₁ es i σ y hy χ heval hi g₂) rmap
    ((colimit.cocone (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi)).whisker
      (Over.forget g₂).op)
    hc hfp s hg
  exact ⟨j.unop.left, j.unop.hom, q, hq1, hq2⟩

section Local

variable [IsFinite f] [Fintype ι]
  (m : MaximalSpectrum (fiberSections f x))
  (hker : RingHom.ker χ = m.asIdeal)
  (hnot : (toFiberSections f x p₁).hom (es i) ∉ m.asIdeal)
  (hmem : ∀ m' : MaximalSpectrum (fiberSections f x), m' ≠ m →
    (toFiberSections f x p₁).hom (es i) ∈ m'.asIdeal)

/-!
### Dominance of the summand system
-/

include hker hnot hmem in
/-- **Factorization of an affine neighbourhood through a finer stage**: for an affine
étale neighbourhood `V'` of `y` mapping to the summand at a base stage `g₂`, the
functions of `V'` map to the functions of the summand at some finer stage `g₃`,
compatibly with the restriction maps and with evaluation at the points. The
homomorphism is obtained by base changing the étale ring map of `V'` over the summand
at `g₂` to the strictly henselian summand sections, retracting, and descending the
resulting map to a finite stage of the colimit by finite presentation. -/
private lemma exists_stage_factorization (hes : CompleteOrthogonalIdempotents es)
    (g₂ : SummandIndex x p₁) {V' : (geometricPoint y).fiber.Elements}
    [IsAffine V'.1.left]
    (b : V' ⟶ (summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂) :
    ∃ (g₃ : SummandIndex x p₁) (t₃ : g₃ ⟶ g₂)
      (q : Γ(V'.1.left, ⊤) ⟶ Γ((summand f x p₁ es i g₃).left, ⊤)),
      b.val.left.appTop ≫ q =
        (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map (op t₃) ∧
      ∀ β : Γ(V'.1.left, ⊤),
        summandSectionsEval f x p₁ es i σ y hy χ heval hi
            ((toSummandSections f x p₁ es i σ y hy χ heval hi g₃).hom (q.hom β)) =
          (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom ((V'.2.val.appTop).hom β) := by
  haveI hSaff : IsAffine
      ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂).1.left :=
    inferInstanceAs (IsAffine (summand f x p₁ es i g₂).left)
  haveI hloc : IsLocalRing (summandSections f x p₁ es i σ y hy χ heval hi) :=
    isLocalRing_summandSections f x p₁ es i σ y hy χ heval hi m hnot hmem hes
  have hbet : Etale b.val.left :=
    etale_elements_hom_left f x p₁ es i σ y hy χ heval hi g₂ b
  have hret : RingHom.Etale (b.val.left.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp hbet
  have hfp : (b.val.left.appTop).hom.FinitePresentation :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hret).2.2
  letI : Algebra Γ((summand f x p₁ es i g₂).left, ⊤) Γ(V'.1.left, ⊤) :=
    (b.val.left.appTop).hom.toAlgebra
  letI : Algebra Γ((summand f x p₁ es i g₂).left, ⊤)
      (summandSections f x p₁ es i σ y hy χ heval hi) :=
    (toSummandSections f x p₁ es i σ y hy χ heval hi g₂).hom.toAlgebra
  haveI hBet : Algebra.Etale Γ((summand f x p₁ es i g₂).left, ⊤) Γ(V'.1.left, ⊤) :=
    hret.toAlgebra
  obtain ⟨σB, hσ1, hσ2⟩ := exists_comp_eq_of_etale hBet
    (summandSectionsEval f x p₁ es i σ y hy χ heval hi)
    (((Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom).comp ((V'.2.val.appTop).hom))
    (fun r => eval_elements_hom_appTop f x p₁ es i σ y hy χ heval hi g₂ b r)
    (ker_summandSectionsEval f x p₁ es i σ y hy χ heval hi m hker hnot hmem hes)
    (fun T _ _ hT χT hkT => exists_retraction_of_etale_summandSections f x p₁ es i σ y
      hy χ heval hi m hnot hmem hes T hT χT hkT)
  have hs : b.val.left.appTop ≫ CommRingCat.ofHom σB =
      toSummandSections f x p₁ es i σ y hy χ heval hi g₂ := by
    ext r
    exact RingHom.congr_fun hσ1 r
  obtain ⟨g₃, t₃, q, hq1, hq2⟩ := exists_comp_toSummandSections_eq f x p₁ es i σ y hy χ
    heval hi g₂ (b.val.left.appTop) hfp (CommRingCat.ofHom σB) hs
  refine ⟨g₃, t₃, q, hq1, fun β => ?_⟩
  have h1 : (toSummandSections f x p₁ es i σ y hy χ heval hi g₃).hom (q.hom β) =
      σB β := by
    have h2 := congrArg (fun t => CommRingCat.Hom.hom t β) hq2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h2
    exact h2.symm
  rw [h1]
  exact RingHom.congr_fun hσ2 β

omit [Fintype ι] in
/-- **The elements morphism associated to a stage factorization**: a factorization of
the functions of an affine étale neighbourhood `V'` of `y` through the sections of a
finer summand which is compatible with the restriction maps and with evaluation at the
points induces a morphism of étale neighbourhoods of `y` from the finer summand to
`V'`. -/
private lemma nonempty_elements_hom_of_factorization (g₂ : SummandIndex x p₁)
    {V' : (geometricPoint y).fiber.Elements} [IsAffine V'.1.left]
    (b : V' ⟶ (summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂)
    (g₃ : SummandIndex x p₁) (t₃ : g₃ ⟶ g₂)
    (q : Γ(V'.1.left, ⊤) ⟶ Γ((summand f x p₁ es i g₃).left, ⊤))
    (hq1 : b.val.left.appTop ≫ q =
      (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map (op t₃))
    (hq2 : ∀ β : Γ(V'.1.left, ⊤),
      summandSectionsEval f x p₁ es i σ y hy χ heval hi
          ((toSummandSections f x p₁ es i σ y hy χ heval hi g₃).hom (q.hom β)) =
        (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom ((V'.2.val.appTop).hom β)) :
    Nonempty ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₃ ⟶ V') := by
  haveI hSaff : IsAffine
      ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂).1.left :=
    inferInstanceAs (IsAffine (summand f x p₁ es i g₂).left)
  have hψTop : ((summand f x p₁ es i g₃).left.isoSpec.hom ≫ Spec.map q ≫
      V'.1.left.isoSpec.inv).appTop = q :=
    isoSpec_hom_specMap_isoSpec_inv_appTop q
  -- the triangle over the summand at the base stage
  have htri : ((summand f x p₁ es i g₃).left.isoSpec.hom ≫ Spec.map q ≫
      V'.1.left.isoSpec.inv) ≫ b.val.left = (summandMap f x p₁ es i t₃).left := by
    apply ext_of_isAffine
    have h1 : (((summand f x p₁ es i g₃).left.isoSpec.hom ≫ Spec.map q ≫
        V'.1.left.isoSpec.inv) ≫ b.val.left).appTop =
        b.val.left.appTop ≫ ((summand f x p₁ es i g₃).left.isoSpec.hom ≫ Spec.map q ≫
          V'.1.left.isoSpec.inv).appTop :=
      Scheme.Hom.comp_appTop _ _
    have h2 : (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map (op t₃) =
        ((summandMap f x p₁ es i t₃).left).appTop :=
      Scheme.Γ_map_op ((summandMap f x p₁ es i t₃).left)
    rw [h1, hψTop, hq1, h2]
  -- the triangle over `Y`
  have hover : ((summand f x p₁ es i g₃).left.isoSpec.hom ≫ Spec.map q ≫
      V'.1.left.isoSpec.inv) ≫ V'.1.hom = (summand f x p₁ es i g₃).hom := by
    have h5 : b.val.left ≫
        ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂).1.hom = V'.1.hom :=
      MorphismProperty.Over.w b.val
    have h6 : (summandMap f x p₁ es i t₃).left ≫ (summand f x p₁ es i g₂).hom =
        (summand f x p₁ es i g₃).hom :=
      MorphismProperty.Over.w (summandMap f x p₁ es i t₃)
    rw [← h5, ← Category.assoc, htri]
    exact h6
  -- compatibility with the points
  have hpt : (summandPoint f x p₁ es i σ y hy χ heval hi g₃).val ≫
      ((summand f x p₁ es i g₃).left.isoSpec.hom ≫ Spec.map q ≫
        V'.1.left.isoSpec.inv) = V'.2.val := by
    apply ext_of_isAffine
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom]
    have hchar : (summandPoint f x p₁ es i σ y hy χ heval hi g₃).val.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom =
        CommRingCat.ofHom ((summandSectionsEval f x p₁ es i σ y hy χ heval hi).comp
          (toSummandSections f x p₁ es i σ y hy χ heval hi g₃).hom) := by
      ext r
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      exact (eval_toSummandSections f x p₁ es i σ y hy χ heval hi g₃ r).symm
    have h1 : ((summandPoint f x p₁ es i σ y hy χ heval hi g₃).val ≫
        ((summand f x p₁ es i g₃).left.isoSpec.hom ≫ Spec.map q ≫
          V'.1.left.isoSpec.inv)).appTop =
        ((summand f x p₁ es i g₃).left.isoSpec.hom ≫ Spec.map q ≫
          V'.1.left.isoSpec.inv).appTop ≫
          (summandPoint f x p₁ es i σ y hy χ heval hi g₃).val.appTop :=
      Scheme.Hom.comp_appTop _ _
    rw [h1, hψTop, Category.assoc, hchar]
    ext β
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact hq2 β
  exact ⟨⟨MorphismProperty.Over.homMk ((summand f x p₁ es i g₃).left.isoSpec.hom ≫
    Spec.map q ≫ V'.1.left.isoSpec.inv) hover trivial, Subtype.ext (by exact hpt)⟩⟩

include hker hnot hmem in
/-- **Dominance of the summand system**: every étale neighbourhood of `y` receives a
morphism from a split summand. Choose an affine common refinement of the neighbourhood
and a base summand; its ring of functions is étale over the sections of the base
summand, hence base changes to an étale algebra over the strictly henselian summand
sections, which retracts back compatibly with the evaluation characters; the retraction
descends to the sections of a finer summand by finite presentation, giving a morphism
of étale neighbourhoods from the finer summand to the refinement. -/
theorem exists_summandFunctor_hom (hes : CompleteOrthogonalIdempotents es)
    (d : (geometricPoint y).fiber.Elements) :
    ∃ g : SummandIndex x p₁,
      Nonempty ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g ⟶ d) := by
  obtain ⟨g₂⟩ : Nonempty (SummandIndex x p₁) := IsCofiltered.nonempty
  -- an affine common refinement of `d` and the summand at `g₂`
  obtain ⟨w⟩ : Nonempty (CostructuredArrow
      (CategoryOfElements.pre (AffineEtale.Spec Y) (geometricPoint y).fiber) d) := by
    haveI := Functor.Initial.out
      (F := CategoryOfElements.pre (AffineEtale.Spec Y) (geometricPoint y).fiber) d
    infer_instance
  obtain ⟨w₂⟩ : Nonempty (CostructuredArrow
      (CategoryOfElements.pre (AffineEtale.Spec Y) (geometricPoint y).fiber)
      ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂)) := by
    haveI := Functor.Initial.out
      (F := CategoryOfElements.pre (AffineEtale.Spec Y) (geometricPoint y).fiber)
      ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂)
    infer_instance
  set j₂ := IsCofiltered.min w.left w₂.left with hj₂
  set V' : (geometricPoint y).fiber.Elements :=
    (CategoryOfElements.pre (AffineEtale.Spec Y) (geometricPoint y).fiber).obj j₂
    with hV'
  haveI hV'aff : IsAffine V'.1.left := inferInstanceAs (IsAffine (Spec (unop j₂.1.left)))
  set a : V' ⟶ d := (CategoryOfElements.pre (AffineEtale.Spec Y)
    (geometricPoint y).fiber).map (IsCofiltered.minToLeft w.left w₂.left) ≫ w.hom
    with ha
  set b : V' ⟶ (summandFunctor f x p₁ es i σ y hy χ heval hi).obj g₂ :=
    (CategoryOfElements.pre (AffineEtale.Spec Y) (geometricPoint y).fiber).map
      (IsCofiltered.minToRight w.left w₂.left) ≫ w₂.hom with hb
  -- factor the refinement through a finer summand and map it to `d`
  obtain ⟨g₃, t₃, q, hq1, hq2⟩ := exists_stage_factorization f x p₁ es i σ y hy χ heval
    hi m hker hnot hmem hes g₂ b
  obtain ⟨e⟩ := nonempty_elements_hom_of_factorization f x p₁ es i σ y hy χ heval hi
    g₂ b g₃ t₃ q hq1 hq2
  exact ⟨g₃, ⟨e ≫ a⟩⟩

/-!
### Initiality of the summand system and the stage C closure
-/

include hker hnot hmem in
/-- **The summand system is initial among the étale neighbourhoods of `y`**: it
dominates every neighbourhood (`exists_summandFunctor_hom`) and equalizes every pair of
morphisms to a neighbourhood (`exists_summandFunctor_map_comp_eq`). -/
theorem initial_summandFunctor (hes : CompleteOrthogonalIdempotents es) :
    (summandFunctor f x p₁ es i σ y hy χ heval hi).Initial :=
  Functor.initial_of_exists_of_isCofiltered _
    (exists_summandFunctor_hom f x p₁ es i σ y hy χ heval hi m hker hnot hmem hes)
    (fun s s' => exists_summandFunctor_map_comp_eq f x p₁ es i σ y hy χ heval hi m
      hker hnot hmem hes s s')

include hker hnot hmem in
/-- **The germ comparison of the summand sections is an isomorphism**: the summand
system is initial among the étale neighbourhoods of `y`, so the colimit restriction to
the summand sections compares isomorphically to the strict localization of `Y` at
`y`. -/
theorem isIso_summandSectionsToStrictLocalization
    (hes : CompleteOrthogonalIdempotents es) :
    IsIso (summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi) := by
  haveI : (summandFunctor f x p₁ es i σ y hy χ heval hi).Initial :=
    initial_summandFunctor f x p₁ es i σ y hy χ heval hi m hker hnot hmem hes
  exact inferInstanceAs (IsIso (colimit.pre (strictLocalizationDiagram y)
    (summandFunctor f x p₁ es i σ y hy χ heval hi).op))

include hi hker hnot hmem in
/-- **The stage C closure of blueprint `lemma:pbc-finite`**: the comparison map from
the localization of the fiber sections at the maximal ideal `m` to the strict
localization of `Y` at the lifted geometric point `y` is bijective. It factors as the
identification of the localization with the summand sections followed by the germ
comparison of the summand sections, which is an isomorphism by the cofinality of the
summand system. -/
theorem bijective_localizationAtPrimeToStrictLocalization
    (hes : CompleteOrthogonalIdempotents es) :
    Function.Bijective
      (localizationAtPrimeToStrictLocalization f x σ y hy χ m heval hker) := by
  haveI hiso : IsIso (summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval
      hi) :=
    isIso_summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi m hker
      hnot hmem hes
  have h1 : Function.Bijective
      ⇑(summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi).hom :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso _
  have h2 : Function.Bijective
      ⇑(localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot
        hmem hes) :=
    (localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot hmem
      hes).bijective
  have hfun : ⇑(localizationAtPrimeToStrictLocalization f x σ y hy χ m heval hker) =
      ⇑(summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi).hom ∘
        ⇑(localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot
          hmem hes) := by
    funext z
    exact (summandSectionsToStrictLocalization_localizationAtPrimeToSummandSections f
      x p₁ es i σ y hy χ heval hi m hker hnot hmem hes z).symm
  rw [hfun]
  exact h1.comp h2

end Local

end AlgebraicGeometry.Scheme.Etale
