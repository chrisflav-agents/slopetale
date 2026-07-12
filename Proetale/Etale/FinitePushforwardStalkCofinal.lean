/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.FinitePushforwardStalkIso

/-!
# The strict localization of the fiber of a finite morphism at a lifted geometric point

This file continues the program towards the stalk formula for pushforwards along finite
morphisms (blueprint `lemma:pbc-finite`), building on
`Proetale.Etale.FinitePushforwardStalk` and `Proetale.Etale.FinitePushforwardStalkIso`.

Let `f : Y ⟶ X` be a morphism of schemes, `x : Spec Ω ⟶ X` a geometric point and
`y : Spec Ω' ⟶ Y` a geometric point of `Y` lying over `x` via a morphism
`ε : Spec Ω' ⟶ Spec Ω` of spectra of separably closed fields.

## The comparison map from the fiber sections to the strict localization at a lift

- `AlgebraicGeometry.Scheme.Etale.pullbackElements`: base change along `f` sends étale
  neighbourhoods of `x` to étale neighbourhoods of `y`, as a functor between the
  categories of elements of the fiber functors.
- `AlgebraicGeometry.Scheme.Etale.fiberSectionsToStrictLocalization`: the induced
  homomorphism `S = colim Γ(U ×_X Y) ⟶ 𝒪^sh_{Y, y}` from the fiber sections over the
  strict localization of `X` at `x` to the strict localization of `Y` at `y`, given on
  each étale neighbourhood stage `(U, u)` of `x` by the germ map of the étale
  neighbourhood `(U ×_X Y, (ε ≫ u, y))` of `y`.

## Evaluation compatibility at the lifts associated to characters (for finite `f`)

For a maximal ideal `m` of the fiber sections with character `χ` (`ker χ = m`,
compatibly with evaluation at `x` — as produced by
`AlgebraicGeometry.Scheme.Etale.exists_ringHom_ker_eq`) and the associated lift
`y = liftOfRingHom f x p₀ hp₀ χ`:

- `AlgebraicGeometry.Scheme.Etale.fiberSectionsToStrictLocalization_liftOfRingHom_eval`:
  evaluation at `y` of the germ of a fiber section is its value under `χ`, i.e.
  `strictLocalizationEval y ∘ θ = χ` for the comparison map `θ`. The proof identifies,
  on the initial family of affine étale neighbourhood stages refining `p₀`, the lifted
  point of `U ×_X Y` with the point associated to the restricted character.

## Consequences: the induced map on the localization at `m`

- `AlgebraicGeometry.Scheme.Etale.isUnit_fiberSectionsToStrictLocalization` /
  `AlgebraicGeometry.Scheme.Etale.fiberSectionsToStrictLocalization_mem_maximalIdeal_iff`:
  `θ` inverts the elements outside `m` and reflects the maximal ideal.
- `AlgebraicGeometry.Scheme.Etale.fiberSectionsToStrictLocalization_eq_zero_of_isIdempotentElem`:
  `θ` kills the idempotents of the complementary factors of the splitting of the fiber
  sections.
- `AlgebraicGeometry.Scheme.Etale.localizationAtPrimeToStrictLocalization`: the induced
  local homomorphism `S_m = Localization.AtPrime m ⟶ 𝒪^sh_{Y, y}`
  (`isLocalHom_localizationAtPrimeToStrictLocalization`), through which `θ` factors.
- `AlgebraicGeometry.Scheme.Etale.exists_ringHom_fiberSectionsToStrictLocalization_eval`:
  the packaged existence statement over the algebraic closure `Ω' = AlgebraicClosure Ω`:
  every maximal ideal `m` of the fiber sections admits a character `χ` with kernel `m`
  whose lift `y` satisfies the evaluation compatibility, so that all of the above
  applies.

## Remaining steps (blueprint `lemma:pbc-finite`, stage C/D)

The remaining content of stage C is that `localizationAtPrimeToStrictLocalization` is
bijective. Injectivity and surjectivity both reduce to the cofinality of the
base-changed neighbourhoods `(U ×_X Y, (ε ≫ u, y))` (equivalently of their split
summands) among all étale neighbourhoods of `y`, which in turn rests on the strict
henselianity of `S_m` (Stacks 04GG (10), 04GH): a finite algebra over the strictly
henselian ring `𝒪^sh_{X, x}` splits into strictly henselian local factors. The
henselianity of the local factors (Stacks 04GH) is not yet formalized. Stage D then
assembles `AlgebraicGeometry.Scheme.Etale.pushforwardStalkToPiStalk` being an
isomorphism from additivity, the commutation of filtered colimits with finite products
and the cofinality above.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X)
  {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
  (ε : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))
  (y : Spec (CommRingCat.of Ω') ⟶ Y) (hy : y ≫ f = ε ≫ x)

/-!
### Base change of étale neighbourhoods, as a functor on categories of elements

A geometric point `y` of `Y` over `x` lifts every étale neighbourhood `(U, u)` of `x`
to the étale neighbourhood `(U ×_X Y, (ε ≫ u, y))` of `y`
(`AlgebraicGeometry.Scheme.Etale.pullbackFiberLift`). The lifts are compatible with the
transition maps, so they assemble into a functor between the categories of elements of
the fiber functors.
-/

/-- **Base change of étale neighbourhoods**: the functor sending an étale neighbourhood
`(U, u)` of `x` to the étale neighbourhood `(U ×_X Y, (ε ≫ u, y))` of a geometric point
`y` of `Y` lying over `x`. -/
noncomputable def pullbackElements :
    (geometricPoint x).fiber.Elements ⥤ (geometricPoint y).fiber.Elements where
  obj p := ⟨(Over.pullback @Etale ⊤ f).obj p.1, pullbackFiberLift f x ε y hy p.1 p.2⟩
  map {p q} g := ⟨(Over.pullback @Etale ⊤ f).map g.val,
    (fiber_map_pullbackFiberLift f x ε y hy g.val p.2).trans
      (congrArg (pullbackFiberLift f x ε y hy q.1) g.property)⟩
  map_id p := CategoryOfElements.ext _ _ _ ((Over.pullback @Etale ⊤ f).map_id p.1)
  map_comp g h := CategoryOfElements.ext _ _ _
    ((Over.pullback @Etale ⊤ f).map_comp g.val h.val)

@[simp]
lemma pullbackElements_obj_fst (p : (geometricPoint x).fiber.Elements) :
    ((pullbackElements f x ε y hy).obj p).1 = (Over.pullback @Etale ⊤ f).obj p.1 :=
  rfl

@[simp]
lemma pullbackElements_obj_snd (p : (geometricPoint x).fiber.Elements) :
    ((pullbackElements f x ε y hy).obj p).2 = pullbackFiberLift f x ε y hy p.1 p.2 :=
  rfl

/-!
### The comparison map from the fiber sections to the strict localization at a lift
-/

/-- The cocone on the fiber sections diagram of `x` with point the strict localization
of `Y` at a lift `y` of `x`: the leg at the étale neighbourhood stage `(U, u)` of `x`
is the germ map of the étale neighbourhood `(U ×_X Y, (ε ≫ u, y))` of `y`. -/
noncomputable def fiberSectionsToStrictLocalizationCocone :
    Cocone (fiberSectionsDiagram f x) where
  pt := strictLocalization y
  ι :=
    { app p := toStrictLocalization y ((pullbackElements f x ε y hy).obj p.unop)
      naturality p q g := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact toStrictLocalization_w y ((pullbackElements f x ε y hy).map g.unop) }

/-- **The comparison map from the fiber sections to the strict localization at a
lift**: the homomorphism `colim_{(U, u)} Γ(U ×_X Y) ⟶ 𝒪^sh_{Y, y}` given on each étale
neighbourhood stage of `x` by the germ map of the base-changed étale neighbourhood of
`y`. -/
noncomputable def fiberSectionsToStrictLocalization :
    fiberSections f x ⟶ strictLocalization y :=
  colimit.desc (fiberSectionsDiagram f x)
    (fiberSectionsToStrictLocalizationCocone f x ε y hy)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toFiberSections_fiberSectionsToStrictLocalization
    (p : (geometricPoint x).fiber.Elements) :
    toFiberSections f x p ≫ fiberSectionsToStrictLocalization f x ε y hy =
      toStrictLocalization y ((pullbackElements f x ε y hy).obj p) :=
  colimit.ι_desc _ _

/-!
### Evaluation compatibility at the lifts associated to characters

For the lift `y = liftOfRingHom f x p₀ hp₀ χ` associated to a character `χ` of the
fiber sections extending the evaluation of the strict localization, evaluation at `y`
of the germ of a fiber section recovers its value under `χ`. The proof identifies, on
the initial family of affine étale neighbourhood stages refining `p₀`, the lifted point
of `U ×_X Y` with the point `Spec Ω' ⟶ Spec Γ(U ×_X Y) ≅ U ×_X Y` associated to the
restriction of `χ` to the stage.
-/

section Eval

/-- The top-level sections of the inverse of `isoSpec` are the inverse of `ΓSpecIso`. -/
private lemma isoSpec_inv_appTop'' (Z : Scheme.{u}) [IsAffine Z] :
    Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
  rw [← Iso.comp_hom_eq_id (Scheme.ΓSpecIso Γ(Z, ⊤)), ← Scheme.toSpecΓ_appTop,
    ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop]

/-- Global sections of a morphism to an affine scheme that factors through `Spec` of a
homomorphism `φ` recover `φ`. -/
private lemma Γ_map_specMap_isoSpec_inv {R : CommRingCat.{u}} (Z : Scheme.{u}) [IsAffine Z]
    (φ : Γ(Z, ⊤) ⟶ R) :
    Scheme.Γ.map (Spec.map φ ≫ Z.isoSpec.inv).op ≫ (Scheme.ΓSpecIso R).hom = φ := by
  have e1 : (Spec.map φ).appTop =
      (Scheme.ΓSpecIso Γ(Z, ⊤)).hom ≫ φ ≫ (Scheme.ΓSpecIso R).inv := by
    rw [← ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Scheme.Γ_map_op, Scheme.Hom.comp_appTop, isoSpec_inv_appTop'', e1]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

variable [IsFinite f]
variable {ψ : Ω →+* Ω'} (χ : fiberSections f x →+* Ω')

omit [IsSepClosed Ω'] [IsFinite f] in
/-- The point of the fiber over an affine étale neighbourhood stage associated to the
restriction of a character `χ` of the fiber sections lies over the geometric point
`Spec Ω' ⟶ Spec Ω ⟶ X`, provided `χ` extends the evaluation of the strict
localization. This is the first-projection component of the identification of the
lifted point with the point associated to `χ`. -/
private lemma specMap_isoSpec_inv_fst
    (hχ : χ.comp (strictLocalizationToFiberSections f x).hom =
      ψ.comp (strictLocalizationEval x).hom)
    (p : (geometricPoint x).fiber.Elements) [IsAffine p.1.left]
    [IsAffine (pullback p.1.hom f)] :
    Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)) ≫
        (pullback p.1.hom f).isoSpec.inv ≫ pullback.fst p.1.hom f =
      Spec.map (CommRingCat.ofHom ψ) ≫ p.2.val := by
  have h1 : strictLocalizationToFiberSections f x ≫ CommRingCat.ofHom χ =
      strictLocalizationEval x ≫ CommRingCat.ofHom ψ := by
    ext a
    exact RingHom.congr_fun hχ a
  have hring : (pullback.fst p.1.hom f).appTop ≫
      CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom) =
      Scheme.Γ.map p.2.val.op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫
        CommRingCat.ofHom ψ := by
    calc (pullback.fst p.1.hom f).appTop ≫
          CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)
        = (Scheme.Γ.map (pullback.fst p.1.hom f).op ≫ toFiberSections f x p) ≫
            CommRingCat.ofHom χ := rfl
      _ = (toStrictLocalization x p ≫ strictLocalizationToFiberSections f x) ≫
            CommRingCat.ofHom χ := by
            rw [toStrictLocalization_strictLocalizationToFiberSections]
      _ = toStrictLocalization x p ≫ strictLocalizationEval x ≫ CommRingCat.ofHom ψ := by
            rw [Category.assoc, h1]
      _ = Scheme.Γ.map p.2.val.op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫
            CommRingCat.ofHom ψ := by
            rw [← Category.assoc, toStrictLocalization_strictLocalizationEval,
              Category.assoc]
  haveI : IsAffine ((𝟭 Scheme.{u}).obj p.1.left) := ‹IsAffine p.1.left›
  apply ext_of_isAffine
  have e1 : (Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom))).appTop =
      (Scheme.ΓSpecIso Γ(pullback p.1.hom f, ⊤)).hom ≫
        CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom) ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω')).inv := by
    rw [← ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have e2 : (Spec.map (CommRingCat.ofHom ψ)).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom ψ ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω')).inv := by
    rw [← ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    isoSpec_inv_appTop'', e1, e2]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, reassoc_of% hring]
  rfl

variable (p₀ : (geometricPoint x).fiber.Elements) (hp₀ : IsAffine p₀.1.left)
  (hχ : χ.comp (strictLocalizationToFiberSections f x).hom =
    ψ.comp (strictLocalizationEval x).hom)

/-- On an affine étale neighbourhood stage `p` refining the base stage `p₀`, the lift
of the geometric point to the fiber `U ×_X Y` is the point associated to the
restriction of the character `χ` to the stage. -/
private lemma pullbackFiberLift_liftOfRingHom_val
    (p : (geometricPoint x).fiber.Elements) [IsAffine p.1.left]
    [IsAffine (pullback p.1.hom f)] (g₀ : p ⟶ p₀) :
    (pullbackFiberLift f x (Spec.map (CommRingCat.ofHom ψ)) (liftOfRingHom f x p₀ hp₀ χ)
        (liftOfRingHom_comp f x p₀ hp₀ χ hχ) p.1 p.2).val =
      Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)) ≫
        (pullback p.1.hom f).isoSpec.inv := by
  haveI := hp₀
  haveI : IsAffine ((𝟭 Scheme.{u}).obj p₀.1.left) := hp₀
  haveI : IsAffine (pullback p₀.1.hom f) := inferInstance
  symm
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackFiberLift_val_fst]
    exact specMap_isoSpec_inv_fst f x χ hχ p
  · rw [Category.assoc, pullbackFiberLift_val_snd]
    have hmap : (fiberSectionsDiagram f x).map (op g₀) =
        (((Over.pullback @Etale ⊤ f).map g₀.val).left).appTop :=
      Scheme.Γ_map_op _
    have hcomp : Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)) ≫
        Spec.map ((((Over.pullback @Etale ⊤ f).map g₀.val).left).appTop) =
        Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p₀).hom)) := by
      rw [← Spec.map_comp]
      congr 1
      rw [← hmap]
      ext a
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      exact congrArg χ (toFiberSections_w_apply f x g₀ a)
    have hnat : (pullback p.1.hom f).isoSpec.inv ≫
          ((Over.pullback @Etale ⊤ f).map g₀.val).left ≫ pullback.snd p₀.1.hom f =
        Spec.map ((((Over.pullback @Etale ⊤ f).map g₀.val).left).appTop) ≫
          (pullback p₀.1.hom f).isoSpec.inv ≫ pullback.snd p₀.1.hom f := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ pullback.snd p₀.1.hom f)
        (Scheme.isoSpec_inv_naturality (X := pullback p.1.hom f)
          (Y := pullback p₀.1.hom f) _).symm
    calc Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)) ≫
          (pullback p.1.hom f).isoSpec.inv ≫ pullback.snd p.1.hom f
        = Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)) ≫
            (pullback p.1.hom f).isoSpec.inv ≫
            ((Over.pullback @Etale ⊤ f).map g₀.val).left ≫ pullback.snd p₀.1.hom f := by
          rw [pullback_map_left_snd]
      _ = (Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)) ≫
            Spec.map ((((Over.pullback @Etale ⊤ f).map g₀.val).left).appTop)) ≫
            (pullback p₀.1.hom f).isoSpec.inv ≫ pullback.snd p₀.1.hom f := by
          rw [Category.assoc, hnat]
      _ = Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p₀).hom)) ≫
            (pullback p₀.1.hom f).isoSpec.inv ≫ pullback.snd p₀.1.hom f := by
          rw [hcomp]
      _ = liftOfRingHom f x p₀ hp₀ χ := rfl

/-- The evaluation compatibility at an affine étale neighbourhood stage refining the
base stage. -/
private lemma toFiberSections_comp_eval
    (p : (geometricPoint x).fiber.Elements) (hp : IsAffine p.1.left) (g₀ : p ⟶ p₀) :
    toFiberSections f x p ≫
        fiberSectionsToStrictLocalization f x (Spec.map (CommRingCat.ofHom ψ))
          (liftOfRingHom f x p₀ hp₀ χ) (liftOfRingHom_comp f x p₀ hp₀ χ hχ) ≫
        strictLocalizationEval (liftOfRingHom f x p₀ hp₀ χ) =
      toFiberSections f x p ≫ CommRingCat.ofHom χ := by
  haveI := hp
  haveI : IsAffine ((𝟭 Scheme.{u}).obj p.1.left) := hp
  haveI : IsAffine (pullback p.1.hom f) := inferInstance
  rw [← Category.assoc, toFiberSections_fiberSectionsToStrictLocalization,
    toStrictLocalization_strictLocalizationEval, pullbackElements_obj_snd,
    pullbackFiberLift_liftOfRingHom_val f x χ p₀ hp₀ hχ p g₀,
    Γ_map_specMap_isoSpec_inv (pullback p.1.hom f)
      (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom))]
  ext a
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]

/-- **Evaluation compatibility at the lift associated to a character**: for the
geometric point `y = liftOfRingHom f x p₀ hp₀ χ` of `Y` associated to a character `χ`
of the fiber sections extending the evaluation of the strict localization of `X` at
`x`, evaluation of germs at `y` recovers `χ`:
`strictLocalizationEval y ∘ fiberSectionsToStrictLocalization = χ`. -/
theorem fiberSectionsToStrictLocalization_liftOfRingHom_eval :
    fiberSectionsToStrictLocalization f x (Spec.map (CommRingCat.ofHom ψ))
        (liftOfRingHom f x p₀ hp₀ χ) (liftOfRingHom_comp f x p₀ hp₀ χ hχ) ≫
      strictLocalizationEval (liftOfRingHom f x p₀ hp₀ χ) =
    CommRingCat.ofHom χ := by
  refine colimit.hom_ext fun P => ?_
  obtain ⟨p⟩ := P
  -- choose an affine étale neighbourhood stage refining both `p` and `p₀`
  set A := CategoryOfElements.pre (AffineEtale.Spec X) (geometricPoint x).fiber with hA
  obtain ⟨w⟩ : Nonempty (CostructuredArrow A p) := by
    haveI := Functor.Initial.out (F := A) p
    infer_instance
  obtain ⟨w₀⟩ : Nonempty (CostructuredArrow A p₀) := by
    haveI := Functor.Initial.out (F := A) p₀
    infer_instance
  set j₂ := IsCofiltered.min w.left w₀.left with hj₂
  set p₂ : (geometricPoint x).fiber.Elements := A.obj j₂ with hp₂
  haveI h₂ : IsAffine p₂.1.left := inferInstanceAs (IsAffine (Spec (unop j₂.1.left)))
  set e₁ : p₂ ⟶ p := A.map (IsCofiltered.minToLeft w.left w₀.left) ≫ w.hom with he₁
  set e₀ : p₂ ⟶ p₀ := A.map (IsCofiltered.minToRight w.left w₀.left) ≫ w₀.hom with he₀
  have hkey := toFiberSections_comp_eval f x χ p₀ hp₀ hχ p₂ h₂ e₀
  change toFiberSections f x p ≫ _ = toFiberSections f x p ≫ _
  rw [← toFiberSections_w f x e₁]
  simp only [Category.assoc]
  rw [hkey]

end Eval

/-!
### The induced map on the localization at a maximal ideal of the fiber sections

For a geometric point `y` of `Y` over `x` and a character `χ` of the fiber sections
compatible with evaluation at `y` (as provided by
`fiberSectionsToStrictLocalization_liftOfRingHom_eval` for the lift associated to
`χ`), the comparison map inverts every element outside `m = ker χ`, hence induces a
local homomorphism `Localization.AtPrime m ⟶ 𝒪^sh_{Y, y}`, and it kills the idempotents
of the complementary factors of the splitting of the fiber sections. -/

section Localization

variable (χ : fiberSections f x →+* Ω')

/-- Elementwise form of the evaluation compatibility: the value at `y` of the germ of a
fiber section is its value under the character `χ`. -/
theorem fiberSectionsToStrictLocalization_eval_apply
    (heval : fiberSectionsToStrictLocalization f x ε y hy ≫ strictLocalizationEval y =
      CommRingCat.ofHom χ) (z : fiberSections f x) :
    (strictLocalizationEval y).hom
      ((fiberSectionsToStrictLocalization f x ε y hy).hom z) = χ z := by
  have h := congrArg (fun t => CommRingCat.Hom.hom t z) heval
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using h

/-- **The value of a fiber section at the lifted geometric point is its value under the
character**: for a section `a` of the fiber `U ×_X Y` over a stage `(U, u)`, the
evaluation of `a` at the lift `(ε ≫ u, y)` agrees with the value of `χ` on the image of
`a` in the fiber sections. -/
theorem eval_pullbackFiberLift_apply
    (heval : fiberSectionsToStrictLocalization f x ε y hy ≫ strictLocalizationEval y =
      CommRingCat.ofHom χ) (p : (geometricPoint x).fiber.Elements)
    (a : Γ(((Over.pullback @Etale ⊤ f).obj p.1).left, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom
        (((pullbackFiberLift f x ε y hy p.1 p.2).val.appTop).hom a) =
      χ ((toFiberSections f x p).hom a) := by
  have h2 := congrArg (fun t => CommRingCat.Hom.hom t a)
    (toFiberSections_fiberSectionsToStrictLocalization f x ε y hy p)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  have h3 := congrArg (fun t => CommRingCat.Hom.hom t a)
    (toStrictLocalization_strictLocalizationEval y ((pullbackElements f x ε y hy).obj p))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
  have h4 : ((pullbackFiberLift f x ε y hy p.1 p.2).val.appTop).hom a =
      (Scheme.Γ.map ((pullbackElements f x ε y hy).obj p).2.val.op).hom a := by
    rw [pullbackElements_obj_snd]
    exact congrArg (fun t => CommRingCat.Hom.hom t a) (Scheme.Γ_map_op _).symm
  have h5 := fiberSectionsToStrictLocalization_eval_apply f x ε y hy χ heval
    ((toFiberSections f x p).hom a)
  exact ((congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom h4).trans h3.symm).trans
    ((congrArg (strictLocalizationEval y).hom h2.symm).trans h5)

/-- **The lifted geometric point lies in the basic open of every fiber section not
vanishing under the character**: if `χ` does not vanish on the image of a section `a`
of the fiber over a stage, the lift of the geometric point factors through the basic
open of `a`. Applied to the splitting idempotent avoiding `m = ker χ`, this shows that
the lift lands in the split summand of `m`. -/
theorem pullbackFiberLift_mem_basicOpen
    (heval : fiberSectionsToStrictLocalization f x ε y hy ≫ strictLocalizationEval y =
      CommRingCat.ofHom χ) (p : (geometricPoint x).fiber.Elements)
    (a : Γ(((Over.pullback @Etale ⊤ f).obj p.1).left, ⊤))
    (ha : χ ((toFiberSections f x p).hom a) ≠ 0) :
    (pullbackFiberLift f x ε y hy p.1 p.2).val.base default ∈
      ((Over.pullback @Etale ⊤ f).obj p.1).left.basicOpen a := by
  set v := (pullbackFiberLift f x ε y hy p.1 p.2).val with hv
  have hunit : IsUnit ((v.appTop).hom a) := by
    have h6 : (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom ((v.appTop).hom a) ≠ 0 := by
      rw [hv, eval_pullbackFiberLift_apply f x ε y hy χ heval p a]
      exact ha
    have h7 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom ((v.appTop).hom a)) :=
      isUnit_iff_ne_zero.mpr h6
    have h8 := h7.map (Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom
    have h9 : (Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom ((v.appTop).hom a)) =
        (v.appTop).hom a := by
      have h10 := congrArg (fun t => CommRingCat.Hom.hom t ((v.appTop).hom a))
        (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom_inv_id
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
        RingHom.id_apply] at h10
      exact h10
    rwa [h9] at h8
  have h1 : (Spec (CommRingCat.of Ω')).basicOpen ((v.appTop).hom a) = ⊤ :=
    RingedSpace.basicOpen_of_isUnit _ hunit
  have h2 : v ⁻¹ᵁ ((Over.pullback @Etale ⊤ f).obj p.1).left.basicOpen a =
      (Spec (CommRingCat.of Ω')).basicOpen ((v.appTop).hom a) :=
    v.preimage_basicOpen_top a
  rw [h1] at h2
  change default ∈ v ⁻¹ᵁ ((Over.pullback @Etale ⊤ f).obj p.1).left.basicOpen a
  rw [h2]
  trivial

/-- **The lifted geometric point comes from the split summand**: for a family of
sections of the fiber over a stage (e.g. the splitting idempotents) and an index `i`
whose section does not vanish under `χ`, the lift of the geometric point to the fiber
factors through the basic open summand of `i`, compatibly with the summand injection.
In particular the summand, equipped with this point, is an étale neighbourhood of `y`
refining the base-changed neighbourhood. -/
theorem exists_fiber_basicOpenSummand
    (heval : fiberSectionsToStrictLocalization f x ε y hy ≫ strictLocalizationEval y =
      CommRingCat.ofHom χ) (p : (geometricPoint x).fiber.Elements) {ι : Type u}
    (ε' : ι → Γ(((Over.pullback @Etale ⊤ f).obj p.1).left, ⊤)) (i : ι)
    (ha : χ ((toFiberSections f x p).hom (ε' i)) ≠ 0) :
    ∃ w : (geometricPoint y).fiber.obj
        (basicOpenSummand ((Over.pullback @Etale ⊤ f).obj p.1) ε' i),
      (geometricPoint y).fiber.map
          ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj p.1) ε').inj i) w =
        pullbackFiberLift f x ε y hy p.1 p.2 := by
  set v := (pullbackFiberLift f x ε y hy p.1 p.2).val with hv
  have hmem : v.base default ∈
      ((Over.pullback @Etale ⊤ f).obj p.1).left.basicOpen (ε' i) :=
    pullbackFiberLift_mem_basicOpen f x ε y hy χ heval p (ε' i) ha
  set O : (((Over.pullback @Etale ⊤ f).obj p.1).left).Opens :=
    ((Over.pullback @Etale ⊤ f).obj p.1).left.basicOpen (ε' i) with hO
  have hrange : Set.range v.base ⊆ Set.range O.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨t, rfl⟩
    rw [Unique.eq_default t]
    exact hmem
  let u' : Spec (CommRingCat.of Ω') ⟶ O := IsOpenImmersion.lift O.ι v hrange
  have hfac : u' ≫ O.ι = v := IsOpenImmersion.lift_fac O.ι v hrange
  refine ⟨geometricPoint.mkFiber y u' ?_, ?_⟩
  · change u' ≫ O.ι ≫ ((Over.pullback @Etale ⊤ f).obj p.1).hom = y
    rw [← Category.assoc, hfac]
    exact (pullbackFiberLift f x ε y hy p.1 p.2).property
  · refine Subtype.ext ?_
    change u' ≫ O.ι = v
    exact hfac

/-- **The comparison map inverts elements outside the kernel of the character**: the
germ at `y` of a fiber section with nonzero value under `χ` is invertible in the strict
localization. -/
theorem isUnit_fiberSectionsToStrictLocalization
    (heval : fiberSectionsToStrictLocalization f x ε y hy ≫ strictLocalizationEval y =
      CommRingCat.ofHom χ) {z : fiberSections f x} (hz : χ z ≠ 0) :
    IsUnit ((fiberSectionsToStrictLocalization f x ε y hy).hom z) := by
  rw [isUnit_iff_strictLocalizationEval_ne_zero,
    fiberSectionsToStrictLocalization_eval_apply f x ε y hy χ heval z]
  exact hz

/-- The comparison map reflects the maximal ideal: the germ at `y` of a fiber section
lies in the maximal ideal of the strict localization if and only if its value under `χ`
vanishes. -/
theorem fiberSectionsToStrictLocalization_mem_maximalIdeal_iff
    (heval : fiberSectionsToStrictLocalization f x ε y hy ≫ strictLocalizationEval y =
      CommRingCat.ofHom χ) (z : fiberSections f x) :
    (fiberSectionsToStrictLocalization f x ε y hy).hom z ∈
      IsLocalRing.maximalIdeal (strictLocalization y) ↔ χ z = 0 := by
  rw [mem_maximalIdeal_strictLocalization_iff,
    fiberSectionsToStrictLocalization_eval_apply f x ε y hy χ heval z]

/-- **The comparison map kills the complementary idempotents**: an idempotent fiber
section with vanishing value under `χ` (such as the splitting idempotents of the
factors at the other maximal ideals) has zero germ at `y`. -/
theorem fiberSectionsToStrictLocalization_eq_zero_of_isIdempotentElem
    (heval : fiberSectionsToStrictLocalization f x ε y hy ≫ strictLocalizationEval y =
      CommRingCat.ofHom χ) {z : fiberSections f x}
    (hidem : IsIdempotentElem z) (hz : χ z = 0) :
    (fiberSectionsToStrictLocalization f x ε y hy).hom z = 0 := by
  set b := (fiberSectionsToStrictLocalization f x ε y hy).hom z with hb
  have hbidem : IsIdempotentElem b := hidem.map _
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self b with hu | hu
  · exfalso
    refine (isUnit_iff_strictLocalizationEval_ne_zero y b).mp hu ?_
    rw [hb, fiberSectionsToStrictLocalization_eval_apply f x ε y hy χ heval z, hz]
  · exact hu.mul_right_cancel (by rw [zero_mul, mul_sub, mul_one, hbidem, sub_self])

variable (m : MaximalSpectrum (fiberSections f x))

/-- **The induced map from the localization of the fiber sections at a maximal
ideal to the strict localization at the associated lift**: since the comparison map
inverts every element outside `m = ker χ`, it factors through the localization
`S_m = Localization.AtPrime m`. The remaining goal of stage C of blueprint
`lemma:pbc-finite` is that this map is bijective. -/
noncomputable def localizationAtPrimeToStrictLocalization
    (heval : fiberSectionsToStrictLocalization f x ε y hy ≫ strictLocalizationEval y =
      CommRingCat.ofHom χ) (hker : RingHom.ker χ = m.asIdeal) :
    Localization.AtPrime m.asIdeal →+* strictLocalization y := by
  refine IsLocalization.lift (M := m.asIdeal.primeCompl)
    (S := Localization.AtPrime m.asIdeal)
    (g := (fiberSectionsToStrictLocalization f x ε y hy).hom) (fun s => ?_)
  refine isUnit_fiberSectionsToStrictLocalization f x ε y hy χ heval (fun h0 => ?_)
  have hmem : (s : fiberSections f x) ∈ m.asIdeal := by
    have h1 : (s : fiberSections f x) ∈ RingHom.ker χ := RingHom.mem_ker.mpr h0
    rwa [hker] at h1
  exact s.2 hmem

@[simp]
lemma localizationAtPrimeToStrictLocalization_algebraMap
    (heval : fiberSectionsToStrictLocalization f x ε y hy ≫ strictLocalizationEval y =
      CommRingCat.ofHom χ) (hker : RingHom.ker χ = m.asIdeal) (z : fiberSections f x) :
    localizationAtPrimeToStrictLocalization f x ε y hy χ m heval hker
        (algebraMap (fiberSections f x) (Localization.AtPrime m.asIdeal) z) =
      (fiberSectionsToStrictLocalization f x ε y hy).hom z :=
  IsLocalization.lift_eq _ _

/-- The induced map on the localization at `m` is a local homomorphism. -/
theorem isLocalHom_localizationAtPrimeToStrictLocalization
    (heval : fiberSectionsToStrictLocalization f x ε y hy ≫ strictLocalizationEval y =
      CommRingCat.ofHom χ) (hker : RingHom.ker χ = m.asIdeal) :
    IsLocalHom (localizationAtPrimeToStrictLocalization f x ε y hy χ m heval hker) := by
  constructor
  intro a ha
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.asIdeal.primeCompl a
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  rw [localizationAtPrimeToStrictLocalization, IsLocalization.lift_mk'] at ha
  have h1 : IsUnit ((fiberSectionsToStrictLocalization f x ε y hy).hom z) :=
    isUnit_of_mul_isUnit_left ha
  have h2 := (isUnit_iff_strictLocalizationEval_ne_zero y _).mp h1
  rw [fiberSectionsToStrictLocalization_eval_apply f x ε y hy χ heval z] at h2
  change z ∉ m.asIdeal
  rw [← hker]
  exact fun hmem => h2 (RingHom.mem_ker.mp hmem)

end Localization

/-!
### Existence of compatible characters over the algebraic closure
-/

/-- **Packaged existence statement over the algebraic closure**: for a finite morphism
`f`, every maximal ideal `m` of the fiber sections admits a character `χ` with values
in the algebraic closure of `Ω` and kernel `m`, such that the associated lift
`y = liftOfRingHom f x p₀ hp₀ χ` of `x` satisfies the evaluation compatibility
`strictLocalizationEval y ∘ fiberSectionsToStrictLocalization = χ`. In particular all
results of this file apply: the comparison map from the fiber sections to the strict
localization of `Y` at `y` induces a local homomorphism
`Localization.AtPrime m ⟶ 𝒪^sh_{Y, y}`
(`localizationAtPrimeToStrictLocalization`). -/
theorem exists_ringHom_fiberSectionsToStrictLocalization_eval [IsFinite f]
    (p₀ : (geometricPoint x).fiber.Elements) (hp₀ : IsAffine p₀.1.left)
    (m : MaximalSpectrum (fiberSections f x)) :
    ∃ (χ : fiberSections f x →+* AlgebraicClosure Ω)
      (hy : liftOfRingHom f x p₀ hp₀ χ ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))) ≫ x),
      RingHom.ker χ = m.asIdeal ∧
      fiberSectionsToStrictLocalization f x
          (Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))))
          (liftOfRingHom f x p₀ hp₀ χ) hy ≫
        strictLocalizationEval (liftOfRingHom f x p₀ hp₀ χ) = CommRingCat.ofHom χ := by
  obtain ⟨χ, hker, hcomp⟩ := exists_ringHom_ker_eq f x m
  exact ⟨χ, liftOfRingHom_comp f x p₀ hp₀ χ hcomp, hker,
    fiberSectionsToStrictLocalization_liftOfRingHom_eval f x χ p₀ hp₀ hcomp⟩

end AlgebraicGeometry.Scheme.Etale
