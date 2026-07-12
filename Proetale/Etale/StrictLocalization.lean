/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.AlgebraicGeometry.Sites.GeometricPoint

/-!
# The strict localization of a scheme at a geometric point

For a geometric point `x : Spec Ω ⟶ X` (with `Ω` separably closed), the *strict
localization* of `X` at `x` is the filtered colimit of the rings of global functions
over the étale neighbourhoods of `x`, i.e. over the category of elements of the fiber
functor of the associated point of the small étale site
(`AlgebraicGeometry.Scheme.Etale.geometricPoint`).

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.strictLocalization`: the strict localization, as a
  filtered colimit of commutative rings.
- `AlgebraicGeometry.Scheme.Etale.strictLocalizationEval`: evaluation at the geometric
  point, a ring homomorphism to `Ω`.

## Main results

- `AlgebraicGeometry.Scheme.Etale.isUnit_iff_strictLocalizationEval_ne_zero`: an element
  of the strict localization is a unit if and only if its value at the geometric point
  is nonzero. In particular the strict localization is a local ring and evaluation is a
  local homomorphism.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X)

/-- The underlying scheme of an étale neighbourhood of a geometric point. -/
noncomputable abbrev neighbourhoodScheme
    (p : (geometricPoint x).fiber.Elements) : Scheme.{u} :=
  p.1.left

/-- The diagram of rings of global functions on the étale neighbourhoods of a geometric
point. Its filtered colimit is the strict localization. -/
noncomputable def strictLocalizationDiagram :
    ((geometricPoint x).fiber.Elements)ᵒᵖ ⥤ CommRingCat.{u} :=
  (CategoryOfElements.π (geometricPoint x).fiber ⋙
    Etale.forget X ⋙ CategoryTheory.Over.forget X).op ⋙ Scheme.Γ

/-- The strict localization of `X` at the geometric point `x`: the colimit of the rings
of functions over the étale neighbourhoods of `x`. -/
noncomputable def strictLocalization : CommRingCat.{u} :=
  colimit (strictLocalizationDiagram x)

/-- The canonical map from the functions on an étale neighbourhood to the strict
localization. -/
noncomputable def toStrictLocalization (p : (geometricPoint x).fiber.Elements) :
    Scheme.Γ.obj (op p.1.left) ⟶ strictLocalization x :=
  colimit.ι (strictLocalizationDiagram x) (op p)

@[reassoc, elementwise]
lemma toStrictLocalization_w {p q : (geometricPoint x).fiber.Elements} (g : p ⟶ q) :
    (strictLocalizationDiagram x).map (op g) ≫ toStrictLocalization x p =
      toStrictLocalization x q :=
  colimit.w (strictLocalizationDiagram x) (op g)

/-- The cocone on the neighbourhood diagram given by evaluating functions at the
geometric point. -/
noncomputable def strictLocalizationEvalCocone : Cocone (strictLocalizationDiagram x) where
  pt := CommRingCat.of Ω
  ι :=
    { app p := Scheme.Γ.map p.unop.2.val.op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
      naturality p q f := by
        have h : p.unop.2.val = q.unop.2.val ≫ f.unop.val.left :=
          (congrArg Subtype.val f.unop.property).symm
        dsimp [strictLocalizationDiagram]
        rw [Category.comp_id, ← Category.assoc, ← Scheme.Hom.comp_appTop]
        exact congrArg (· ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom)
          (congrArg Scheme.Hom.appTop h.symm) }

/-- Evaluation of germs at the geometric point, as a homomorphism from the strict
localization to `Ω`. -/
noncomputable def strictLocalizationEval : strictLocalization x ⟶ CommRingCat.of Ω :=
  colimit.desc _ (strictLocalizationEvalCocone x)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toStrictLocalization_strictLocalizationEval
    (p : (geometricPoint x).fiber.Elements) :
    toStrictLocalization x p ≫ strictLocalizationEval x =
      Scheme.Γ.map p.2.val.op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom :=
  colimit.ι_desc _ _

/-- Every element of the strict localization is the germ of a function on some étale
neighbourhood. -/
lemma exists_toStrictLocalization_eq (z : strictLocalization x) :
    ∃ (p : (geometricPoint x).fiber.Elements) (a : Scheme.Γ.obj (op p.1.left)),
      (toStrictLocalization x p).hom a = z := by
  obtain ⟨⟨p⟩, a, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget CommRingCat)
      (colimit.isColimit (strictLocalizationDiagram x))) z
  exact ⟨p, a, rfl⟩

/-- A function on an étale neighbourhood whose value at the geometric point is
invertible has an invertible germ in the strict localization: the basic open on which
the function is invertible is again an étale neighbourhood. -/
private lemma isUnit_toStrictLocalization_of_isUnit
    (p : (geometricPoint x).fiber.Elements) (a : Scheme.Γ.obj (op p.1.left))
    (hb : IsUnit ((p.2.val.appTop).hom a)) :
    IsUnit ((toStrictLocalization x p).hom a) := by
  haveI : Etale p.1.hom := p.1.prop
  let v : Spec (CommRingCat.of Ω) ⟶ p.1.left := p.2.val
  have hb' : IsUnit ((v.appTop).hom a) := hb
  -- the geometric point lands in the basic open of `a`
  have hmem : v.base default ∈ p.1.left.basicOpen a := by
    have h1 : (Spec (CommRingCat.of Ω)).basicOpen ((v.appTop).hom a) = ⊤ :=
      RingedSpace.basicOpen_of_isUnit _ hb'
    have h2 := v.preimage_basicOpen_top a
    rw [h1] at h2
    show default ∈ v ⁻¹ᵁ p.1.left.basicOpen a
    rw [h2]
    trivial
  -- the basic open of `a`, as an étale neighbourhood refining `p`
  set O : p.1.left.Opens := p.1.left.basicOpen a with hO
  have hrange : Set.range v.base ⊆ Set.range O.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨t, rfl⟩
    rw [Unique.eq_default t]
    exact hmem
  let u' : Spec (CommRingCat.of Ω) ⟶ O := IsOpenImmersion.lift O.ι v hrange
  have hfac : u' ≫ O.ι = v := IsOpenImmersion.lift_fac O.ι v hrange
  let V : X.Etale := MorphismProperty.Over.mk _ (O.ι ≫ p.1.hom) inferInstance
  let elt : (geometricPoint x).fiber.obj V := geometricPoint.mkFiber x u' (by
    show u' ≫ O.ι ≫ p.1.hom = x
    rw [← Category.assoc, hfac]
    exact p.2.property)
  let pV : (geometricPoint x).fiber.Elements := ⟨V, elt⟩
  let g : pV ⟶ p :=
    ⟨MorphismProperty.Over.homMk O.ι rfl trivial, Subtype.ext (by
      show u' ≫ O.ι = v
      exact hfac)⟩
  -- the restriction of `a` to its basic open is invertible
  have hunit : IsUnit (((strictLocalizationDiagram x).map (op g)).hom a) := by
    have himg : O.ι ''ᵁ (⊤ : O.toScheme.Opens) = O := Scheme.Opens.ι_image_top O
    have hcomp : (homOfLE le_top : O.ι ''ᵁ (⊤ : O.toScheme.Opens) ⟶ ⊤) =
        eqToHom himg ≫ homOfLE le_top := Subsingleton.elim _ _
    show IsUnit ((p.1.left.presheaf.map
      (homOfLE (x := O.ι ''ᵁ (⊤ : O.toScheme.Opens)) le_top).op).hom a)
    rw [hcomp, op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (p.1.left.toRingedSpace.isUnit_res_basicOpen a).map _
  have h := congrArg (fun t => CommRingCat.Hom.hom t a) (toStrictLocalization_w x g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [← h]
  exact hunit.map _

/-- An element of the strict localization is a unit if and only if its value at the
geometric point is nonzero. -/
theorem isUnit_iff_strictLocalizationEval_ne_zero (z : strictLocalization x) :
    IsUnit z ↔ (strictLocalizationEval x).hom z ≠ 0 := by
  constructor
  · intro hz h0
    have hu := hz.map (strictLocalizationEval x).hom
    rw [h0] at hu
    exact not_isUnit_zero hu
  · intro hz
    obtain ⟨p, a, rfl⟩ := exists_toStrictLocalization_eq x z
    apply isUnit_toStrictLocalization_of_isUnit
    have hcomp := congrArg (fun t => CommRingCat.Hom.hom t a)
      (toStrictLocalization_strictLocalizationEval x p)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hcomp
    rw [hcomp] at hz
    have h1 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
        ((Scheme.Γ.map p.2.val.op).hom a)) := isUnit_iff_ne_zero.mpr hz
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    have h3 : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.Γ.map p.2.val.op).hom a)) =
        (Scheme.Γ.map p.2.val.op).hom a := by
      have h4 := congrArg (fun t => CommRingCat.Hom.hom t ((Scheme.Γ.map p.2.val.op).hom a))
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom_inv_id
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h4
      exact h4
    rw [h3] at h2
    exact h2

instance : Nontrivial (strictLocalization x) :=
  (strictLocalizationEval x).hom.domain_nontrivial

/-- The strict localization at a geometric point is a local ring, the maximal ideal
being the functions vanishing at the point. -/
instance : IsLocalRing (strictLocalization x) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb ↦ ?_
  simp only [mem_nonunits_iff, isUnit_iff_strictLocalizationEval_ne_zero, not_not] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

/-- Evaluation at the geometric point is a local homomorphism. -/
instance : IsLocalHom (strictLocalizationEval x).hom :=
  ⟨fun z hz ↦ (isUnit_iff_strictLocalizationEval_ne_zero x z).mpr hz.ne_zero⟩

lemma mem_maximalIdeal_strictLocalization_iff (z : strictLocalization x) :
    z ∈ IsLocalRing.maximalIdeal (strictLocalization x) ↔
      (strictLocalizationEval x).hom z = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_strictLocalizationEval_ne_zero, not_not]

end AlgebraicGeometry.Scheme.Etale
