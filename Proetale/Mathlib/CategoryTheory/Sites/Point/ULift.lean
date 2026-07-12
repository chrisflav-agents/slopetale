/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Point.Conservative
import Proetale.Mathlib.CategoryTheory.Elements

/-!
# Universe lifting for points of sites

A point of a site with fiber functor valued in `Type w` induces a point with fiber
functor valued in `Type (max w s)` by postcomposing with `uliftFunctor`. We show that
this operation preserves conservativity of (small) families of points, so that a site
with enough `w`-points also has enough `max w s`-points.

This is needed to check isomorphisms of sheaves valued in a category which is concrete
over a bigger universe than the one where a conservative family of points is available
(e.g. `Ab.{u + 1}`-valued sheaves on the small étale site of a `u`-scheme).
-/

universe s w t v'' u'' v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

/-- The universe lift of a point of a site, obtained by postcomposing the fiber functor
with `uliftFunctor`. -/
def ulift.{s', w', v', u'} {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    (Φ : Point.{w'} J) : Point.{max w' s'} J where
  fiber := Φ.fiber ⋙ uliftFunctor.{s'}
  isCofiltered :=
    IsCofiltered.of_equivalence (CategoryOfElements.compUliftEquivalence Φ.fiber).symm
  initiallySmall := by
    have := Φ.initiallySmall
    have : EssentiallySmall.{max w' s'} (InitialModel Φ.fiber.Elements) :=
      essentiallySmallSelf _
    exact initiallySmall_of_initial_of_essentiallySmall
      (fromInitialModel Φ.fiber.Elements ⋙
        (CategoryOfElements.compUliftEquivalence Φ.fiber).inverse)
  jointly_surjective R h x := by
    obtain ⟨Y, f, hf, y, hy⟩ := Φ.jointly_surjective R h x.down
    exact ⟨Y, f, hf, ULift.up y, congrArg ULift.up hy⟩

@[simp]
lemma ulift_fiber (Φ : Point.{w} J) :
    (Point.ulift.{s} Φ).fiber = Φ.fiber ⋙ uliftFunctor.{s} :=
  rfl

instance (Φ : Point.{w} J) {A : Type u''} [Category.{v''} A]
    [HasColimitsOfSize.{max w s, max w s} A] :
    HasColimitsOfShape (Φ.fiber ⋙ uliftFunctor.{s, w}).Elementsᵒᵖ A :=
  inferInstanceAs (HasColimitsOfShape (Point.ulift.{s} Φ).fiber.Elementsᵒᵖ A)

open CategoryOfElements in
/-- The stalk of a presheaf at the universe lift of a point agrees with the stalk at
the point itself. -/
noncomputable def uliftPresheafFiberIso.{s', w', v', u'}
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (Φ : Point.{w'} J)
    {A : Type u''} [Category.{v''} A]
    [HasColimitsOfSize.{w', w'} A] [HasColimitsOfSize.{max w' s', max w' s'} A] :
    (Point.ulift.{s'} Φ).presheafFiber (A := A) ≅ Φ.presheafFiber :=
  Functor.isoWhiskerLeft ((Functor.whiskeringLeft _ _ A).obj (π Φ.fiber).op)
    (Functor.Final.colimIso (compUliftEquivalence.{s'} Φ.fiber).functor.op)

open CategoryOfElements in
/-- The stalk of a sheaf at the universe lift of a point agrees with the stalk at
the point itself. -/
noncomputable def uliftSheafFiberIso.{s', w', v', u'}
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (Φ : Point.{w'} J)
    {A : Type u''} [Category.{v''} A]
    [HasColimitsOfSize.{w', w'} A] [HasColimitsOfSize.{max w' s', max w' s'} A] :
    (Point.ulift.{s'} Φ).sheafFiber (A := A) ≅ Φ.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (uliftPresheafFiberIso Φ)

end GrothendieckTopology.Point

namespace ObjectProperty.IsConservativeFamilyOfPoints

open GrothendieckTopology

/-- If a small family of points is conservative, then every sieve whose fibers are
jointly surjective at each point of the family is a covering sieve. This is the converse
of the criterion `ObjectProperty.IsConservativeFamilyOfPoints.mk'` (SGA 4 IV 6.5). -/
lemma sieve_mem [LocallySmall.{w} C] {P : ObjectProperty (Point.{w} J)}
    (hP : P.IsConservativeFamilyOfPoints) [ObjectProperty.Small.{w} P]
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    {X : C} (S : Sieve X)
    (h : ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
      ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : Φ.obj.fiber.obj Y), Φ.obj.fiber.map g y = x) :
    S ∈ J X := by
  refine J.superset_covering
    (S := Sieve.ofArrows _ (fun i : Σ (Y : C), { g : Y ⟶ X // S g } ↦ i.2.1)) ?_ ?_
  · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    exact fun i ↦ i.2.2
  · rw [hP.jointly_reflect_ofArrows_mem_of_small]
    intro Φ x
    obtain ⟨Y, g, hg, y, hy⟩ := h Φ x
    exact ⟨⟨Y, g, hg⟩, y, hy⟩

/-- Conservativity of a small family of points is preserved by universe lifting. -/
lemma ulift.{s', w', t', v', u'} {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    [LocallySmall.{w'} C] [LocallySmall.{max w' s'} C] {ι : Type t'} {F : ι → Point.{w'} J}
    (hP : (ObjectProperty.ofObj F).IsConservativeFamilyOfPoints)
    [Small.{w'} ι] [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')]
    [HasSheafify J (Type (max w' s'))] :
    (ObjectProperty.ofObj fun i ↦ Point.ulift.{s'} (F i)).IsConservativeFamilyOfPoints := by
  refine mk' (fun X S hS ↦ hP.sieve_mem S ?_)
  rintro ⟨Φ, ⟨i⟩⟩ x
  obtain ⟨Y, g, hg, y, hy⟩ := hS ⟨Point.ulift.{s'} (F i), ⟨i⟩⟩ (ULift.up x)
  exact ⟨Y, g, hg, y.down, congrArg ULift.down hy⟩

end ObjectProperty.IsConservativeFamilyOfPoints

namespace GrothendieckTopology.HasEnoughPoints

/-- A site with enough `w`-points has enough `max w s`-points. -/
lemma ulift.{s', w', v', u'} {C : Type u'} [Category.{v'} C]
    (J : GrothendieckTopology C) [LocallySmall.{w'} C] [LocallySmall.{max w' s'} C]
    [HasEnoughPoints.{w'} J]
    [HasSheafify J (Type w')] [J.WEqualsLocallyBijective (Type w')]
    [HasSheafify J (Type (max w' s'))] :
    HasEnoughPoints.{max w' s'} J := by
  obtain ⟨P, hsmall, hP⟩ := exists_objectProperty.{w'} J
  haveI := hsmall
  haveI : Small.{max w' s'} (Subtype P) := small_lift _
  rw [← ObjectProperty.ofObj_subtypeVal P] at hP
  exact ⟨_, inferInstance,
    ObjectProperty.IsConservativeFamilyOfPoints.ulift.{s'} hP⟩

end GrothendieckTopology.HasEnoughPoints

end CategoryTheory
