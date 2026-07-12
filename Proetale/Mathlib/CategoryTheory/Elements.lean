/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Precomposition on categories of elements, and smallness

For functors `G : C ⥤ D` and `F : D ⥤ Type w`, we define the precomposition functor
`CategoryOfElements.pre G F : (G ⋙ F).Elements ⥤ F.Elements` and show that it inherits
fullness, faithfulness and essential surjectivity from `G`. As an application, the
category of elements of a type-valued functor on an essentially `w`-small category is
essentially `w`-small.
-/

universe w' w v' v u' u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace CategoryOfElements

/-- The functor `(G ⋙ F).Elements ⥤ F.Elements` induced by precomposing
`F : D ⥤ Type w` with `G : C ⥤ D`. -/
@[simps]
def pre (G : C ⥤ D) (F : D ⥤ Type w) : (G ⋙ F).Elements ⥤ F.Elements where
  obj p := ⟨G.obj p.1, p.2⟩
  map f := ⟨G.map f.val, f.property⟩

instance (G : C ⥤ D) (F : D ⥤ Type w) [G.Faithful] : (pre G F).Faithful where
  map_injective h := Subtype.ext <| G.map_injective congr($(h).val)

instance (G : C ⥤ D) (F : D ⥤ Type w) [G.Full] : (pre G F).Full where
  map_surjective {p q} f :=
    ⟨⟨G.preimage f.val, by simpa only [Functor.comp_map, G.map_preimage] using f.property⟩,
      Subtype.ext (G.map_preimage f.val)⟩

instance (G : C ⥤ D) (F : D ⥤ Type w) [G.EssSurj] : (pre G F).EssSurj where
  mem_essImage p := by
    obtain ⟨d, x⟩ := p
    refine ⟨⟨G.objPreimage d, F.map (G.objObjPreimageIso d).inv x⟩,
      ⟨isoMk _ _ (G.objObjPreimageIso d) ?_⟩⟩
    show F.map _ (F.map _ x) = x
    rw [← types_comp_apply (F.map _) (F.map _), ← F.map_comp, Iso.inv_hom_id, F.map_id,
      types_id_apply]

instance (G : C ⥤ D) (F : D ⥤ Type w) [G.IsEquivalence] : (pre G F).IsEquivalence where

/-- The category of elements of `F ⋙ uliftFunctor.{w'}` is equivalent to the category of
elements of `F`. -/
def compUliftEquivalence (F : C ⥤ Type w) :
    (F ⋙ uliftFunctor.{w'}).Elements ≌ F.Elements where
  functor :=
    { obj p := ⟨p.1, p.2.down⟩
      map f := ⟨f.val, congrArg ULift.down f.property⟩ }
  inverse :=
    { obj p := ⟨p.1, ULift.up p.2⟩
      map f := ⟨f.val, congrArg ULift.up f.property⟩ }
  unitIso := NatIso.ofComponents fun p ↦ Iso.refl _
  counitIso := NatIso.ofComponents fun p ↦ Iso.refl _

end CategoryOfElements

/-- The category of elements of a type-valued functor on an essentially small category
is essentially small. -/
instance Functor.Elements.essentiallySmall [EssentiallySmall.{w} C] (F : C ⥤ Type w) :
    EssentiallySmall.{w} F.Elements := by
  let e := equivSmallModel.{w} C
  have : Small.{w} (e.inverse ⋙ F).Elements :=
    inferInstanceAs <| Small.{w} ((s : SmallModel.{w} C) × F.obj (e.inverse.obj s))
  have : EssentiallySmall.{w} (e.inverse ⋙ F).Elements := inferInstance
  exact (essentiallySmall_congr (CategoryOfElements.pre e.inverse F).asEquivalence).1 this

end CategoryTheory
