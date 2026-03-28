/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.CategoryTheory.NatIso

/-!
# Local properties of sheafs
-/

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category C] (K : GrothendieckTopology C)
variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable {J : Type*} [Category J]

namespace Sheaf

--structure IsLocal (P : ObjectProperty (Sheaf K A)) : Prop where
--  iff_of_coversTop (F : Sheaf K A) {ι : Type*} (X : ι → C) (h : K.CoversTop X) :
--    P F ↔ ∀ i, P (F.over (X i))

variable {ι : Type*} (X : ι → C) (hX : K.CoversTop X)
include hX

/-- A sheaf morphism is an isomorphism if it becomes one after pulling back along each
element of a covering family. -/
lemma isIso_of_coversTop {F G : Sheaf K A} {f : F ⟶ G}
    (h : ∀ i, IsIso ((K.overPullback A (X i)).map f)) :
    IsIso f := by
  -- f.val.app (op Z) is iso for any Z with a map to some X i
  have hiso (Z : C) (i : ι) (g : Z ⟶ X i) : IsIso (f.val.app (op Z)) := by
    have h1 : IsIso ((sheafToPresheaf (K.over (X i)) A).map ((K.overPullback A (X i)).map f)) :=
      inferInstance
    rw [sheafToPresheaf_map, NatTrans.isIso_iff_isIso_app] at h1
    exact h1 (op (Over.mk g))
  -- Show IsIso f.val, then sheafToPresheaf reflects isos
  haveI : IsIso f.val := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W
    set S : K.Cover W.unop := hX.cover W.unop
    have harrow (I : S.Arrow) : IsIso (f.val.app (op I.Y)) := by
      obtain ⟨i, ⟨g⟩⟩ := I.hf
      exact hiso I.Y i g
    -- Construct inverse via sheaf amalgamation
    let invMap : G.val.obj (op W.unop) ⟶ F.val.obj (op W.unop) :=
      F.2.amalgamate S (fun I => G.val.map I.f.op ≫ inv (f.val.app (op I.Y))) (by
        intro I₁ I₂ r
        have hZ : IsIso (f.val.app (op r.Z)) := by
          obtain ⟨i, ⟨g⟩⟩ := I₁.hf
          exact hiso r.Z i (r.g₁ ≫ g)
        simp only [Category.assoc, f.val.naturality_inv]
        rw [← Category.assoc, ← Category.assoc, ← G.val.map_comp, ← G.val.map_comp,
          ← op_comp, ← op_comp, r.w])
    change IsIso (f.val.app (op W.unop))
    exact ⟨⟨invMap, by
      apply F.2.hom_ext S
      intro I
      simp only [Category.assoc, Category.id_comp]
      rw [Presheaf.IsSheaf.amalgamate_map, ← Category.assoc, ← f.val.naturality,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id], by
      apply G.2.hom_ext S
      intro I
      simp only [Category.assoc, Category.id_comp]
      rw [← f.val.naturality, Presheaf.IsSheaf.amalgamate_map_assoc,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩⟩
  rw [← isIso_iff_of_reflects_iso f (sheafToPresheaf K A), sheafToPresheaf_map]
  exact this

/-- A sheaf morphism is an isomorphism iff it becomes one after pulling back along each
element of a covering family. -/
lemma isIso_iff_of_coversTop {F G : Sheaf K A} (f : F ⟶ G) :
    IsIso f ↔ ∀ i, IsIso ((K.overPullback A (X i)).map f) :=
  ⟨fun _ _ => inferInstance, fun h => isIso_of_coversTop K X hX h⟩

lemma foo (F : Sheaf K A) [HasColimitsOfShape J A] [(forget A).ReflectsIsomorphisms]
    (hF : ∀ i : ι, PreservesColimitsOfShape J (F.over (X i)).val) :
    PreservesColimitsOfShape J F.val := by
  constructor
  intro D
  constructor
  intro c hc
  constructor
  have : IsIso ((colimit.isColimit (D ⋙ F.val)).desc (F.val.mapCocone c)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    simp only [colimit.cocone_x, Functor.mapCocone_pt, colimit.isColimit_desc]
    refine ⟨?_, ?_⟩
    · -- Injectivity: use sheaf property on covering
      intro x₁ x₂ h
      sorry
    · -- Surjectivity: use sheaf amalgamation to construct preimage
      intro y
      sorry
  exact .ofPointIso (colimit.isColimit _)

end Sheaf

end CategoryTheory
