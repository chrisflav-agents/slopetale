/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Cofilteredness along a fully faithful initial functor

The source of a fully faithful initial functor into a cofiltered category is cofiltered.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The source of a fully faithful initial functor into a cofiltered category is
cofiltered. -/
theorem IsCofiltered.of_initial_of_fullyFaithful (F : C ⥤ D) [F.Initial] [F.Full]
    [F.Faithful] [IsCofiltered D] : IsCofiltered C := by
  have hwk : ∀ d : D, ∃ c : C, Nonempty (F.obj c ⟶ d) := fun d ↦ by
    haveI := Functor.Initial.out (F := F) d
    obtain ⟨s⟩ : Nonempty (CostructuredArrow F d) := inferInstance
    exact ⟨s.left, ⟨s.hom⟩⟩
  haveI : Nonempty D := IsCofiltered.nonempty
  haveI : Nonempty C := by
    obtain ⟨c, -⟩ := hwk (Classical.arbitrary D)
    exact ⟨c⟩
  haveI : IsCofilteredOrEmpty C := by
    constructor
    · intro X Y
      obtain ⟨c, ⟨s⟩⟩ := hwk (IsCofiltered.min (F.obj X) (F.obj Y))
      exact ⟨c, F.preimage (s ≫ IsCofiltered.minToLeft _ _),
        F.preimage (s ≫ IsCofiltered.minToRight _ _), trivial⟩
    · intro X Y f g
      obtain ⟨c, ⟨s⟩⟩ := hwk (IsCofiltered.eq (F.map f) (F.map g))
      refine ⟨c, F.preimage (s ≫ IsCofiltered.eqHom _ _), F.map_injective ?_⟩
      simp only [Functor.map_comp, Functor.map_preimage, Category.assoc]
      rw [IsCofiltered.eq_condition]
  exact ⟨⟩

end CategoryTheory
