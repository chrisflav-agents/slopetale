/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Order.Filter.Finite

/-!
# Closures in categorical limits of topological spaces.

-/

open CategoryTheory Limits Filter Topology

theorem TopCat.closure_eq_iInter_preimage_closure_image {I : Type*} [Category I] [IsCofiltered I]
    {F : Functor I TopCat} {C : Cone F} (hC : IsLimit C) (s : Set C.pt) :
    closure s = ⋂ (i : I), (C.π.app i)⁻¹' (closure ((C.π.app i)'' s)) := by
  apply Set.Subset.antisymm
  · -- ⊆ direction: RHS is closed and contains s
    refine closure_minimal ?_ ?_
    · intro x hx
      simp only [Set.mem_iInter, Set.mem_preimage]
      intro i
      exact subset_closure ⟨x, hx, rfl⟩
    · exact isClosed_iInter fun i =>
        (isClosed_closure.preimage (C.π.app i).hom.continuous)
  · -- ⊇ direction: uses the initial topology characterization and IsCofiltered
    intro x hx
    simp only [Set.mem_iInter, Set.mem_preimage] at hx
    rw [mem_closure_iff_nhds]
    intro U hU
    have htop : C.pt.str = ⨅ j, (F.obj j).str.induced (C.π.app j) := TopCat.induced_of_isLimit C hC
    rw [htop, nhds_iInf, Filter.mem_iInf] at hU
    obtain ⟨J, hJfin, V, hV, rfl⟩ := hU
    -- Convert J to Finset
    haveI : Fintype J := hJfin.fintype
    let Jfin : Finset I := J.toFinset
    -- Use cofiltered to find common object k
    obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists Jfin
    -- Get morphisms from k to each j
    have hkmor : ∀ j : J, k ⟶ j.val := fun j => (hk (Set.mem_toFinset.mpr j.property)).some
    -- For each j, extract neighborhood in F.obj j
    have hVmem : ∀ j : J, ∃ W ∈ nhds (C.π.app j.val x), (C.π.app j.val)⁻¹' W ⊆ V j := by
      intro j
      have : V j ∈ @nhds _ (TopologicalSpace.induced (C.π.app j.val) (F.obj j.val).str) x := hV j
      rw [nhds_induced] at this
      exact Filter.mem_comap.mp this
    choose W hWmem hWsub using hVmem
    -- Construct neighborhood at k by pulling back through morphisms
    let Wk : Set (F.obj k) := ⋂ j : J, (F.map (hkmor j))⁻¹' (W j)
    have hWk_nhds : Wk ∈ nhds (C.π.app k x) := by
      refine Filter.iInter_mem.mpr fun j => ?_
      have hnat : C.π.app k ≫ F.map (hkmor j) = C.π.app j.val := by
        have := C.π.naturality (hkmor j)
        simp only [Functor.const_obj_map] at this
        exact this.symm
      have : W j ∈ nhds ((C.π.app k ≫ F.map (hkmor j)) x) := by
        have h := hWmem j
        rw [← hnat] at h
        exact h
      exact (F.map (hkmor j)).hom.continuous.continuousAt this
    -- Use closure property at k: Wk ∩ (C.π.app k)'' s is nonempty
    have hxk : C.π.app k x ∈ closure ((C.π.app k)'' s) := hx k
    rw [mem_closure_iff_nhds] at hxk
    have hinter : (Wk ∩ (C.π.app k)'' s).Nonempty := hxk Wk hWk_nhds
    obtain ⟨y, hy_wk, z, hz, rfl⟩ := hinter
    -- Now z ∈ s and C.π.app k z ∈ Wk
    refine ⟨z, ?_, hz⟩
    simp only [Set.mem_iInter]
    intro j
    -- We have C.π.app k z ∈ Wk = ⋂ j : J, (F.map (hkmor j))⁻¹' (W j)
    have : C.π.app k z ∈ (F.map (hkmor j))⁻¹' (W j) := by
      change C.π.app k z ∈ Wk at hy_wk
      simp only [Wk, Set.mem_iInter] at hy_wk
      exact hy_wk j
    -- So (F.map (hkmor j)) (C.π.app k z) ∈ W j
    simp only [Set.mem_preimage] at this
    -- By naturality, (C.π.app j.val) z = (C.π.app k ≫ F.map (hkmor j)) z
    have hnat : C.π.app k ≫ F.map (hkmor j) = C.π.app j.val := by
      have := C.π.naturality (hkmor j)
      simp only [Functor.const_obj_map] at this
      exact this.symm
    have hzj : (C.π.app j.val) z ∈ W j := by
      rw [← hnat]
      exact this
    -- Now (C.π.app j.val)⁻¹' W j ⊆ V j
    exact hWsub j hzj


theorem image_closure_image_subset_closure_image {I : Type*} [Category I]
    {F : Functor I TopCat} (C : Cone F) (s : Set C.pt) {i j : I} (f : i ⟶ j) :
    (F.map f) '' (closure ((C.π.app i) '' s)) ⊆ closure ((C.π.app j) '' s) := by
  have hnat : C.π.app i ≫ F.map f = C.π.app j := by
    have := C.π.naturality f
    dsimp [Functor.const] at this
    rw [Category.id_comp] at this
    exact this.symm
  have himg : (C.π.app j) '' s = (F.map f) '' ((C.π.app i) '' s) := by
    rw [← hnat, ← Set.image_comp]
    rfl
  rw [himg]
  exact image_closure_subset_closure_image (F.map f).hom.continuous
