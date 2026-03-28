/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Mathlib.Topology.Inseparable
import Proetale.Mathlib.Topology.Separation.Basic
import Proetale.Mathlib.Topology.Spectral.Basic
import Proetale.Topology.SpectralSpace.Constructible
import Proetale.Topology.SpectralSpace.ConnectedComponent
import Mathlib.Topology.JacobsonSpace

/-!
# w-local spaces

In this file we define w-local spaces. These are spectral spaces in which every point
specializes to a unique closed point and where the set of closed points is closed.
-/

/--
A spectral space is w-local if every point specializes to a unique closed point
and the set of closed points is closed.
Note: In a spectral space, every point specializes to a closed point, so we only require
the uniqueness.
-/
class WLocalSpace (X : Type*) [TopologicalSpace X] : Prop extends SpectralSpace X where
  /-- Any two closed specializations of a point are equal. -/
  eq_of_specializes {x c c' : X} (hc : IsClosed {c}) (hc' : IsClosed {c'})
    (hxc : x ⤳ c) (hxc' : x ⤳ c') : c = c'
  /-- The set of closed points is closed. -/
  isClosed_closedPoints : IsClosed (closedPoints X)

attribute [instance] WLocalSpace.isClosed_closedPoints

/-- A w-local map is a spectral map that maps closed points to closed points. -/
@[mk_iff]
structure IsWLocalMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Prop
    extends IsSpectralMap f where
  closedPoints_subset_preimage_closedPoints : closedPoints X ⊆ f ⁻¹' (closedPoints Y)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A w-local map sends closed points to closed points. -/
lemma IsWLocalMap.isClosed_singleton {f : X → Y} (hf : IsWLocalMap f)
    {x : X} (hx : IsClosed {x}) :
    IsClosed {f x} :=
  mem_closedPoints_iff.mp
    (hf.closedPoints_subset_preimage_closedPoints (mem_closedPoints_iff.mpr hx))

lemma IsWLocalMap.comp {Z : Type*} [TopologicalSpace Z] {f : X → Y} {g : Y → Z}
    (hf : IsWLocalMap f) (hg : IsWLocalMap g) :
    IsWLocalMap (g ∘ f) where
  toIsSpectralMap := hg.toIsSpectralMap.comp hf.toIsSpectralMap
  closedPoints_subset_preimage_closedPoints _ hx :=
    hg.closedPoints_subset_preimage_closedPoints
      (hf.closedPoints_subset_preimage_closedPoints hx)

/-- An embedding with specialization-stable range maps closed singletons to closed singletons. -/
lemma Topology.IsEmbedding.isClosed_singleton
    {f : X → Y} (hf : IsEmbedding f) (hrange : StableUnderSpecialization (Set.range f))
    {z : X} (hz : IsClosed {z}) :
    IsClosed {f z} := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun y hy => ?_) subset_closure
  have hspec : f z ⤳ y := specializes_iff_mem_closure.mpr hy
  obtain ⟨z', rfl⟩ := hrange hspec (Set.mem_range_self z)
  have hzz' : z ⤳ z' := hf.specializes_iff.mp hspec
  have : z' ∈ ({z} : Set X) := hz.closure_eq ▸ hzz'.mem_closure
  rw [Set.mem_singleton_iff.mp this]
  exact Set.mem_singleton _

/-- If `f` is an embedding and `{f z}` is closed, then `{z}` is closed. -/
lemma Topology.IsEmbedding.isClosed_singleton_of_isClosed_image_singleton
    {f : X → Y} (hf : IsEmbedding f) {z : X} (hz : IsClosed {f z}) :
    IsClosed {z} := by
  rw [← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun x hx => ?_) subset_closure
  have hfspec : f z ⤳ f x := (specializes_iff_mem_closure.mpr hx).map hf.continuous
  exact Set.mem_singleton_iff.mpr
    (hf.injective (Set.mem_singleton_iff.mp (hz.closure_eq ▸ hfspec.mem_closure)))

/-- An embedding with specialization-stable range identifies
closed points of `X` with the preimage of closed points of `Y`. -/
lemma Topology.IsEmbedding.closedPoints_eq_preimage
    {f : X → Y} (hf : IsEmbedding f) (hrange : StableUnderSpecialization (Set.range f)) :
    closedPoints X = f ⁻¹' closedPoints Y := by
  ext x
  simp only [Set.mem_preimage, mem_closedPoints_iff]
  exact ⟨hf.isClosed_singleton hrange, hf.isClosed_singleton_of_isClosed_image_singleton⟩

lemma Topology.IsEmbedding.wLocalSpace_of_stableUnderSpecialization_range {f : X → Y}
    (hf : IsEmbedding f) (h : StableUnderSpecialization (Set.range f))
    [SpectralSpace X] [WLocalSpace Y] : WLocalSpace X where
  eq_of_specializes {x c c'} hc hc' hxc hxc' :=
    hf.injective (WLocalSpace.eq_of_specializes (hf.isClosed_singleton h hc)
      (hf.isClosed_singleton h hc') (hxc.map hf.continuous) (hxc'.map hf.continuous))
  isClosed_closedPoints := by
    rw [hf.closedPoints_eq_preimage h]
    exact WLocalSpace.isClosed_closedPoints.preimage hf.continuous

lemma StableUnderSpecialization.generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X}
    (hs : StableUnderSpecialization s) :
    StableUnderSpecialization (generalizationHull s) := by
  rw [generalizationHull_eq]
  intro a b hab ha
  obtain ⟨y, hys, hay⟩ := ha
  obtain ⟨c, hc_closed, hyc⟩ := exists_isClosed_specializes y
  obtain ⟨c', hc'_closed, hbc'⟩ := exists_isClosed_specializes b
  obtain rfl := WLocalSpace.eq_of_specializes hc_closed hc'_closed
    (hay.trans hyc) (hab.trans hbc')
  exact ⟨c, hs hyc hys, hbc'⟩

lemma Topology.IsClosedEmbedding.wLocalSpace {f : X → Y} (hf : IsClosedEmbedding f)
    [WLocalSpace Y] : WLocalSpace X :=
  have : SpectralSpace X := hf.spectralSpace
  hf.isEmbedding.wLocalSpace_of_stableUnderSpecialization_range
    hf.isClosedMap.isClosed_range.stableUnderSpecialization

lemma isClosed_generalizationHull_of_wLocalSpace [WLocalSpace X] {s : Set X} (hs : IsClosed s) :
    IsClosed (generalizationHull s) := by
  apply IsClosed.of_isClosed_constructibleTopology
  · obtain ⟨S, hS_sub, hS_eq⟩ := @generalizationHull.eq_sInter_of_isCompact X _ _ s hs.isCompact
    rw [hS_eq]
    apply @isClosed_sInter (WithConstructibleTopology X)
    intro U hU
    obtain ⟨hU_open, hU_compact⟩ := hS_sub hU
    rw [← @isOpen_compl_iff (WithConstructibleTopology X)]
    show @IsOpen (WithConstructibleTopology X) _ Uᶜ
    have : @IsCompact X _ U := hU_compact
    have : @IsClosed X _ Uᶜ := hU_open.isClosed_compl
    exact (by rwa [compl_compl] : @IsCompact X _ (Uᶜ)ᶜ).isOpen_constructibleTopology_of_isClosed this
  · exact hs.stableUnderSpecialization.generalizationHull_of_wLocalSpace

/-- If `X` is w-local, the composition `closedPoints X → X → ConnectedComponents X` is
a homeomorphism. -/
lemma WLocalSpace.isHomeomorph_connectedComponents_closedPoints (X : Type*) [TopologicalSpace X]
    [WLocalSpace X] :
    IsHomeomorph (ConnectedComponents.mk ∘ ((↑) : closedPoints X → X)) := by
  haveI : CompactSpace (closedPoints X) := inferInstance
  haveI : T2Space (ConnectedComponents X) := t2Space_connectedComponent
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨ConnectedComponents.continuous_coe.comp continuous_subtype_val, ?_, ?_⟩
  · -- Injectivity: use clopen separation in closedPoints X
    intro ⟨x, hx⟩ ⟨y, hy⟩ h_eq
    by_contra h_ne
    simp only [Function.comp_apply, Subtype.mk.injEq] at h_eq h_ne
    -- closedPoints X is profinite (spectral with all points closed)
    haveI : SpectralSpace (closedPoints X) := SpectralSpace.of_isClosed X
    have h_closed_singleton : ∀ z : closedPoints X, IsClosed ({z} : Set (closedPoints X)) := by
      intro ⟨z, hz⟩
      convert (mem_closedPoints_iff.mp hz).preimage continuous_subtype_val using 1
      ext ⟨w, hw⟩
      simp [Subtype.ext_iff]
    haveI : T2Space (closedPoints X) :=
      SpectralSpace.t2Space_of_isClosed_singleton h_closed_singleton
    haveI : TotallyDisconnectedSpace (closedPoints X) :=
      SpectralSpace.totallyDisconnectedSpace_of_isClosed_singleton h_closed_singleton
    haveI : LocallyCompactSpace (closedPoints X) := inferInstance
    haveI : TotallySeparatedSpace (closedPoints X) :=
      instTotallySeparatedSpaceOfTotallyDisconnectedSpace
    -- Get clopen separation
    have : Pairwise fun (x1 x2 : closedPoints X) => ∃ U, IsClopen U ∧ x1 ∈ U ∧ x2 ∈ Uᶜ :=
      totallySeparatedSpace_iff_exists_isClopen.mp inferInstance
    have h_ne' : (⟨x, hx⟩ : closedPoints X) ≠ (⟨y, hy⟩ : closedPoints X) := by
      simp [Subtype.mk.injEq, h_ne]
    obtain ⟨U₀, hU₀_clopen, hx_in, hy_out⟩ := this h_ne'
    -- Take generalization hulls to get clopen partition of X
    set U := generalizationHull (Subtype.val '' U₀) with hU_def
    set V := generalizationHull (Subtype.val '' U₀ᶜ) with hV_def
    -- U and V are closed
    have hU_closed : IsClosed U := by
      apply isClosed_generalizationHull_of_wLocalSpace
      exact WLocalSpace.isClosed_closedPoints.isClosedMap_subtype_val U₀ hU₀_clopen.1
    have hV_closed : IsClosed V := by
      apply isClosed_generalizationHull_of_wLocalSpace
      exact WLocalSpace.isClosed_closedPoints.isClosedMap_subtype_val U₀ᶜ hU₀_clopen.compl.1
    -- x ∈ U and y ∈ V
    have hx_U : x ∈ U := by
      rw [mem_generalizationHull_iff]
      exact ⟨x, ⟨⟨x, hx⟩, hx_in, rfl⟩, specializes_rfl⟩
    have hy_V : y ∈ V := by
      rw [mem_generalizationHull_iff]
      exact ⟨y, ⟨⟨y, hy⟩, hy_out, rfl⟩, specializes_rfl⟩
    -- U and V partition X (every closed point is in exactly one)
    have hUV_partition : U ∪ V = Set.univ := by
      ext z
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      obtain ⟨c, hc_closed, hzc⟩ := exists_isClosed_specializes z
      by_cases h : (⟨c, mem_closedPoints_iff.mpr hc_closed⟩ : closedPoints X) ∈ U₀
      · left
        rw [mem_generalizationHull_iff]
        exact ⟨c, ⟨⟨c, mem_closedPoints_iff.mpr hc_closed⟩, h, rfl⟩, hzc⟩
      · right
        rw [mem_generalizationHull_iff]
        exact ⟨c, ⟨⟨c, mem_closedPoints_iff.mpr hc_closed⟩, h, rfl⟩, hzc⟩
    -- U and V are disjoint
    have hUV_disjoint : Disjoint U V := by
      refine Set.disjoint_iff_inter_eq_empty.mpr ?_
      ext z
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hz_U hz_V
      rw [mem_generalizationHull_iff] at hz_U hz_V
      obtain ⟨c₁, ⟨⟨c₁', hc₁'⟩, hc₁_U₀, rfl⟩, hzc₁⟩ := hz_U
      obtain ⟨c₂, ⟨⟨c₂', hc₂'⟩, hc₂_U₀c, rfl⟩, hzc₂⟩ := hz_V
      have : c₁' = c₂' := WLocalSpace.eq_of_specializes hc₁' hc₂' hzc₁ hzc₂
      subst this
      exact hc₂_U₀c hc₁_U₀
    -- U is open (complement of V is closed)
    have hU_open : IsOpen U := by
      have hUc_eq_V : Uᶜ = V := by
        ext z
        constructor
        · intro hz
          simp only [Set.mem_compl_iff] at hz
          have : z ∈ U ∪ V := hUV_partition ▸ Set.mem_univ z
          exact this.resolve_left hz
        · intro hz
          simp only [Set.mem_compl_iff]
          intro hz_U
          have : z ∈ U ∩ V := ⟨hz_U, hz⟩
          rw [Set.disjoint_iff_inter_eq_empty.mp hUV_disjoint] at this
          exact this
      have : IsClosed Uᶜ := hUc_eq_V ▸ hV_closed
      rw [← compl_compl U]
      exact this.isOpen_compl
    -- Derive contradiction: x and y in same connected component but separated by clopen U
    have hU_clopen : IsClopen U := ⟨hU_closed, hU_open⟩
    have hx_cc : connectedComponent x ⊆ U := hU_clopen.connectedComponent_subset hx_U
    have hy_in_cc : y ∈ connectedComponent x := by
      rw [ConnectedComponents.coe_eq_coe] at h_eq
      rw [h_eq]
      exact mem_connectedComponent
    have hy_in_U : y ∈ U := hx_cc hy_in_cc
    have hy_not_in_U : y ∉ U := by
      intro hy_U
      have : y ∈ U ∩ V := ⟨hy_U, hy_V⟩
      rw [Set.disjoint_iff_inter_eq_empty.mp hUV_disjoint] at this
      exact this
    exact hy_not_in_U hy_in_U
  · -- Surjectivity: every connected component contains a closed point
    intro c
    obtain ⟨x, rfl⟩ := Quot.exists_rep c
    obtain ⟨z, hz_closed, hxz⟩ := exists_isClosed_specializes x
    refine ⟨⟨z, mem_closedPoints_iff.mpr hz_closed⟩, ?_⟩
    simp only [Function.comp_apply]
    change ConnectedComponents.mk z = ConnectedComponents.mk x
    rw [ConnectedComponents.coe_eq_coe]
    apply connectedComponent_eq_iff_mem.mpr
    have hx_in : x ∈ connectedComponent x := mem_connectedComponent
    have : closure {x} ⊆ connectedComponent x :=
      closure_minimal (Set.singleton_subset_iff.mpr hx_in) isClosed_connectedComponent
    exact this hxz.mem_closure

/-- The closed points of a w-local space are homeomorphic to the connected components. -/
noncomputable
def WLocalSpace.closedPointsHomeomorph {X : Type*} [TopologicalSpace X] [WLocalSpace X] :
    closedPoints X ≃ₜ ConnectedComponents X :=
  (WLocalSpace.isHomeomorph_connectedComponents_closedPoints X).homeomorph
