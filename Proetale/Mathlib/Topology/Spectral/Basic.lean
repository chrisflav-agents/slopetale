import Mathlib.Topology.Spectral.Basic
import Proetale.Mathlib.Topology.Inseparable
import Proetale.Mathlib.Topology.QuasiSeparated
import Proetale.Mathlib.Topology.Sober
import Proetale.Mathlib.Topology.Spectral.Prespectral


open Topology

variable (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]

-- after `SpectralSpace`
variable {X Y} in
theorem Homeomorph.spectralSpace [SpectralSpace X] (f : X ≃ₜ Y) : SpectralSpace Y :=
  {f.t0Space, f.compactSpace, f.quasiSober, f.quasiSeparatedSpace, f.prespectralSpace with}

variable {X Y} in
theorem Topology.IsClosedEmbedding.spectralSpace {f : X → Y} (hf : IsClosedEmbedding f)
    [SpectralSpace Y] : SpectralSpace X where
  toT0Space := hf.isEmbedding.t0Space
  toQuasiSober := hf.quasiSober
  toQuasiSeparatedSpace := by
    constructor
    intro V1 V2 open1 cpt1 open2 cpt2
    obtain ⟨U1, open1, cpt1, h1⟩ := hf.isOpen_and_isCompact_and_preimage_eq open1 cpt1
    obtain ⟨U2, open2, cpt2, h2⟩ := hf.isOpen_and_isCompact_and_preimage_eq open2 cpt2
    simp [← h1, ← h2, ← Set.preimage_inter]
    apply IsCompact.preimage_of_isOpen hf.isProperMap.isSpectralMap
    · exact QuasiSeparatedSpace.inter_isCompact U1 U2 open1 cpt1 open2 cpt2
    · exact open1.inter open2
  toCompactSpace := hf.compactSpace
  toPrespectralSpace := PrespectralSpace.of_isClosedEmbedding f hf

instance SpectralSpace.of_isClosed [SpectralSpace X] {C : Set X} [IsClosed C] : SpectralSpace C :=
  (IsClosed.isClosedEmbedding_subtypeVal ‹_›).spectralSpace

@[stacks 0907]
instance SpectralSpace.prod [SpectralSpace X] [SpectralSpace Y] : SpectralSpace (X × Y) where
  toCompactSpace := inferInstance
  toT0Space := inferInstance
  toQuasiSober := inferInstance
  toQuasiSeparatedSpace := inferInstance
  toPrespectralSpace := inferInstance

theorem
 generalizationHull.eq_sInter_of_isCompact [SpectralSpace X] {s : Set X} (hs : IsCompact s) :
    ∃ S ⊆ {U : Set X | IsOpen U ∧ IsCompact U}, (generalizationHull s) = ⋂₀ S := by
  set W := generalizationHull s
  use {U : Set X | IsOpen U ∧ IsCompact U ∧ W ⊆ U}
  constructor
  · intro U hU
    exact ⟨hU.1, hU.2.1⟩
  · refine subset_antisymm ?_ ?_
    · intro x hx U ⟨hU_open, hU_compact, hW_sub⟩
      exact hW_sub hx
    · intro x hx
      by_contra hxW
      -- For each y ∈ s, find compact open Uy containing y but not x
      have : ∀ y ∈ s, ∃ Uy, IsOpen Uy ∧ IsCompact Uy ∧ y ∈ Uy ∧ x ∉ Uy := by
        intro y hy
        have hxy : ¬(x ⤳ y) := by
          intro hxy
          apply hxW
          rw [mem_generalizationHull_iff]
          exact ⟨y, hy, hxy⟩
        rw [specializes_iff_mem_closure] at hxy
        have hbasis := PrespectralSpace.isTopologicalBasis (X := X)
        obtain ⟨Uy, ⟨hUy_open, hUy_compact⟩, hy_Uy, hUy_sub⟩ :=
          hbasis.exists_subset_of_mem_open hxy (isOpen_compl_iff.mpr isClosed_closure)
        refine ⟨Uy, hUy_open, hUy_compact, hy_Uy, fun hx_Uy => ?_⟩
        exact hUy_sub hx_Uy (subset_closure (Set.mem_singleton x))
      choose Uy hUy using this
      -- Extract finite subcover
      obtain ⟨t, ht_cover⟩ := hs.elim_finite_subcover
        (fun y : s => Uy y y.2) (fun y => (hUy y y.2).1)
        (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, (hUy y hy).2.2.1⟩)
      -- U := ⋃ y ∈ t, Uy y contradicts hx
      set U := ⋃ y ∈ t, Uy y.1 y.2
      have hU_open : IsOpen U := isOpen_biUnion fun y _ => (hUy y.1 y.2).1
      have hU_compact : IsCompact U := t.finite_toSet.isCompact_biUnion fun y _ => (hUy y.1 y.2).2.1
      have hW_sub : W ⊆ U := fun z hz => by
        rw [mem_generalizationHull_iff] at hz
        obtain ⟨y, hy, hzy⟩ := hz
        exact hzy.mem_open hU_open (ht_cover hy)
      have hx_notin : x ∉ U := fun hx_mem => by
        rw [Set.mem_iUnion] at hx_mem
        obtain ⟨y, hy_mem⟩ := hx_mem
        rw [Set.mem_iUnion] at hy_mem
        obtain ⟨hy_t, hx_Uy⟩ := hy_mem
        exact (hUy y.1 y.2).2.2.2 hx_Uy
      have : x ∈ U := hx U ⟨hU_open, hU_compact, hW_sub⟩
      exact hx_notin this
