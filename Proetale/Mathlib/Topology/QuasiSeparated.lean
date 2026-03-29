import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Spectral.Prespectral

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : β → α}

/-- Quasi-separatedness transfers along homeomorphisms. -/
-- after `quasiSeparatedSpace_iff`
theorem Homeomorph.quasiSeparatedSpace [QuasiSeparatedSpace α] (f : α ≃ₜ β) :
    QuasiSeparatedSpace β where
  inter_isCompact U V hUo hUc hVo hVc := by
    have hc := QuasiSeparatedSpace.inter_isCompact _ _
      (hUo.preimage f.continuous) (f.isClosedEmbedding.isCompact_preimage hUc)
      (hVo.preimage f.continuous) (f.isClosedEmbedding.isCompact_preimage hVc)
    rw [← f.image_preimage (U ∩ V), Set.preimage_inter]
    exact hc.image f.continuous

/-- Quasi-separatedness is invariant under homeomorphisms. -/
theorem Homeomorph.quasiSeparatedSpace_iff (f : α ≃ₜ β) :
    QuasiSeparatedSpace α ↔ QuasiSeparatedSpace β :=
  ⟨fun _ => f.quasiSeparatedSpace, fun _ => f.symm.quasiSeparatedSpace⟩

-- after `NoetherianSpace.to_quasiSeparatedSpace`
-- Stacks Project Tag 0907: The product of spectral spaces is spectral.
-- The proof relies on compact opens forming a basis (PrespectralSpace property).
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [QuasiSeparatedSpace β]
    [PrespectralSpace α] [PrespectralSpace β] :
    QuasiSeparatedSpace (α × β) := by
  let ι := { U : Set α | IsOpen U ∧ IsCompact U } × { V : Set β | IsOpen V ∧ IsCompact V }
  let b : ι → Set (α × β) := fun ⟨U, V⟩ => (U : Set α) ×ˢ (V : Set β)
  refine .of_isTopologicalBasis (ι := ι) (b := b) ?basis ?compact_inter
  · have : range b = image2 (· ×ˢ ·) {U | IsOpen U ∧ IsCompact U} {V | IsOpen V ∧ IsCompact V} := by
      ext s; constructor
      · rintro ⟨⟨⟨U, hU⟩, ⟨V, hV⟩⟩, rfl⟩
        refine ⟨U, hU, V, hV, ?_⟩
        rfl
      · rintro ⟨U, hU, V, hV, rfl⟩
        refine ⟨⟨⟨U, hU⟩, ⟨V, hV⟩⟩, ?_⟩
        rfl
    rw [this]
    exact PrespectralSpace.isTopologicalBasis.prod PrespectralSpace.isTopologicalBasis
  · intro ⟨⟨U₁, hU₁o, hU₁c⟩, ⟨V₁, hV₁o, hV₁c⟩⟩ ⟨⟨U₂, hU₂o, hU₂c⟩, ⟨V₂, hV₂o, hV₂c⟩⟩
    simp [b, Set.prod_inter_prod]
    exact (QuasiSeparatedSpace.inter_isCompact _ _ hU₁o hU₁c hU₂o hU₂c).prod
      (QuasiSeparatedSpace.inter_isCompact _ _ hV₁o hV₁c hV₂o hV₂c)
