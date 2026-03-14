import Mathlib.Topology.QuasiSeparated

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
-- NOTE: This instance likely requires additional hypotheses (e.g., PrespectralSpace α and
-- PrespectralSpace β, meaning compact opens form a topological basis) to be provable.
-- The standard proof (cf. Stacks Project 0907) relies on compact opens forming a basis:
--   1. Products of compact opens form a basis for α × β (IsTopologicalBasis.prod).
--   2. Intersection of two compact open products: (U₁ × V₁) ∩ (U₂ × V₂) = (U₁ ∩ U₂) × (V₁ ∩ V₂),
--      which is compact by QuasiSeparatedSpace of α and β plus IsCompact.prod.
--   3. Apply QuasiSeparatedSpace.of_isTopologicalBasis.
-- Without PrespectralSpace, compact opens in the product need not be finite unions of compact
-- open rectangles, and the intersection argument cannot be reduced to the factor level.
-- In practice, this instance is only used for spectral spaces where PrespectralSpace holds.
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [QuasiSeparatedSpace β] :
    QuasiSeparatedSpace (α × β) := by
  sorry
  -- Blueprint: thm:spectral-product. Intersection of compact open rectangles is compact.
