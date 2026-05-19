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
-- NOTE: This instance corresponds to Stacks Project Tag 0907, which is stated for **spectral**
-- spaces. The standard proof relies on compact opens forming a topological basis (i.e. a
-- `PrespectralSpace` hypothesis):
--   1. Products of compact opens form a basis for α × β (`IsTopologicalBasis.prod`).
--   2. The intersection of two compact-open rectangles equals
--      `(U₁ ∩ U₂) ×ˢ (V₁ ∩ V₂)`, which is compact by `QuasiSeparatedSpace` of `α` and `β`
--      together with `IsCompact.prod`.
--   3. Apply `QuasiSeparatedSpace.of_isTopologicalBasis`.
-- Without a `PrespectralSpace` hypothesis, compact opens in `α × β` need not be finite unions
-- of compact-open rectangles, and the intersection argument cannot be reduced to the factor
-- level. The statement as given therefore appears to require strengthening (e.g. adding
-- `[PrespectralSpace α] [PrespectralSpace β]`); we leave a scoped `sorry` at the genuine gap
-- and record partial progress below.
instance QuasiSeparatedSpace.prod [QuasiSeparatedSpace α] [QuasiSeparatedSpace β] :
    QuasiSeparatedSpace (α × β) where
  inter_isCompact U V hUo hUc hVo hVc := by
    -- The projections of `U` and `V` are compact open in their respective factors, since
    -- `Prod.fst`/`Prod.snd` are open continuous maps.
    have hπ₁U_open : IsOpen (Prod.fst '' U) := isOpenMap_fst U hUo
    have hπ₁U_cpt : IsCompact (Prod.fst '' U) := hUc.image continuous_fst
    have hπ₁V_open : IsOpen (Prod.fst '' V) := isOpenMap_fst V hVo
    have hπ₁V_cpt : IsCompact (Prod.fst '' V) := hVc.image continuous_fst
    have hπ₂U_open : IsOpen (Prod.snd '' U) := isOpenMap_snd U hUo
    have hπ₂U_cpt : IsCompact (Prod.snd '' U) := hUc.image continuous_snd
    have hπ₂V_open : IsOpen (Prod.snd '' V) := isOpenMap_snd V hVo
    have hπ₂V_cpt : IsCompact (Prod.snd '' V) := hVc.image continuous_snd
    -- Using `QuasiSeparatedSpace` of `α` and `β`, the intersections of these projections are
    -- compact open.
    set K : Set α := (Prod.fst '' U) ∩ (Prod.fst '' V) with hK
    set L : Set β := (Prod.snd '' U) ∩ (Prod.snd '' V) with hL
    have hK_cpt : IsCompact K :=
      QuasiSeparatedSpace.inter_isCompact _ _ hπ₁U_open hπ₁U_cpt hπ₁V_open hπ₁V_cpt
    have hL_cpt : IsCompact L :=
      QuasiSeparatedSpace.inter_isCompact _ _ hπ₂U_open hπ₂U_cpt hπ₂V_open hπ₂V_cpt
    -- The rectangle `K ×ˢ L` is compact open in `α × β` and contains `U ∩ V`.
    have hKL_cpt : IsCompact (K ×ˢ L) := hK_cpt.prod hL_cpt
    have hUV_subset : U ∩ V ⊆ K ×ˢ L := by
      rintro ⟨a, b⟩ ⟨huv₁, huv₂⟩
      refine ⟨⟨⟨(a, b), huv₁, rfl⟩, ⟨(a, b), huv₂, rfl⟩⟩,
              ⟨⟨(a, b), huv₁, rfl⟩, ⟨(a, b), huv₂, rfl⟩⟩⟩
    have hUV_open : IsOpen (U ∩ V) := hUo.inter hVo
    -- At this point we know `U ∩ V` is an open subset contained in the compact set `K ×ˢ L`.
    -- To finish, we would need `U ∩ V` to be **closed** in `K ×ˢ L` (or equivalently, to be a
    -- finite union of compact-open rectangles). Neither follows from the available hypotheses:
    -- without a `PrespectralSpace` structure, a compact open in `α × β` is only a finite union
    -- of *open* rectangles `A × B` (with `A, B` open but not necessarily compact), so the
    -- factor-level quasi-separatedness cannot be invoked. See task_results for an analysis of
    -- this gap; the natural fix is to require `[PrespectralSpace α] [PrespectralSpace β]`.
    sorry
