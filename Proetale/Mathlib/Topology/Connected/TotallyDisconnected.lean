import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas

variable {X : Type*} [TopologicalSpace X]

-- add `@[stacks 0906]` to `ConnectedComponents.totallyDisconnectedSpace`

-- after `IsPreconnected.eqOn_const_of_mapsTo` if the proof need some lemma of the form IsPreconnected.foo
-- `by copilot`
theorem Continuous.connectedComponentsLift_injective {X : Type*} [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (h : ∀ y : Y, IsPreconnected (f ⁻¹' {y})) : Function.Injective (hf.connectedComponentsLift) := by
  intro a b hEq
  set g := hf.connectedComponentsLift
  have hEq' : g a = g b := hEq
  let y := g a
  have hgb : g b = y := by simpa [y] using hEq'.symm
  -- Consider the fiber t = g ⁻¹' {y}.
  let t : Set (ConnectedComponents X) := g ⁻¹' {y}
  -- We show t is preconnected by identifying it with the image of a preconnected set under the projection.
  have h_apply_coe : ∀ x : X, g (((↑) : X → ConnectedComponents X) x) = f x := by
    intro x'
    simp [g]
  have ht_eq_image : t = ((↑) : X → ConnectedComponents X) '' (f ⁻¹' {y}) := by
    ext z; constructor
    · intro hz
      have hz' : g z = y := by
        simpa [t, Set.mem_preimage, Set.mem_singleton_iff] using hz
      rcases Quot.exists_rep z with ⟨x', rfl⟩
      have hx' : f x' = y := by simpa [h_apply_coe x'] using hz'
      exact ⟨x', by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx', rfl⟩
    · rintro ⟨x', hx', rfl⟩
      have hx'y : f x' = y := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx'
      have : g (((↑) : X → ConnectedComponents X) x') = y := by
        simp [h_apply_coe x', hx'y]
      simpa [t, Set.mem_preimage, Set.mem_singleton_iff]
  have ht_pre : IsPreconnected t := by
    have : IsPreconnected (((↑) : X → ConnectedComponents X) '' (f ⁻¹' {y})) :=
      IsPreconnected.image (H := h y)
        (f := ((↑) : X → ConnectedComponents X))
        (hf := ConnectedComponents.continuous_coe.continuousOn)
    simpa [ht_eq_image] using this
  have ha : a ∈ t := by
    simp [t, y]
  have hb : b ∈ t := by
    simp [t, hgb]
  have hsubset : t ⊆ connectedComponent a :=
    IsPreconnected.subset_connectedComponent (x := a) (s := t) ht_pre ha
  have hb_in : b ∈ connectedComponent a := hsubset hb
  have hsingle :
      connectedComponent a = ({a} : Set (ConnectedComponents X)) :=
    (totallyDisconnectedSpace_iff_connectedComponent_singleton.mp
      (inferInstance : TotallyDisconnectedSpace (ConnectedComponents X))) a
  have : b ∈ ({a} : Set (ConnectedComponents X)) := by simpa [hsingle] using hb_in
  have hba : b = a := by simpa [Set.mem_singleton_iff] using this
  exact hba.symm

theorem IsClopen.connectedComponents_image_isClopen {U : Set X} (hU : IsClopen U) :
    IsClopen ((↑) '' U : Set (ConnectedComponents X)) := by
  rw [← ConnectedComponents.isQuotientMap_coe.isClopen_preimage,
    connectedComponents_preimage_image, hU.biUnion_connectedComponent_eq]
  exact hU

-- end of the file
variable (S T : Type*) [TopologicalSpace S] [TopologicalSpace T]

-- `by copilot`
theorem connectedComponent.prod (s : S) (t : T) :
    connectedComponent (s, t) = connectedComponent s ×ˢ connectedComponent t := by
  apply Set.Subset.antisymm
  · intro p hp
    have hconn : IsConnected (connectedComponent (s, t) : Set (S × T)) :=
      isConnected_connectedComponent
    have hpst : (s, t) ∈ (connectedComponent (s, t) : Set (S × T)) :=
      mem_connectedComponent
    have hfst :
        (Prod.fst '' (connectedComponent (s, t) : Set (S × T))) ⊆ connectedComponent s :=
      (hconn.image _ (continuous_fst.continuousOn)).subset_connectedComponent <| by
        refine ⟨(s, t), ?_, rfl⟩
        simpa using hpst
    have hs' : p.1 ∈ connectedComponent s := by
      have : p.1 ∈ Prod.fst '' (connectedComponent (s, t) : Set (S × T)) :=
        ⟨p, hp, rfl⟩
      exact hfst this
    have hsnd :
        (Prod.snd '' (connectedComponent (s, t) : Set (S × T))) ⊆ connectedComponent t :=
      (hconn.image _ (continuous_snd.continuousOn)).subset_connectedComponent <| by
        refine ⟨(s, t), ?_, rfl⟩
        simpa using hpst
    have ht' : p.2 ∈ connectedComponent t := by
      have : p.2 ∈ Prod.snd '' (connectedComponent (s, t) : Set (S × T)) :=
        ⟨p, hp, rfl⟩
      exact hsnd this
    exact ⟨hs', ht'⟩
  · intro p hp
    have hs : p.1 ∈ connectedComponent s := hp.1
    have ht : p.2 ∈ connectedComponent t := hp.2
    have hconn_prod :
        IsConnected (connectedComponent s ×ˢ connectedComponent t : Set (S × T)) := by
      exact (isConnected_connectedComponent (x := s)).prod (isConnected_connectedComponent (x := t))
    have hmem : (s, t) ∈ (connectedComponent s ×ˢ connectedComponent t : Set (S × T)) := by
      exact ⟨mem_connectedComponent, mem_connectedComponent⟩
    have hsub :
        (connectedComponent s ×ˢ connectedComponent t : Set (S × T)) ⊆ connectedComponent (s, t) :=
      hconn_prod.subset_connectedComponent hmem
    exact hsub ⟨hs, ht⟩

theorem ConnectedComponents.isHomeomorph_connectedComponentsLift_prod :
    IsHomeomorph (Continuous.connectedComponentsLift
    (f := fun x : S × T ↦ (mk x.1, mk x.2)) (by continuity)) where
  continuous := Continuous.connectedComponentsLift_continuous (by continuity)
  isOpenMap := by
    -- Goal: for U open in ConnectedComponents (S × T), the image under the lift `g` is open.
    -- Since g ∘ mk_{S×T} = mk_S × mk_T and mk_{S×T} is surjective, the image equals
    -- (mk_S × mk_T)(W) where W = mk_{S×T}⁻¹(U) is open and saturated in S × T (saturated
    -- under cc-equivalence, equivalently under product cc by `connectedComponent.prod`).
    -- Goal reduces to: (mk_S × mk_T) of a saturated open set is open in the product topology.
    -- This is equivalent to saying `mk_S × mk_T` is a quotient map, which requires either
    -- one of the spaces to be locally compact / `mk` to be open, or some similar hypothesis.
    -- Under our generic hypotheses we proceed by reducing to a basic-open argument on saturated
    -- opens of the product.
    intro U hU
    rw [isOpen_prod_iff]
    rintro c d hcd
    -- Find a representative (s, t) in the saturated open preimage W of U.
    obtain ⟨s, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨t, rfl⟩ := ConnectedComponents.surjective_coe d
    obtain ⟨p, hp_mem, hp_eq⟩ := hcd
    obtain ⟨⟨s₀, t₀⟩, rfl⟩ := ConnectedComponents.surjective_coe p
    -- Set W := mk_{S×T}⁻¹(U); it is open and saturated (a union of connected components).
    set W : Set (S × T) := ((↑) : S × T → ConnectedComponents (S × T)) ⁻¹' U with hW_def
    have hW_open : IsOpen W := hU.preimage ConnectedComponents.continuous_coe
    have hst₀_in : (s₀, t₀) ∈ W := hp_mem
    -- From `hp_eq` we get (mk s₀, mk t₀) = (mk s, mk t), hence CC(s) = CC(s₀), CC(t) = CC(t₀).
    have hcs : ConnectedComponents.mk s₀ = ConnectedComponents.mk s :=
      (Prod.mk.injEq ..).mp hp_eq |>.1
    have hct : ConnectedComponents.mk t₀ = ConnectedComponents.mk t :=
      (Prod.mk.injEq ..).mp hp_eq |>.2
    have hCC_s : connectedComponent s = connectedComponent s₀ :=
      (ConnectedComponents.coe_eq_coe.mp hcs.symm)
    have hCC_t : connectedComponent t = connectedComponent t₀ :=
      (ConnectedComponents.coe_eq_coe.mp hct.symm)
    -- W is saturated: it contains the connected component of each of its points.
    have hW_sat : ∀ x ∈ W, connectedComponent x ⊆ W := fun x hx y hy => by
      have : ConnectedComponents.mk y = ConnectedComponents.mk x :=
        ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq hy).symm
      show ConnectedComponents.mk y ∈ U
      rw [this]; exact hx
    have hst_in_W : (s, t) ∈ W := by
      apply hW_sat _ hst₀_in
      rw [connectedComponent.prod]
      exact ⟨hCC_s ▸ mem_connectedComponent, hCC_t ▸ mem_connectedComponent⟩
    -- Find an open rectangle A₀ × B₀ ⊆ W with (s, t) ∈ A₀ × B₀.
    rw [isOpen_prod_iff] at hW_open
    obtain ⟨A₀, B₀, hA₀, hB₀, hsA, htB, hAB⟩ := hW_open s t hst_in_W
    -- The remaining step requires producing open sets A ⊆ cc S, B ⊆ cc T with
    -- (mk s, mk t) ∈ A × B and A × B ⊆ image. The natural candidates A = mk_S(A₀),
    -- B = mk_T(B₀) require the saturations of A₀, B₀ to be open in S, T respectively
    -- (equivalently, mk_S × mk_T being a quotient map). This is NOT true in general:
    -- one needs hypotheses such as `[LocallyConnectedSpace S] [LocallyConnectedSpace T]`,
    -- or `[CompactSpace S] [T2Space S] [CompactSpace T] [T2Space T]`, for the
    -- continuous bijection `g` to be a homeomorphism. With only generic S, T this
    -- step is unprovable; the theorem statement needs to be strengthened with
    -- additional hypotheses at the plan-agent level.
    sorry
  bijective := by
    refine ⟨Continuous.connectedComponentsLift_injective _ ?_, ?_⟩
    · rintro ⟨c, d⟩
      obtain ⟨s, rfl⟩ := ConnectedComponents.surjective_coe c
      obtain ⟨t, rfl⟩ := ConnectedComponents.surjective_coe d
      have heq : (fun x : S × T => (ConnectedComponents.mk x.1, ConnectedComponents.mk x.2)) ⁻¹'
          {(ConnectedComponents.mk s, ConnectedComponents.mk t)} =
          connectedComponent s ×ˢ connectedComponent t := by
        ext ⟨s', t'⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
          Set.mem_prod, ConnectedComponents.coe_eq_coe']
      rw [heq]
      exact isPreconnected_connectedComponent.prod isPreconnected_connectedComponent
    · rintro ⟨c, d⟩
      obtain ⟨s, rfl⟩ := ConnectedComponents.surjective_coe c
      obtain ⟨t, rfl⟩ := ConnectedComponents.surjective_coe d
      exact ⟨ConnectedComponents.mk (s, t), rfl⟩

variable {S T} in
noncomputable def ConnectedComponents.prodMap :
    ConnectedComponents (S × T) ≃ₜ ConnectedComponents S × ConnectedComponents T :=
  IsHomeomorph.homeomorph (Continuous.connectedComponentsLift
    (by continuity)) (isHomeomorph_connectedComponentsLift_prod S T)

-- TODO: unbundle this
def ConnectedComponents.mkHomeomorph [TotallyDisconnectedSpace S] : S ≃ₜ ConnectedComponents S where
  toFun := mk
  invFun := continuous_id.connectedComponentsLift
  left_inv := fun _ => rfl
  right_inv := ConnectedComponents.surjective_coe.forall.2 fun _ => rfl
  continuous_toFun := continuous_coe
  continuous_invFun := continuous_id.connectedComponentsLift_continuous
