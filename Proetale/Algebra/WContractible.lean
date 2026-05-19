/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Proetale.Algebra.WLocalization.Ideal
import Proetale.Algebra.WStrictLocalization
import Proetale.Algebra.IndEtale
import Proetale.Algebra.IndZariski
import Proetale.Mathlib.Topology.Connected.TotallyDisconnected
import Proetale.Mathlib.RingTheory.Spectrum.Prime.Topology
import Proetale.Mathlib.Topology.Constructions
import Proetale.Topology.SpectralSpace.ConnectedComponent

/-!
# w-contractible rings

A ring is w-contractible if it is w-strictly-local and the space of connected components of
its prime spectrum is extremally disconnected.

Every w-contractible ring is indeed contractible in the ind-étale topology in the following
sense: If `R` is w-contractible, then every ind-étale faithfully flat map `R →+* S`
has a retraction.

The ind-étale site has enough contractible objects, in the sense that every ring admits a
faithfully flat, ind-étale algebra that is w-contractible.
-/

universe u

/-- A ring `R` is w-contractible if it is w-strictly-local and the space of connected components
of `Spec R` is extremally disconnected. -/
class IsWContractibleRing (R : Type*) [CommRing R] extends IsWStrictlyLocalRing R where
  extremallyDisconnected_connectedComponents :
    ExtremallyDisconnected (ConnectedComponents <| PrimeSpectrum R)

open PrimeSpectrum TopologicalSpace

noncomputable section

namespace WContractification

variable {A : Type u} [CommRing A]

/-!
## The W-Contractification

In this section, we construct w-contractification of w-strictly local rings.
-/

def RestrictClopen (W : Clopens (PrimeSpectrum A)) : Type u :=
  Localization.Away (isIdempotentElemEquivClopens.symm W).val

namespace RestrictClopen

variable {W W₁ W₂ : Clopens (PrimeSpectrum A)}

instance commRing : CommRing (RestrictClopen W) := fast_instance%
  inferInstanceAs <| CommRing <| Localization.Away _

instance algebra : Algebra A (RestrictClopen W) := fast_instance%
  inferInstanceAs <| Algebra A <| Localization.Away _

instance away : IsLocalization.Away (isIdempotentElemEquivClopens.symm W).val
    (RestrictClopen W) :=
  Localization.isLocalization

instance isStandardOpenImmersion : Algebra.IsStandardOpenImmersion A (RestrictClopen W) :=
  ⟨(isIdempotentElemEquivClopens.symm W).val, RestrictClopen.away⟩

lemma val_dvd {W₁ W₂ : Clopens (PrimeSpectrum A)} (h : W₁ ≤ W₂) :
    (isIdempotentElemEquivClopens.symm W₂).val ∣
    (isIdempotentElemEquivClopens.symm W₁).val := by
  use (isIdempotentElemEquivClopens.symm W₁).val
  nth_rw 1 [(isIdempotentElemEquivClopens.symm.monotone h).symm, mul_comm]

open IsLocalization Away in
def map {W₁ W₂ : Clopens (PrimeSpectrum A)} (h : W₁ ≤ W₂) :
    RestrictClopen W₂ →ₐ[A] RestrictClopen W₁ where
  toRingHom := lift (isIdempotentElemEquivClopens.symm W₂).val (isUnit_of_dvd _ (val_dvd h))
  commutes' := fun r => by simp

end RestrictClopen

open scoped CategoryTheory
open CategoryTheory.Limits Topology PrimeSpectrum ConnectedComponents Continuous

section Restriction
variable (T : Set (ConnectedComponents (PrimeSpectrum A)))

def Restriction.diag :
    {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W}ᵒᵖ ⥤ CommAlgCat A where
  obj W := .of A (RestrictClopen W.unop.val)
  map {X Y} f := CommAlgCat.ofHom (RestrictClopen.map f.unop.le)
  map_id X := by
    apply CommAlgCat.hom_ext
    exact Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton
        (Submonoid.powers (isIdempotentElemEquivClopens.symm X.unop.val).val)) _ _
  map_comp {X Y Z} f g := by
    apply CommAlgCat.hom_ext
    exact Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton
        (Submonoid.powers (isIdempotentElemEquivClopens.symm X.unop.val).val)) _ _

def Restriction : Type u :=
  colimit (C := CommAlgCat A) (Restriction.diag T)

namespace Restriction

instance commRing : CommRing (Restriction T) :=
  inferInstanceAs <| CommRing <| colimit (C := CommAlgCat A) (Restriction.diag T)

instance algebra : Algebra A (Restriction T) :=
  inferInstanceAs <| Algebra A <| colimit (C := CommAlgCat A) (Restriction.diag T)

instance indZariski : Algebra.IndZariski A (Restriction T) := by
  rw [Algebra.IndZariski.iff_ind_isLocalIso]
  haveI : Nonempty {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    ⟨⟨⊤, le_top⟩⟩
  haveI : CategoryTheory.IsCofilteredOrEmpty
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    { cone_objs := fun ⟨W₁, h₁⟩ ⟨W₂, h₂⟩ => by
        refine ⟨⟨W₁ ⊓ W₂, le_inf h₁ h₂⟩, CategoryTheory.homOfLE ?_,
          CategoryTheory.homOfLE ?_, trivial⟩
        · exact Subtype.mk_le_mk.mpr inf_le_left
        · exact Subtype.mk_le_mk.mpr inf_le_right
      cone_maps := fun X _ _ _ => ⟨X, CategoryTheory.CategoryStruct.id X, Subsingleton.elim _ _⟩ }
  haveI : CategoryTheory.IsCofiltered
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    { }
  exact ⟨_, inferInstance, inferInstance, .colimit (Restriction.diag T),
    fun W => show Algebra.IsLocalIso A (RestrictClopen W.unop.val) from inferInstance⟩

lemma algebraMap_surjective : Function.Surjective (algebraMap A (Restriction T)) := by
  intro x
  -- The colimit is a filtered colimit since the indexing category is cofiltered
  haveI : Nonempty {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    ⟨⟨⊤, le_top⟩⟩
  haveI : CategoryTheory.IsCofilteredOrEmpty
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    { cone_objs := fun ⟨W₁, h₁⟩ ⟨W₂, h₂⟩ => by
        refine ⟨⟨W₁ ⊓ W₂, le_inf h₁ h₂⟩, CategoryTheory.homOfLE ?_,
          CategoryTheory.homOfLE ?_, trivial⟩
        · exact Subtype.mk_le_mk.mpr inf_le_left
        · exact Subtype.mk_le_mk.mpr inf_le_right
      cone_maps := fun X _ _ _ => ⟨X, CategoryTheory.CategoryStruct.id X, Subsingleton.elim _ _⟩ }
  haveI : CategoryTheory.IsCofiltered
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} := { }
  -- Use that forget preserves filtered colimits to get jointly surjective
  have hc := CategoryTheory.Limits.colimit.isColimit (Restriction.diag T)
  have hc' := CategoryTheory.Limits.isColimitOfPreserves
    (CategoryTheory.forget (CommAlgCat A)) hc
  obtain ⟨⟨j⟩, y, hy⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit hc' x
  -- y is in the underlying type of RestrictClopen j.val
  -- The algebraMap from A to RestrictClopen j.val is surjective (localization at idempotent)
  have hpiece : Function.Surjective (algebraMap A (RestrictClopen j.val)) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (isIdempotentElemEquivClopens.symm j.val).val
      (isIdempotentElemEquivClopens.symm j.val).prop
  obtain ⟨a, ha⟩ := hpiece y
  -- The cocone map sends algebraMap a to algebraMap a
  refine ⟨a, ?_⟩
  -- x = cocone.ι.app (op j) y, and y = algebraMap a, so x = cocone.ι.app (op j) (algebraMap a)
  -- algebraMap A (Restriction T) a = cocone.ι.app (op j) (algebraMap A (RestrictClopen j.val) a)
  -- since the algebra structure on Restriction T restricts through the cocone
  change (CategoryTheory.forget (CommAlgCat A)).map
    (colimit.ι (Restriction.diag T) (Opposite.op j)) y = x at hy
  rw [← ha] at hy
  -- Now need: algebraMap A (Restriction T) a = cocone map applied to (algebraMap A (RestrictClopen j.val) a)
  -- This holds by the fact that the cocone map is an algebra hom
  change algebraMap A (colimit (C := CommAlgCat A) (Restriction.diag T)) a = x
  rw [← hy]
  -- The cocone map is an AlgHom, so it commutes with algebraMap
  let ι_alg : RestrictClopen j.val →ₐ[A] colimit (C := CommAlgCat A) (Restriction.diag T) :=
    (colimit.ι (Restriction.diag T) (Opposite.op j)).hom
  exact (ι_alg.commutes a).symm

variable {T}

-- Helper: the range of Spec(RestrictClopen W) -> Spec(A) equals W as a set.
private lemma restrictClopen_range_eq (W : Clopens (PrimeSpectrum A)) :
    Set.range (PrimeSpectrum.comap (algebraMap A (RestrictClopen W))) =
      (W : Set (PrimeSpectrum A)) := by
  rw [localization_away_comap_range (RestrictClopen W) (isIdempotentElemEquivClopens.symm W).val]
  have h := basicOpen_isIdempotentElemEquivClopens_symm W
  -- h : basicOpen e_W = W.toOpens (as Opens)
  -- Need: (basicOpen e_W : Set _) = (W : Set _)
  -- W : Clopens _, coercion to Set goes through toOpens
  change (basicOpen (isIdempotentElemEquivClopens.symm W).val).carrier = W.toOpens.carrier
  exact congr_arg Opens.carrier h

-- Helper: for each W, ker(A -> A_W) ⊆ ker(A -> colim)
private lemma ker_algebraMap_restrictClopen_le
    {W : Clopens (PrimeSpectrum A)} (hW : ConnectedComponents.mk ⁻¹' T ≤ W) :
    RingHom.ker (algebraMap A (RestrictClopen W)) ≤
      RingHom.ker (algebraMap A (Restriction T)) := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  let ι : RestrictClopen W →ₐ[A] Restriction T :=
    (colimit.ι (Restriction.diag T) (Opposite.op ⟨W, hW⟩)).hom
  calc algebraMap A (Restriction T) a = ι (algebraMap A (RestrictClopen W) a) :=
        (ι.commutes a).symm
    _ = ι 0 := by rw [ha]
    _ = 0 := map_zero _

lemma range_algebraMap_specComap (h : IsClosed T) :
    Set.range (PrimeSpectrum.comap <| algebraMap A (Restriction T)) =
      ConnectedComponents.mk ⁻¹' T := by
  -- Set up filtered indexing category instances
  haveI : Nonempty {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    ⟨⟨⊤, le_top⟩⟩
  haveI : CategoryTheory.IsCofilteredOrEmpty
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
    { cone_objs := fun ⟨W₁, h₁⟩ ⟨W₂, h₂⟩ => by
        refine ⟨⟨W₁ ⊓ W₂, le_inf h₁ h₂⟩, CategoryTheory.homOfLE ?_,
          CategoryTheory.homOfLE ?_, trivial⟩
        · exact Subtype.mk_le_mk.mpr inf_le_left
        · exact Subtype.mk_le_mk.mpr inf_le_right
      cone_maps := fun X _ _ _ => ⟨X, CategoryTheory.CategoryStruct.id X, Subsingleton.elim _ _⟩ }
  haveI : CategoryTheory.IsCofiltered
      {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} := { }
  -- Step 1: range = zeroLocus(ker) by surjectivity
  have hsr : Set.range (comap (algebraMap A (Restriction T))) =
      zeroLocus ↑(RingHom.ker (algebraMap A (Restriction T))) :=
    _root_.range_comap_of_surjective (Restriction T) (algebraMap A (Restriction T))
      (algebraMap_surjective T)
  rw [hsr]
  apply Set.Subset.antisymm
  · -- ⊆ direction: p ∈ zeroLocus(ker(A -> colim)) implies p ∈ mk⁻¹'T
    intro p hp
    -- For each clopen W ⊇ mk⁻¹'T, show p ∈ W
    have hp_in_W : ∀ (W : Clopens (PrimeSpectrum A)),
        ConnectedComponents.mk ⁻¹' T ≤ W → p ∈ (W : Set (PrimeSpectrum A)) := by
      intro W hW
      have hker : RingHom.ker (algebraMap A (RestrictClopen W)) ≤
          RingHom.ker (algebraMap A (Restriction T)) :=
        ker_algebraMap_restrictClopen_le (T := T) hW
      have hzl : zeroLocus (RingHom.ker (algebraMap A (Restriction T)) : Set A) ⊆
          zeroLocus (RingHom.ker (algebraMap A (RestrictClopen W)) : Set A) := by
        apply zeroLocus_anti_mono
        intro x hx
        exact hker hx
      have := hzl hp
      have hrW : Set.range (comap (algebraMap A (RestrictClopen W))) =
          zeroLocus ↑(RingHom.ker (algebraMap A (RestrictClopen W))) :=
        _root_.range_comap_of_surjective (RestrictClopen W) (algebraMap A (RestrictClopen W))
          (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem _
            (isIdempotentElemEquivClopens.symm W).prop)
      rw [← hrW, restrictClopen_range_eq] at this
      exact this
    -- mk⁻¹'T is closed and a union of connected components
    have hclosed : IsClosed (ConnectedComponents.mk ⁻¹' T : Set (PrimeSpectrum A)) :=
      h.preimage ConnectedComponents.continuous_coe
    have hunion : ∃ I : Set (PrimeSpectrum A),
        ⋃ x ∈ I, connectedComponent x = ConnectedComponents.mk ⁻¹' T := by
      refine ⟨ConnectedComponents.mk ⁻¹' T, ?_⟩
      ext x; simp only [Set.mem_iUnion, Set.mem_preimage]; constructor
      · rintro ⟨y, hy, hxy⟩
        have : (x : ConnectedComponents (PrimeSpectrum A)) =
            (y : ConnectedComponents (PrimeSpectrum A)) :=
          ConnectedComponents.coe_eq_coe'.mpr hxy
        rw [this]; exact hy
      · intro hx; exact ⟨x, hx, mem_connectedComponent⟩
    -- By the theorem, mk⁻¹'T = ⋂ of clopens containing it
    obtain ⟨J, hJ⟩ := isClosed_and_iUnion_connectedComponent_eq_iff.1 ⟨hclosed, hunion⟩
    rw [← hJ]
    simp only [Set.iInter_coe_set, Set.mem_iInter, Subtype.forall]
    intro V hV hVJ
    have hTsubV : ConnectedComponents.mk ⁻¹' T ≤
        (⟨V, hV⟩ : {U : Set (PrimeSpectrum A) // IsClopen U}).val := by
      rw [← hJ]
      exact Set.iInter_subset_of_subset ⟨⟨V, hV⟩, hVJ⟩ le_rfl
    exact hp_in_W ⟨V, hV⟩ hTsubV
  · -- ⊇ direction: p ∈ mk⁻¹'T implies p ∈ zeroLocus(ker(A -> colim))
    intro p hp
    rw [mem_zeroLocus]
    intro a ha
    rw [SetLike.mem_coe, RingHom.mem_ker] at ha
    -- ha : algebraMap A (Restriction T) a = 0
    -- We express algebraMap via the cocone map at ⊤
    let top_idx : {W : Clopens (PrimeSpectrum A) // ConnectedComponents.mk ⁻¹' T ≤ W} :=
      ⟨⊤, le_top⟩
    let ι_top := colimit.ι (Restriction.diag T) (Opposite.op top_idx)
    -- ι_top.hom (algebraMap A (RestrictClopen ⊤) a) = ι_top.hom 0 in the colimit
    have heq_in_colim : ι_top.hom (algebraMap A (RestrictClopen ⊤) a) =
        ι_top.hom (0 : RestrictClopen ⊤) :=
      (ι_top.hom.commutes a).trans (ha.trans (map_zero ι_top.hom).symm)
    -- Use that this is a cocone in CommAlgCat, which is concrete.
    -- By filtered colimit property, there exists k and morphisms such that
    -- the images become equal at stage k.
    -- We use the underlying Types colimit.
    have hc := CategoryTheory.Limits.colimit.isColimit (Restriction.diag T)
    have hc' := CategoryTheory.Limits.isColimitOfPreserves
      (CategoryTheory.forget (CommAlgCat A)) hc
    -- Transfer the equality to the Types colimit
    have heq_types : (CategoryTheory.forget (CommAlgCat A)).map ι_top
        (algebraMap A (RestrictClopen ⊤) a) =
      (CategoryTheory.forget (CommAlgCat A)).map ι_top (0 : RestrictClopen ⊤) := heq_in_colim
    -- Use Types.FilteredColimit.isColimit_eq_iff
    have hexists := (CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff
      (Restriction.diag T ⋙ CategoryTheory.forget (CommAlgCat A)) hc').mp heq_types
    obtain ⟨k, f_top_k, g_top_k, hfg⟩ := hexists
    -- f_top_k, g_top_k : op top_idx ⟶ k in the indexing category
    -- hfg : (diag T ⋙ forget).map f_top_k (algebraMap ...) = (diag T ⋙ forget).map g_top_k 0
    -- The map (diag T ⋙ forget).map g_top_k is the underlying function of an algebra hom,
    -- so it sends 0 to 0.
    -- The transition maps are algebra homs, so they preserve 0 and commute with algebraMap
    let W := k.unop.val
    have hW : ConnectedComponents.mk ⁻¹' T ≤ W := k.unop.property
    -- Extract the algebra hom underlying f_top_k
    let φ : RestrictClopen ⊤ →ₐ[A] RestrictClopen W :=
      ((Restriction.diag T).map f_top_k).hom
    -- hfg says: φ (algebraMap A (RestrictClopen ⊤) a) = ψ 0 where ψ is from g_top_k
    -- Since ψ is an algebra hom, ψ 0 = 0
    have hg0 : (Restriction.diag T ⋙ CategoryTheory.forget (CommAlgCat A)).map g_top_k
        (0 : RestrictClopen ⊤) = (0 : RestrictClopen W) := by
      show ((Restriction.diag T).map g_top_k).hom (0 : RestrictClopen ⊤) = 0
      exact map_zero _
    have hf_alg : (Restriction.diag T ⋙ CategoryTheory.forget (CommAlgCat A)).map f_top_k
        (algebraMap A (RestrictClopen ⊤) a) = algebraMap A (RestrictClopen W) a := by
      show φ (algebraMap A (RestrictClopen ⊤) a) = _
      exact φ.commutes a
    -- Combine: algebraMap A (RestrictClopen W) a = 0
    have ha_zero : algebraMap A (RestrictClopen W) a = 0 := by
      rw [← hf_alg, hfg, hg0]
    -- So a ∈ ker(A -> RestrictClopen W)
    have ha_ker : a ∈ RingHom.ker (algebraMap A (RestrictClopen W)) :=
      RingHom.mem_ker.mpr ha_zero
    -- zeroLocus(ker(A -> RestrictClopen W)) = W for any W
    have hzl_eq : zeroLocus ↑(RingHom.ker (algebraMap A (RestrictClopen W))) =
        (W : Set (PrimeSpectrum A)) := by
      rw [← _root_.range_comap_of_surjective (RestrictClopen W)
        (algebraMap A (RestrictClopen W))
        (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem _
          (isIdempotentElemEquivClopens.symm W).prop),
        restrictClopen_range_eq]
    -- p ∈ mk⁻¹'T ⊆ W
    have hp_in_W : p ∈ (W : Set (PrimeSpectrum A)) := hW hp
    -- So p ∈ zeroLocus(ker(A -> RestrictClopen W)), meaning ker ≤ p.asIdeal
    have hker_le : RingHom.ker (algebraMap A (RestrictClopen W)) ≤ p.asIdeal := by
      rw [← SetLike.coe_subset_coe, ← PrimeSpectrum.mem_zeroLocus]
      exact hzl_eq ▸ hp_in_W
    exact SetLike.mem_coe.mp (hker_le ha_ker)

lemma isClosedEmbedding_algebraMap_specComap (_h : IsClosed T) :
    IsClosedEmbedding (PrimeSpectrum.comap <| algebraMap A (Restriction T)) :=
  PrimeSpectrum.isClosedEmbedding_comap_of_surjective (Restriction T)
    (algebraMap A (Restriction T)) (algebraMap_surjective T)

/-- If `A` is w-local and `T ⊆ π₀(Spec A)` is closed, then `Restriction T` is
w-local. This is Stacks 097D. -/
-- Strategy (to be proved in a later round):
-- 1. By `range_algebraMap_specComap` and `isClosedEmbedding_algebraMap_specComap`,
--    `Spec (Restriction T)` identifies with the closed subspace
--    `ConnectedComponents.mk ⁻¹' T ⊆ Spec A`.
-- 2. The set `ConnectedComponents.mk ⁻¹' T` is saturated for the connected-component
--    relation, hence a (closed) union of connected components.
-- 3. By `IsWLocalRing A`, each connected component of `Spec A` contains a unique
--    closed point. The closed points of `Spec (Restriction T)` are precisely the
--    images (under the embedding) of those closed points lying in `mk⁻¹' T`.
-- 4. The closed-points subspace `closedPoints (Spec (Restriction T))` is then a
--    homeomorphic copy of `closedPoints (Spec A) ∩ mk⁻¹' T`, which is closed in
--    `Spec (Restriction T)` and totally disconnected; this verifies the
--    `WLocalSpace` axioms for `Spec (Restriction T)`.
lemma isWLocalRing_of_isClosed [IsWLocalRing A] (h : IsClosed T) :
    IsWLocalRing (Restriction T) :=
  ⟨(isClosedEmbedding_algebraMap_specComap (T := T) h).wLocalSpace⟩

/-- The connected components of `Spec (Restriction T)` are canonically homeomorphic
to `T`, when `T` is closed and `A` is w-local.

This is the identification used in the construction of the w-contractification
(blueprint `def:modify-pi0-profinite`, Stacks 097D / 0983). -/
-- Strategy (to be proved in a later round):
-- 1. Identify `Spec (Restriction T)` with the closed subspace
--    `mk ⁻¹' T ⊆ Spec A` via `isClosedEmbedding_algebraMap_specComap`.
-- 2. The connected components of `mk ⁻¹' T` (with the subspace topology) are
--    in canonical bijection with `T` itself, because `mk ⁻¹' T` is a union of
--    connected components of `Spec A` (since `T` is closed).
-- 3. Combine to get the desired homeomorphism.
def connectedComponentsEquiv [IsWLocalRing A] (h : IsClosed T) :
    ConnectedComponents (PrimeSpectrum (Restriction T)) ≃ₜ T := by
  set f : PrimeSpectrum (Restriction T) → PrimeSpectrum A :=
    PrimeSpectrum.comap (algebraMap A (Restriction T)) with hf_def
  have hce : IsClosedEmbedding f := isClosedEmbedding_algebraMap_specComap (T := T) h
  have hrange : Set.range f = ConnectedComponents.mk ⁻¹' T :=
    range_algebraMap_specComap (T := T) h
  have hf_cont : Continuous f := hce.continuous
  -- The continuous function PrimeSpectrum (Restriction T) → T, sending q to mk (f q).
  have hmem : ∀ q, ConnectedComponents.mk (f q) ∈ T := fun q => by
    have : f q ∈ Set.range f := Set.mem_range_self q
    rw [hrange] at this; exact this
  let φ : PrimeSpectrum (Restriction T) → T :=
    fun q => ⟨ConnectedComponents.mk (f q), hmem q⟩
  have hφ_cont : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    exact ConnectedComponents.continuous_coe.comp hf_cont
  -- ψ is the lift to connected components.
  let ψ : ConnectedComponents (PrimeSpectrum (Restriction T)) → T :=
    Continuous.connectedComponentsLift hφ_cont
  have hψ_cont : Continuous ψ := Continuous.connectedComponentsLift_continuous _
  -- Instances we need.
  haveI : IsWLocalRing (Restriction T) := isWLocalRing_of_isClosed (T := T) h
  -- Surjectivity.
  have hsurj : Function.Surjective ψ := by
    rintro ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe t
    have hx_range : x ∈ Set.range f := by rw [hrange]; exact ht
    obtain ⟨q, hq⟩ := hx_range
    refine ⟨ConnectedComponents.mk q, ?_⟩
    show φ q = ⟨ConnectedComponents.mk x, ht⟩
    simp [φ, hq]
  -- Injectivity via Continuous.connectedComponentsLift_injective.
  have hinj : Function.Injective ψ := by
    apply Continuous.connectedComponentsLift_injective hφ_cont
    rintro ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe t
    -- φ ⁻¹' {⟨mk x, ht⟩} = f ⁻¹' (mk ⁻¹' {mk x}) = f ⁻¹' connectedComponent x.
    have hfib_eq : φ ⁻¹' {⟨ConnectedComponents.mk x, ht⟩} =
        f ⁻¹' connectedComponent x := by
      ext q
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk.injEq, φ]
      rw [← connectedComponents_preimage_singleton, Set.mem_preimage,
        Set.mem_singleton_iff]
    rw [hfib_eq]
    -- connectedComponent x ⊆ range f (since mk is constant on connected components
    -- and mk x = t ∈ T means the whole connected component sits in mk⁻¹' T).
    have hcc_sub : (connectedComponent x : Set (PrimeSpectrum A)) ⊆ Set.range f := by
      rw [hrange]
      intro y hy
      have : ConnectedComponents.mk y = ConnectedComponents.mk x :=
        ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq hy).symm
      show ConnectedComponents.mk y ∈ T
      rw [this]; exact ht
    have himg : f '' (f ⁻¹' (connectedComponent x : Set (PrimeSpectrum A))) =
        connectedComponent x :=
      Set.image_preimage_eq_of_subset hcc_sub
    have hpre_img : IsPreconnected
        (f '' (f ⁻¹' (connectedComponent x : Set (PrimeSpectrum A)))) := by
      rw [himg]; exact isPreconnected_connectedComponent
    exact hce.isInducing.isPreconnected_image.mp hpre_img
  -- Bundle as equiv, then upgrade to homeomorphism.
  let e : ConnectedComponents (PrimeSpectrum (Restriction T)) ≃ T :=
    Equiv.ofBijective ψ ⟨hinj, hsurj⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := e) hψ_cont

end Restriction

end Restriction

section Pullback

variable {T : Type*} [TopologicalSpace T] [CompactSpace T] (S : DiscreteQuotient T)
  (f : C(T, ConnectedComponents (PrimeSpectrum A)))

def Z := Set.range fun t ↦ connectedComponentsMap (PrimeSpectrum.continuous_sigmaToPi fun _ ↦ A) <|
  connectedComponentsMap Prod.continuous_toSigma (prodMap.symm (mkHomeomorph _ (S.proj t), f t))

def Pullback := Restriction (Z S f)

namespace Pullback

instance commRing : CommRing (Pullback S f) :=
  inferInstanceAs <| CommRing <| Restriction (Z S f)

instance algebra' : Algebra (S → A) (Pullback S f) :=
  inferInstanceAs <| Algebra (S → A) <| Restriction (Z S f)

instance algebra : Algebra A (Pullback S f) := Algebra.compHom _ (Pi.ringHom fun _ : S ↦ RingHom.id A)

instance isScalarTower : IsScalarTower A (S → A) (Pullback S f) :=
  .of_algebraMap_eq' rfl

variable {T : Type u} [TopologicalSpace T] [CompactSpace T] (S : DiscreteQuotient T)
  (f : C(T, ConnectedComponents (PrimeSpectrum A)))

instance indZariski' : Algebra.IndZariski (S → A) (Pullback S f) :=
  inferInstanceAs <| Algebra.IndZariski (S → A) <| Restriction (Z S f)

instance indZariski : Algebra.IndZariski A (Pullback S f) :=
  .trans A (S → A) (Pullback S f)

theorem bijectiveOnStalks_algebraMap : (algebraMap A (Pullback S f)).BijectiveOnStalks :=
  Algebra.IndZariski.bijectiveOnStalks_algebraMap _ _

-- Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting for 1.123

end Pullback

end Pullback

end WContractification

end

variable {R : Type u} [CommRing R]

/--
Let `R` be a w-contractible ring and `I` an ideal of `R` cutting out the set `X^c` of closed
points in `Spec R`. Then every faithfully flat ind-étale map `R →+* S` with `S` w-local and
whose closed points of `Spec S` are exactly `V(IB)` has a retraction.
-/
-- An ind-etale map from a w-strictly-local ring to a w-local ring (with matching closed points)
-- is bijective on stalks. This corresponds to the first step of
-- thm:ind-etale-plus-c-has-retraction-if-w-contractible in the blueprint.
-- The proof uses thm:ind-etale-strictly-henselian-localization-isom: if A is a strictly
-- Henselian local ring and A -> B is ind-etale, then A -> B_n is an isomorphism for any
-- maximal ideal n lying over the maximal ideal of A.
private lemma bijectiveOnStalks_of_indEtale_wStrictlyLocal [IsWStrictlyLocalRing R]
    {I : Ideal R} (hI : zeroLocus I = closedPoints (PrimeSpectrum R))
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.IndEtale R S]
    [IsWLocalRing S]
    (hS : zeroLocus (I.map (algebraMap R S)) = closedPoints (PrimeSpectrum S)) :
    (algebraMap R S).BijectiveOnStalks := by
  -- For each prime q of S, need to show localRingHom (q.comap f) q f rfl is bijective.
  -- The key case is when q is maximal (lies in V(IS) = closedPoints).
  -- Then q.comap f lies in V(I) = closedPoints(Spec R), so q.comap f is maximal.
  -- Since R is w-strictly-local, R_(comap q) is strictly Henselian.
  -- Since R → S is ind-étale, the stalk map R_(comap q) → S_q is ind-étale
  -- and hence an isomorphism (thm:ind-etale-strictly-henselian-localization-isom).
  -- For non-maximal primes q, BijectiveOnStalks follows by passing through the
  -- unique closed point that q specializes to (using w-local structure).
  sorry

-- If R is w-local with extremally disconnected pi_0(Spec R) and R -> S is faithfully flat,
-- bijective on stalks, with S w-local and matching closed points, then R -> S has a retraction.
-- This corresponds to thm:ff-identifies-local-rings-plus-c-has-retraction-if in the blueprint.
-- Proof outline (Stacks 097V):
-- 1. V(IS) → V(I) is surjective (from Module.FaithfullyFlat → Spec.comap surjective,
--    restricted to V(IS); preimage of V(I) under Spec.comap equals V(IS) by hS+hI).
-- 2. V(I) ≅ closedPoints(Spec R) ≅ π₀(Spec R) via
--    `WLocalSpace.isHomeomorph_connectedComponents_closedPoints`, hence is extremally
--    disconnected and (CompHaus) projective. Lift the surjection in (1) to a section
--    σ : V(I) → V(IS).
-- 3. T := image of σ in π₀(Spec S) (via the V(IS) ≅ π₀(Spec S) homeomorphism).
--    By construction T is closed and homeomorphic to π₀(Spec R).
-- 4. Form `B_T := WContractification.Restriction T` (defined in this file).
--    The map S → B_T is surjective and ind-Zariski; B_T is w-local (Stacks 097D);
--    `range_algebraMap_specComap` (already proved here) gives Spec(B_T) → Spec S has
--    range = mk⁻¹ T.
-- 5. The composition R → S → B_T is bijective by `RingHom.IsWLocal.bijective_of_bijective`
--    (FULLY PROVED in `Proetale/Algebra/WLocal.lean:95`):
--    • bijective on stalks: hbij ∘ (ind-Zariski → BijectiveOnStalks);
--    • bijective on π₀: by step (3), T ≃ π₀(Spec R) and π₀(Spec B_T) ≃ T.
-- 6. The inverse R ≃ B_T composed with S → B_T gives the retraction S → R.
-- BLOCKERS for this Lean proof:
--   (a) `IsWLocalRing (Restriction T)` — declared as
--       `WContractification.Restriction.isWLocalRing_of_isClosed`; proof sorry.
--   (b) `Algebra.IndZariski.bijectiveOnStalks_algebraMap` (sorried in IndZariski.lean).
--   (c) Projectivity of extremally disconnected CompHaus / lift of section.
--   (d) Identification `π₀(Spec (Restriction T)) ≃ T` — declared as
--       `WContractification.Restriction.connectedComponentsEquiv`; proof sorry.
private lemma exists_retraction_of_bijectiveOnStalks [IsWLocalRing R]
    (hED : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R)))
    {I : Ideal R} (hI : zeroLocus I = closedPoints (PrimeSpectrum R))
    {S : Type u} [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] [IsWLocalRing S]
    (hS : zeroLocus (I.map (algebraMap R S)) = closedPoints (PrimeSpectrum S))
    (hbij : (algebraMap R S).BijectiveOnStalks) :
    ∃ (f : S →+* R), f.comp (algebraMap R S) = RingHom.id R := by
  -- Blueprint: thm:ff-identifies-local-rings-plus-c-has-retraction-if (Stacks 097V).
  -- ============================================================================
  -- Step 1: faithful flatness ⇒ Spec.comap is surjective, and so the induced
  -- map on connected-components π₀(Spec S) → π₀(Spec R) is also surjective.
  -- ============================================================================
  have hsurj_spec : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  have hcont_comap : Continuous (PrimeSpectrum.comap (algebraMap R S)) :=
    PrimeSpectrum.continuous_comap _
  have hsurj_pi0 : Function.Surjective hcont_comap.connectedComponentsMap :=
    hcont_comap.connectedComponentsMap_surjective hsurj_spec
  -- ============================================================================
  -- Step 2: pick a continuous section σ via extremal disconnectedness.
  -- ============================================================================
  haveI hED' : ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R)) := hED
  have hproj : CompactT2.Projective (ConnectedComponents (PrimeSpectrum R)) :=
    @CompactT2.ExtremallyDisconnected.projective _ _ hED' _ _
  obtain ⟨σ, hσ_cont, hσ_section⟩ :=
    hproj (f := id) (g := hcont_comap.connectedComponentsMap)
      continuous_id hcont_comap.connectedComponentsMap_continuous hsurj_pi0
  -- σ : π₀(Spec R) → π₀(Spec S), continuous; comap∘σ = id, hence σ is injective.
  have hσ_inj : Function.Injective σ := by
    intro x y hxy
    have := congrArg hcont_comap.connectedComponentsMap hxy
    have hx : hcont_comap.connectedComponentsMap (σ x) = x := congrFun hσ_section x
    have hy : hcont_comap.connectedComponentsMap (σ y) = y := congrFun hσ_section y
    rw [hx, hy] at this; exact this
  -- ============================================================================
  -- Step 3: T := Set.range σ is a closed subset of π₀(Spec S), with σ : π₀(Spec R) ≃ₜ T.
  -- ============================================================================
  set T : Set (ConnectedComponents (PrimeSpectrum S)) := Set.range σ with hT_def
  have hT_closed : IsClosed T := by
    rw [hT_def, ← Set.image_univ]
    exact (isCompact_univ.image hσ_cont).isClosed
  -- σ as a continuous bijection π₀(Spec R) → T.
  let σ' : ConnectedComponents (PrimeSpectrum R) → T :=
    fun x => ⟨σ x, x, rfl⟩
  have hσ'_cont : Continuous σ' := Continuous.subtype_mk hσ_cont _
  have hσ'_bij : Function.Bijective σ' := by
    refine ⟨fun x y hxy => hσ_inj (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨t, x, rfl⟩
    exact ⟨x, rfl⟩
  -- Convert to a homeomorphism σ' : π₀(Spec R) ≃ₜ T (compact-to-T2).
  haveI : T2Space T := inferInstance
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hT_closed.isCompact
  let σ_homeo : ConnectedComponents (PrimeSpectrum R) ≃ₜ T :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective σ' hσ'_bij) hσ'_cont
  -- ============================================================================
  -- Step 4: form B := WContractification.Restriction (A := S) T.
  -- ============================================================================
  set B : Type u := WContractification.Restriction (A := S) T with hB_def
  letI : CommRing B := WContractification.Restriction.commRing T
  letI : Algebra S B := WContractification.Restriction.algebra T
  -- B is w-local (Stacks 097D).
  haveI hB_wlocal : IsWLocalRing B :=
    WContractification.Restriction.isWLocalRing_of_isClosed (T := T) hT_closed
  -- B is ind-Zariski over S; hence bijective on stalks.
  haveI hSB_indZ : Algebra.IndZariski S B := WContractification.Restriction.indZariski T
  have hSB_bij : (algebraMap S B).BijectiveOnStalks :=
    Algebra.IndZariski.bijectiveOnStalks_algebraMap _ _
  -- S → B is surjective.
  have hSB_surj : Function.Surjective (algebraMap S B) :=
    WContractification.Restriction.algebraMap_surjective T
  -- π₀(Spec B) ≃ₜ T (the construction at Restriction.connectedComponentsEquiv).
  let ccBeq : ConnectedComponents (PrimeSpectrum B) ≃ₜ T :=
    WContractification.Restriction.connectedComponentsEquiv (T := T) hT_closed
  -- Range of Spec(S → B) is `mk⁻¹ T`.
  have hSB_range : Set.range (PrimeSpectrum.comap <| algebraMap S B) =
      ConnectedComponents.mk ⁻¹' T :=
    WContractification.Restriction.range_algebraMap_specComap (T := T) hT_closed
  -- The closed embedding Spec B → Spec S.
  have hSB_clEmb : Topology.IsClosedEmbedding (PrimeSpectrum.comap (algebraMap S B)) :=
    WContractification.Restriction.isClosedEmbedding_algebraMap_specComap (T := T) hT_closed
  -- ============================================================================
  -- Step 5: build R-algebra structure on B via the composition R → S → B.
  -- ============================================================================
  letI algRB : Algebra R B := Algebra.compHom B (algebraMap R S)
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  -- The composed algebraMap R B equals (algebraMap S B).comp (algebraMap R S).
  have halgRB_eq : (algebraMap R B) = (algebraMap S B).comp (algebraMap R S) := rfl
  -- R → B is bijective on stalks (composition of bijective-on-stalks maps).
  have hRB_bij : (algebraMap R B).BijectiveOnStalks := by
    rw [halgRB_eq]; exact hbij.comp hSB_bij
  -- The induced map π₀(Spec B) → π₀(Spec S).
  have hcont_SB : Continuous (PrimeSpectrum.comap (algebraMap S B)) :=
    PrimeSpectrum.continuous_comap _
  -- The induced map π₀(Spec B) → π₀(Spec R) is the composition.
  have hcont_RB : Continuous (PrimeSpectrum.comap (algebraMap R B)) :=
    PrimeSpectrum.continuous_comap _
  -- ============================================================================
  -- Step 6: the connected-components map π₀(Spec B) → π₀(Spec R) is bijective.
  -- π₀(Spec B) ≃ₜ T  (via ccBeq);  π₀(Spec R) ≃ₜ T via σ_homeo.
  -- The composition π₀(B) → π₀(S) → π₀(R) factors as
  --   π₀(B) →(ccBeq)→ T →(σ_homeo.symm)→ π₀(R).
  -- ============================================================================
  -- The crucial identification: ccBeq.symm ∘ σ_homeo = id on π₀(R)
  -- (i.e., the maps agree by uniqueness of the section σ).
  -- We show: the composed map π₀(B) → π₀(R) is `σ_homeo.symm ∘ ccBeq`,
  -- which is the composition of two homeomorphisms, hence bijective.
  --
  -- The proof of this identification follows from:
  -- 1. Spec B → Spec S is the closed embedding into `mk⁻¹ T`.
  -- 2. mk : Spec S → π₀(S) restricted to `mk⁻¹ T` factors through T.
  -- 3. Composing with Spec(S → R) i.e. mk gives π₀(S) → π₀(R) via connectedComponentsMap.
  -- 4. By definition of σ, hcont_comap.connectedComponentsMap ∘ σ = id.
  -- Hence the composition `π₀(B) →(ccBeq)→ T →(σ_homeo.symm)→ π₀(R)` agrees with
  -- the natural map `π₀(B) → π₀(R)` induced by Spec(R → B).
  have hRB_pi0_bij : Function.Bijective hcont_RB.connectedComponentsMap := by
    -- Plan: identify hcont_RB.connectedComponentsMap with σ_homeo.symm ∘ Subtype.val ∘ ccBeq
    -- (where Subtype.val : T → π₀(S) is the inclusion). Wait, we need π₀(R) on the right,
    -- so the right map is σ_homeo.symm : T → π₀(R), giving a composition that is bijective.
    --
    -- Concretely: hcont_RB.connectedComponentsMap = σ_homeo.symm ∘ ccBeq, viewed via the
    -- inclusion T ↪ π₀(S) and the section equation. This sub-identification is the
    -- technical heart of Stacks 09AZ step (3); it requires careful pointwise verification.
    -- We bundle it as a separate `have` and complete the bijectivity afterwards.
    -- Auxiliary: the inclusion T ↪ π₀(S) composed with ccBeq equals hcont_SB.cc_map.
    have hccBeq_val : ∀ b, ((ccBeq b : T) : ConnectedComponents (PrimeSpectrum S)) =
        hcont_SB.connectedComponentsMap b := by
      intro b
      obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe b
      -- The lift definition of `connectedComponentsEquiv` reduces ccBeq (mk p) to
      -- ⟨mk (comap S→B p), _⟩. Hence its `.val` is mk (comap S→B p), which is also
      -- hcont_SB.cc_map (mk p) by definition.
      rfl
    have hidentify : ∀ (b : ConnectedComponents (PrimeSpectrum B)),
        hcont_RB.connectedComponentsMap b = (σ_homeo.symm (ccBeq b) : _) := by
      intro b
      -- Apply σ_homeo on both sides.
      apply σ_homeo.injective
      rw [σ_homeo.apply_symm_apply]
      obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe b
      -- σ_homeo (cc_map_RB (mk p)) and ccBeq (mk p), both in T.
      -- It suffices to compare their values in π₀(S).
      apply Subtype.ext
      -- LHS.val = σ (cc_map_RB (mk p)) by def of σ_homeo.
      show σ (hcont_RB.connectedComponentsMap (ConnectedComponents.mk p)) =
        ((ccBeq (ConnectedComponents.mk p) : T) : ConnectedComponents (PrimeSpectrum S))
      rw [hccBeq_val]
      -- Now: σ (cc_map_RB (mk p)) = cc_map_SB (mk p).
      -- Use: σ ∘ (cc_map_comap ∘ mk) = mk on the image, via hσ_section.
      -- Specifically, cc_map_SB (mk p) ∈ T = range σ, with preimage cc_map_RB (mk p).
      have h_mk_in_T : hcont_SB.connectedComponentsMap (ConnectedComponents.mk p) ∈ T := by
        show ConnectedComponents.mk (PrimeSpectrum.comap (algebraMap S B) p) ∈ T
        have hmem : PrimeSpectrum.comap (algebraMap S B) p ∈
            Set.range (PrimeSpectrum.comap (algebraMap S B)) := ⟨p, rfl⟩
        rw [hSB_range] at hmem
        exact hmem
      obtain ⟨y, hy⟩ := h_mk_in_T
      -- cc_map_RB (mk p) = cc_map_comap (cc_map_SB (mk p)) = cc_map_comap (σ y) = y.
      have hRB_eq : hcont_RB.connectedComponentsMap (ConnectedComponents.mk p) = y := by
        have hcc_RB :
            hcont_RB.connectedComponentsMap (ConnectedComponents.mk p) =
              hcont_comap.connectedComponentsMap
                (hcont_SB.connectedComponentsMap (ConnectedComponents.mk p)) := rfl
        rw [hcc_RB, ← hy]
        exact congrFun hσ_section y
      rw [hRB_eq, hy]
    constructor
    · -- Injectivity: composition of injections.
      intro x y hxy
      rw [hidentify, hidentify] at hxy
      have h2 : ccBeq x = ccBeq y := σ_homeo.symm.injective hxy
      exact ccBeq.injective h2
    · -- Surjectivity: composition of surjections.
      intro r
      refine ⟨ccBeq.symm (σ_homeo r), ?_⟩
      rw [hidentify]
      have hcc : ccBeq (ccBeq.symm (σ_homeo r)) = σ_homeo r := ccBeq.apply_symm_apply _
      rw [hcc]
      exact σ_homeo.symm_apply_apply r
  -- ============================================================================
  -- Step 7: R → B is a w-local map (closed points map to closed points).
  -- We use that closed points of B are precisely those whose connected components
  -- correspond (via ccBeq) to elements of T, and that the composed map to π₀(R)
  -- is a bijection by step 6.
  -- ============================================================================
  have hRB_wLocal : (algebraMap R B).IsWLocal := by
    -- Use the maximal-ideal characterization of `IsWLocal`.
    rw [RingHom.isWLocal_iff_isMaximal_of_isMaximal]
    intro m hm_max
    -- {m} closed in Spec B (since m is maximal in B).
    let p_m : PrimeSpectrum B := ⟨m, hm_max.isPrime⟩
    have hp_m_closed : IsClosed ({p_m} : Set (PrimeSpectrum B)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal p_m).mpr hm_max
    -- Push forward via the closed embedding Spec B ↪ Spec S.
    let q : PrimeSpectrum S := PrimeSpectrum.comap (algebraMap S B) p_m
    have hq_closed : IsClosed ({q} : Set (PrimeSpectrum S)) := by
      have himg : (PrimeSpectrum.comap (algebraMap S B)) '' ({p_m} : Set _) = {q} :=
        Set.image_singleton
      rw [← himg]; exact hSB_clEmb.isClosedMap _ hp_m_closed
    -- closedPoints(Spec S) = V(IS), so q ∈ V(IS).
    have hq_in_clS : q ∈ closedPoints (PrimeSpectrum S) := mem_closedPoints_iff.mpr hq_closed
    have hq_in_VIS : q ∈ zeroLocus (I.map (algebraMap R S) : Set S) := by
      rw [hS]; exact hq_in_clS
    -- Hence I ≤ q.asIdeal.comap (algebraMap R S).
    have hI_sub : I ≤ q.asIdeal.comap (algebraMap R S) := by
      have hISq : I.map (algebraMap R S) ≤ q.asIdeal := by
        rw [PrimeSpectrum.mem_zeroLocus] at hq_in_VIS
        rwa [← SetLike.coe_subset_coe]
      exact Ideal.map_le_iff_le_comap.mp hISq
    -- m.comap (algebraMap R B) factors through q (under the comp).
    have hcomap_eq : m.comap (algebraMap R B) = q.asIdeal.comap (algebraMap R S) := by
      show m.comap ((algebraMap S B).comp (algebraMap R S)) = _
      rw [← Ideal.comap_comap]; rfl
    -- m.comap (algebraMap R B) is in V(I) = closed points of R.
    haveI : (m.comap (algebraMap R B)).IsPrime := Ideal.IsPrime.comap _
    have hp_in : (⟨m.comap (algebraMap R B), inferInstance⟩ : PrimeSpectrum R)
        ∈ zeroLocus (I : Set R) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro x hxI
      have : x ∈ q.asIdeal.comap (algebraMap R S) := hI_sub hxI
      show x ∈ m.comap (algebraMap R B)
      rw [hcomap_eq]; exact this
    have := hI ▸ hp_in
    rw [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal] at this
    exact this
  -- ============================================================================
  -- Step 8: apply bijective_of_bijective to conclude R → B is bijective as rings.
  -- ============================================================================
  have hRB_bijective : Function.Bijective (algebraMap R B) :=
    RingHom.IsWLocal.bijective_of_bijective hRB_wLocal hRB_bij hRB_pi0_bij
  -- ============================================================================
  -- Step 9: extract the inverse and compose with S → B.
  -- ============================================================================
  let e : R ≃+* B := RingEquiv.ofBijective (algebraMap R B) hRB_bijective
  refine ⟨(e.symm : B →+* R).comp (algebraMap S B), ?_⟩
  ext r
  show e.symm ((algebraMap S B) ((algebraMap R S) r)) = r
  have : (algebraMap S B) ((algebraMap R S) r) = (algebraMap R B) r := rfl
  rw [this]
  exact e.symm_apply_apply r

theorem IsWContractibleRing.exists_retraction_of_zeroLocus_map_eq_closedPoints [IsWContractibleRing R]
    {I :Ideal R} (hI : zeroLocus I = closedPoints (PrimeSpectrum R)) {S : Type u} [CommRing S]
    [Algebra R S] [Algebra.IndEtale R S] [Module.FaithfullyFlat R S] [IsWLocalRing S]
    (hS : zeroLocus (I.map (algebraMap R S)) = closedPoints (PrimeSpectrum S)) :
    ∃ (f : S →+* R), f.comp (algebraMap R S) = RingHom.id R := by
  -- Step 1: R → S is bijective on stalks (identifies local rings).
  -- This uses that R is w-strictly local (stalks at maximal ideals are strictly Henselian)
  -- and S is ind-étale over R with matching closed points.
  have hbij : (algebraMap R S).BijectiveOnStalks :=
    bijectiveOnStalks_of_indEtale_wStrictlyLocal hI hS
  -- Step 2: Apply the retraction theorem for faithfully flat maps that identify local rings,
  -- using that π₀(Spec R) is extremally disconnected.
  exact exists_retraction_of_bijectiveOnStalks
    (IsWContractibleRing.extremallyDisconnected_connectedComponents) hI hS hbij

variable (R)

/-- If `R` is w-contractible, every faithfully flat, ind-étale map `R →+* S` has a retraction. -/
theorem IsWContractibleRing.exists_retraction [IsWContractibleRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.IndEtale R S] [Module.FaithfullyFlat R S] :
    ∃ (f : S →+* R), f.comp (algebraMap R S) = RingHom.id R := by
  let I := vanishingIdeal (closedPoints (PrimeSpectrum R))
  have hI : zeroLocus I = closedPoints (PrimeSpectrum R) := by
    rw [zeroLocus_vanishingIdeal_eq_closure, IsClosed.closure_eq (IsWLocalRing.wLocalSpace_primeSepectrum.isClosed_closedPoints)]
  let S' := (I.map (algebraMap R S)).WLocalization
  have : Module.FaithfullyFlat R S' :=
    Ideal.WLocalization.faithfullyFlat_map_algebraMap hI (fun _ _ ↦ inferInstance)
  have : Algebra.IndEtale R S' := Algebra.IndEtale.trans R S S'
  have : zeroLocus (I.map (algebraMap R S')) = closedPoints (PrimeSpectrum S') :=
    Ideal.WLocalization.algebraMap_specComap_preimage_closedPoints_eq hI (fun _ _ ↦ inferInstance)
  obtain ⟨g, hg⟩ := IsWContractibleRing.exists_retraction_of_zeroLocus_map_eq_closedPoints hI this
  use g.comp (algebraMap S S')
  simp only [RingHom.comp_assoc]
  exact hg

/-!
### The w-contractification of a w-strictly-local ring

The main result `exists_isWContractibleRing_of_isWStrictlyLocal` constructs an ind-Zariski,
faithfully flat, w-contractible cover of any w-strictly-local ring. The proof follows the
blueprint (thm:ind-etale-w-contractible-cover-of-w-strictly-local, Stacks 0983):

1. By Gleason's theorem (`StoneCech.projective` + `CompactT2.Projective.extremallyDisconnected`),
   choose an extremally disconnected profinite space `T` (= `Ultrafilter (pi_0(Spec R))`)
   with a surjection `T -> pi_0(Spec R)`.
2. By the Pullback construction (`WContractification.Pullback`), taking the colimit over
   all discrete quotients of `T`, we get a ring `D` that is ind-Zariski and faithfully flat
   over `R`, with `pi_0(Spec D) = T` (hence extremally disconnected).
3. The local rings of `D` at maximal ideals are isomorphic to the corresponding local rings
   of `R` (by `Algebra.IndZariski.bijectiveOnStalks_algebraMap`), hence strictly Henselian.
4. Therefore `D` is w-contractible.

The construction of the "profinite Pullback" (colimit of `WContractification.Pullback S f`
over `S : DiscreteQuotient T`) and verification of its properties (`pi_0(Spec D) = T`,
cartesian diagram, w-local structure, faithfully flat) requires substantial infrastructure
that is stated as an admitted helper lemma below.
-/

-- Helper: the existence of a w-contractible cover, with the detailed construction admitted.
-- This corresponds to `thm:ind-etale-w-contractible-cover-of-w-strictly-local` in the blueprint
-- and `Stacks 0983` (second half).
-- The construction uses:
-- (a) Gleason's theorem: Ultrafilter(pi_0(Spec A)) is extremally disconnected
--     (Mathlib: StoneCech.projective + CompactT2.Projective.extremallyDisconnected)
-- (b) The profinite Pullback: colimit of WContractification.Pullback S f over
--     S : DiscreteQuotient (Ultrafilter (pi_0(Spec A))), cf. def:modify-pi0-profinite
-- (c) Properties of the profinite Pullback (Stacks 097D):
--     * ind-Zariski over A (colimit of ind-Zariski is ind-Zariski)
--     * pi_0(Spec D) = T (from the cartesian diagram, Stacks 096C)
--     * D is w-local (from WLocal/Pullback.lean, fully proved)
--     * D is faithfully flat (from Module.Flat.of_indZariski + surjectivity of Spec.comap)
-- (d) Stalks at maximal ideals are strictly Henselian:
--     by bijectiveOnStalks_algebraMap (fully proved in IndZariski.lean) +
--     transfer of strictly Henselian property through ring isomorphism
-- Individual pieces (a), (c-w-local part), (d-bijectiveOnStalks) are fully proved.
-- Missing infrastructure: (b) profinite Pullback definition + (c-remaining) its properties.
private lemma exists_wContractibleCover (A : Type u) [CommRing A] [IsWStrictlyLocalRing A] :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Algebra.IndZariski A D ∧ Module.FaithfullyFlat A D ∧ IsWContractibleRing D := by
  -- Blueprint: thm:ind-etale-w-contractible-cover-of-w-strictly-local (Stacks 0983).
  sorry

/-- Any w-strictly-local ring has an ind-Zariski, faithfully flat cover that is w-contractible. -/
lemma exists_isWContractibleRing_of_isWStrictlyLocal
    [IsWStrictlyLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndZariski R S ∧ Module.FaithfullyFlat R S ∧ IsWContractibleRing S :=
  exists_wContractibleCover R

/-- Any ring has an ind-étale, faithfully flat cover that is w-contractible. -/
theorem exists_isWContractibleRing :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndEtale R S ∧ Module.FaithfullyFlat R S ∧ IsWContractibleRing S := by
  obtain ⟨S, _, _, _, _, _⟩ :=
    exists_isWContractibleRing_of_isWStrictlyLocal (WStrictLocalization R)
  letI : Algebra R S := Algebra.compHom _ (algebraMap R (WStrictLocalization R))
  have : IsScalarTower R (WStrictLocalization R) S := .of_algebraMap_eq' rfl
  refine ⟨S, inferInstance, inferInstance, ?_, ?_, inferInstance⟩
  · exact Algebra.IndEtale.trans _ (WStrictLocalization R) _
  · exact Module.FaithfullyFlat.trans _ (WStrictLocalization R) _

/-- Any ring has an ind-étale, faithfully flat cover for which every ind-étale
faithfully flat cover splits. -/
theorem exists_forall_exists_retraction :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.IndEtale R S ∧ Module.FaithfullyFlat R S ∧
      ∀ (T : Type u) [CommRing T] [Algebra S T] [Algebra.IndEtale S T] [Module.FaithfullyFlat S T],
        ∃ (f : T →+* S), f.comp (algebraMap S T) = RingHom.id S := by
  obtain ⟨S, _, _, _, _, _⟩ := exists_isWContractibleRing R
  use S, inferInstance, inferInstance, inferInstance, inferInstance
  intro T _ _ _ _
  obtain ⟨f, hf⟩ := IsWContractibleRing.exists_retraction S T
  use f, hf
