/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite
import Proetale.Mathlib.RingTheory.RingHom.OpenImmersion

/-!
# Local isomorphisms

A ring homomorphism is a local isomorphism if source locally (in the geometric sense)
it is a standard open immersion.
-/

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Algebra.IsLocalIso

instance refl : IsLocalIso R R := inferInstance

lemma span_isStandardOpenImmersion_eq_top [Algebra.IsLocalIso R S] :
    Ideal.span {g : S | Algebra.IsStandardOpenImmersion R (Localization.Away g)} = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hms⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨g, hgm, hstd⟩ :=
    Algebra.IsLocalIso.exists_notMem_isStandardOpenImmersion (R := R) m
  exact hgm (hms (Ideal.subset_span hstd))

lemma iff_span_isStandardOpenImmersion_eq_top :
    IsLocalIso R S ↔
      Ideal.span {g : S | IsStandardOpenImmersion R (Localization.Away g)} = ⊤ := by
  refine ⟨fun _ ↦ span_isStandardOpenImmersion_eq_top R S, fun h ↦ ⟨fun q hq ↦ ?_⟩⟩
  by_contra!
  apply hq.ne_top
  rw [_root_.eq_top_iff, ← h, Ideal.span_le]
  grind [SetLike.mem_coe]

/-- Local isomorphisms are stable under composition. -/
lemma trans (T : Type*) [CommSemiring T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalIso R S] [IsLocalIso S T] : IsLocalIso R T := by
  -- The proof is purely formal given that open immersions are stable under composition.
  let s : Set S := {g : S | IsStandardOpenImmersion R (Localization.Away g)}
  let T' (g : S) := Localization.Away (algebraMap S T g)
  let (g : S) : Algebra (Localization.Away g) (T' g) := localizationAlgebra (.powers g) T
  let T'' (g : S) (x : T) := Localization.Away (algebraMap _ (T' g) x)
  let t (g : S) : Set T := {x : T | IsStandardOpenImmersion (Localization.Away g) (T'' g x)}
  let ι : Type _ := Σ i : s, t i.1
  have (i : ι) : IsStandardOpenImmersion (Localization.Away i.1.1) (T'' i.1 i.2) := i.2.2
  suffices h : Ideal.span (Set.range fun i : ι ↦ algebraMap S T i.1 * i.2) = ⊤ by
    have (i : ι) : IsStandardOpenImmersion R (T'' i.1 i.2) :=
      have : IsScalarTower R (Localization.Away i.1.1) (T' i.1.1) :=
        IsScalarTower.to₁₃₄ _ S _ _
      have : IsStandardOpenImmersion (Localization.Away i.1.1) (T'' i.1.1 i.2.1) := i.2.2
      have : IsStandardOpenImmersion R (Localization.Away i.1.1) := i.1.2
      .trans _ (Localization.Away i.1.1) _
    exact .of_span_range_eq_top _ h fun i : ι ↦ T'' i.1 i.2
  have h1 := congr(Ideal.map (algebraMap S T) $(span_isStandardOpenImmersion_eq_top R S))
  rw [Ideal.map_top, Ideal.map_span] at h1
  nth_rw 1 [_root_.eq_top_iff, ← Ideal.top_mul ⊤, ← h1, ← span_isStandardOpenImmersion_eq_top S T,
    Ideal.span_mul_span, Ideal.span_le, Set.mul_subset_iff]
  simp only [Set.mem_image, Set.mem_setOf_eq, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro g hg x hx
  refine Ideal.subset_span ⟨⟨⟨g, hg⟩, ⟨x, ?_⟩⟩, rfl⟩
  simp only [Set.mem_setOf_eq, t]
  let : Algebra (Localization.Away x) (T'' g x) :=
    localizationAlgebra (.powers x) (T' g)
  have : IsScalarTower S (Localization.Away x) (T'' g x) :=
    IsScalarTower.to₁₃₄ _ T _ _
  have : IsLocalization (algebraMapSubmonoid (Localization.Away x) (.powers g)) (T'' g x) := by
    have : algebraMapSubmonoid (Localization.Away x) (.powers g) =
      algebraMapSubmonoid (Localization.Away x) (.powers (algebraMap S T g)) := by
        simp [IsScalarTower.algebraMap_apply S T (Localization.Away x)]
    rw [this]
    exact .commutes _ (T' g) _ (.powers x) (.powers (algebraMap S T g))
  have : IsPushout S (Localization.Away x) (Localization.Away g) (T'' g x) :=
    Algebra.isPushout_of_isLocalization (.powers g) _ _ _
  exact .of_isPushout S (Localization.Away x) _ _

end Algebra.IsLocalIso

section Flat

universe v w

/-- A standard open immersion is flat, since it is a localization. -/
lemma Module.Flat.of_isStandardOpenImmersion
    (R : Type v) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardOpenImmersion R S] : Module.Flat R S := by
  obtain ⟨r, _⟩ := Algebra.IsStandardOpenImmersion.exists_away R S
  exact IsLocalization.flat S (Submonoid.powers r)

/-- A local isomorphism is flat, since it is locally a localization. -/
lemma Algebra.IsLocalIso.flat
    (R : Type v) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsLocalIso R S] : Module.Flat R S := by
  refine Module.flat_of_isLocalized_span S S
    {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top _ _)
    (fun g ↦ Localization.Away g.1)
    (fun g ↦ Algebra.linearMap S (Localization.Away g.1)) fun ⟨g, hg⟩ ↦ by
      letI : Algebra.IsStandardOpenImmersion R (Localization.Away g) := hg
      exact Module.Flat.of_isStandardOpenImmersion R (Localization.Away g)

end Flat

/-- A ring homomorphism is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
@[stacks 096E "(1)", algebraize]
def RingHom.IsLocalIso {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IsLocalIso R S

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}

lemma RingHom.isLocalIso_algebraMap [Algebra R S] :
    (algebraMap R S).IsLocalIso ↔ Algebra.IsLocalIso R S := by
  rw [RingHom.IsLocalIso, toAlgebra_algebraMap]

namespace RingHom.IsLocalIso

/-- A bijective ring homomorphism is a local isomorphism. -/
lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso := by
  algebraize [f]
  haveI := Algebra.IsStandardOpenImmersion.of_bijective hf
  change Algebra.IsLocalIso R S
  infer_instance

/-- The composition of local isomorphisms is a local isomorphism. -/
lemma comp {T : Type*} [CommSemiring T] {g : S →+* T} (hg : g.IsLocalIso) (hf : f.IsLocalIso) :
    (g.comp f).IsLocalIso := by
  algebraize [f, g, g.comp f]
  exact Algebra.IsLocalIso.trans R S T

lemma stableUnderComposition : StableUnderComposition IsLocalIso :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

end RingHom.IsLocalIso

/-- `RingHom.IsLocalIso` is stable under base change. -/
lemma RingHom.IsLocalIso.isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.IsLocalIso := by
  refine RingHom.IsStableUnderBaseChange.mk RingHom.IsLocalIso.respectsIso ?_
  intro R S T _ _ _ _ _ hRT
  rw [RingHom.isLocalIso_algebraMap] at hRT ⊢
  infer_instance

namespace CategoryTheory.MorphismProperty

/-- The `MorphismProperty` on `CommRingCat` associated to `RingHom.IsLocalIso` is stable
under cobase change. -/
instance isLocalIso_isStableUnderCobaseChange :
    (RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderCobaseChange := by
  rw [RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.IsLocalIso.isStableUnderBaseChange

/-- The `MorphismProperty` on `CommRingCat` associated to `RingHom.IsLocalIso` is stable
under composition. -/
instance isLocalIso_isStableUnderComposition :
    (RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderComposition where
  comp_mem _ _ hf hg := hg.comp hf

end CategoryTheory.MorphismProperty
