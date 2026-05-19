/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Topology.Proetale.Sheafification
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma
import Proetale.Mathlib.AlgebraicGeometry.Sites.Small

/-!
# Comparison with the étale site

-/

universe u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

/-- The inclusion of the étale site into the pro-étale site. -/
@[simps! obj_toComma]
def toProEtale (S : Scheme.{u}) : S.Etale ⥤ S.ProEt :=
  MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl

variable (S : Scheme.{u})

instance : (toProEtale S).Full :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Full

instance : (toProEtale S).Faithful :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl).Faithful

instance : HasFiniteLimits S.Etale :=
  inferInstanceAs <| HasFiniteLimits (MorphismProperty.Over @Etale ⊤ S)

instance : PreservesFiniteLimits (toProEtale S) := by
  have h1 : PreservesFiniteLimits (toProEtale S ⋙ ProEt.forget S) :=
    inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.forget @Etale ⊤ S)
  exact preservesFiniteLimits_of_reflects_of_preserves (toProEtale S) (ProEt.forget S)

/-- `RepresentablyFlat (toProEtale S)`: the structured-arrow comma category
`StructuredArrow Y (toProEtale S)` is cofiltered for every `Y : S.ProEt`.
Since `S.Etale` has all finite limits and `toProEtale S` preserves them (via the
forgetful functor `ProEt.forget S`, which is fully faithful and hence reflects
limits), the conclusion is `flat_of_preservesFiniteLimits`. -/
instance representablyFlat_toProEtale : RepresentablyFlat (toProEtale S) :=
  flat_of_preservesFiniteLimits _

/-- The inclusion of the étale site into the pro-étale site is continuous.

The proof factors through the equality
`toProEtale S ⋙ Over.forget @WeaklyEtale ⊤ S = Over.forget @Etale ⊤ S`
(both functors compute the underlying `Over S` object), the inequality
`etaleTopology ≤ proetaleTopology` (so étale covers are pro-étale covers), and
`RepresentablyFlat (toProEtale S)` (to get the `CompatiblePreserving` half via
`compatiblePreservingOfFlat`). -/
instance isContinuous_toProEtale :
    (toProEtale S).IsContinuous (smallEtaleTopology S) (ProEt.topology S) := by
  refine Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ (toProEtale S)) ?_
  refine ⟨fun {X R} hR ↦ ?_⟩
  -- `R` is a small-étale cover of `X : S.Etale`. We must show its pushforward along
  -- `toProEtale S` is a pro-étale cover of `(toProEtale S).obj X` in `S.ProEt`.
  rw [ProEt.topology_eq_inducedTopology, Functor.mem_inducedTopology_sieves_iff,
    ← Sieve.functorPushforward_comp]
  -- The composition `toProEtale S ⋙ Over.forget @WeaklyEtale ⊤ S` agrees with
  -- `Over.forget @Etale ⊤ S` by definition of `Over.changeProp` (the underlying
  -- `Over S` object is preserved). After this rewrite the goal becomes:
  -- `R.functorPushforward (Over.forget @Etale ⊤ S) ∈ proetaleTopology.over S _`.
  -- The hypothesis `hR : R ∈ smallEtaleTopology S X` unfolds to
  -- `R.functorPushforward (Over.forget @Etale ⊤ S) ∈ etaleTopology.over S _`,
  -- and we conclude using `etaleTopology_le_proetaleTopology` lifted to `.over S`.
  have hR' : R.functorPushforward (Over.forget @Etale ⊤ S) ∈ etaleTopology.over S _ := hR
  rw [GrothendieckTopology.mem_over_iff] at hR' ⊢
  exact etaleTopology_le_proetaleTopology _ hR'

namespace ProEt

variable (A : Type*) [Category A]

/-- The direct image functor from pro-étale sheafs to étale sheafs. -/
@[simps! obj_obj]
abbrev sheafPushforward :
    Sheaf (ProEt.topology S) A ⥤ Sheaf (smallEtaleTopology S) A :=
  (toProEtale S).sheafPushforwardContinuous _ _ _

instance (F : S.Etaleᵒᵖ ⥤ Ab.{u + 1}) : (toProEtale S).op.HasPointwiseLeftKanExtension F :=
  inferInstance

/-- The direct image functor from pro-étale sheafs to étale sheafs has a left-adjoint. -/
instance : (ProEt.sheafPushforward S Ab.{u + 1}).IsRightAdjoint := inferInstance

variable [(sheafPushforward S A).IsRightAdjoint]

/-- The inverse image functor from étale sheafs to pro-étale sheafs. -/
noncomputable abbrev sheafPullback :
    Sheaf (smallEtaleTopology S) A ⥤ Sheaf (ProEt.topology S) A :=
  (toProEtale S).sheafPullback _ _ _

/-- The inverse image - direct image adjunction for the pro-étale site. -/
noncomputable abbrev sheafAdjunction :
    ProEt.sheafPullback S A ⊣ ProEt.sheafPushforward S A :=
  (toProEtale S).sheafAdjunctionContinuous _ _ _

-- needs more assumptions on `A`
/-- The unit of the adjunction `sheafPullback ⊣ sheafPushforward` is an isomorphism.

This is the geometric form of `\lemma:pullback-fully-faithful` (Bhatt–Scholze
Lemma 5.1.2, fully faithful part): the pullback functor `ν^*` from étale sheaves
to pro-étale sheaves is fully faithful, which is equivalent to the unit being
an iso.

The proof depends on `\lemma:pullback-unit-iso` (`F → ν_* ν^* F` is an iso for
every étale sheaf `F`), which in turn relies on `\lemma:pullback-section-affproet`:
for any étale sheaf `F` and `U = lim Uᵢ` in `affproet`,
`ν^* F (U) = colim F(Uᵢ)`.

Formalisation requires:
* the affine pro-étale comparison `isEquivalence_sheafPushforwardContinuous_toProEt`
  (already available in `Proetale/Topology/Comparison/Affine.lean`);
* a description of `ν^*` on objects of `S.AffineProEt` via the colimit over the
  presentation, which needs `A` to admit suitable filtered colimits (concretely:
  `HasFilteredColimitsOfSize` plus their preservation by enough forgetful
  functors), and the colimit being a sheaf;
* invoking the small-étale cover `affet → et` to reduce checking the unit-iso to
  affine étale objects, where the colimit is trivial.

These prerequisites are not yet packaged in the current development; leaving as
`sorry`. -/
instance isIso_unit_sheafAdjunction : IsIso (sheafAdjunction S A).unit :=
  sorry

instance faithful_sheafPullback : (sheafPullback S A).Faithful :=
  (sheafAdjunction S A).faithful_L_of_mono_unit_app

instance full_sheafPullback : (sheafPullback S A).Full :=
  (sheafAdjunction S A).full_L_of_isSplitEpi_unit_app

end ProEt

end AlgebraicGeometry.Scheme
