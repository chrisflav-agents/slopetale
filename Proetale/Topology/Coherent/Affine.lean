/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.FromPi1.Etale
import Proetale.Mathlib.AlgebraicGeometry.Extensive
import Proetale.Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Proetale.Mathlib.CategoryTheory.Limits.Comma
import Proetale.Topology.Flat.Sheaf
import Proetale.Topology.Coherent.Etale

/-!
# Affine étale site
-/

universe u

open CategoryTheory Opposite Limits

namespace CategoryTheory

section

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (X : D)

instance (J : Type*) [Category J] [IsConnected J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F]
    [HasLimitsOfShape J D] :
    PreservesLimitsOfShape J (CostructuredArrow.toOver F X) where
  preservesLimit {K} := by
    have : PreservesLimitsOfShape J (CostructuredArrow.proj F X) := by
      infer_instance
    have : PreservesLimit K (CostructuredArrow.toOver F X ⋙ Over.forget X) := by
      change PreservesLimit K (CostructuredArrow.proj F X ⋙ F)
      infer_instance
    have : HasLimit (K ⋙ CostructuredArrow.toOver F X) := by
      infer_instance
    have : PreservesLimit (K ⋙ CostructuredArrow.toOver F X) (Over.forget X) := by
      infer_instance
    have : ReflectsLimit (K ⋙ CostructuredArrow.toOver F X) (Over.forget X) :=
      reflectsLimit_of_reflectsIsomorphisms _ _
    apply Limits.preservesLimit_of_reflects_of_preserves _ (Over.forget X)

end

namespace MorphismProperty

variable {C D : Type*} [Category C] [Category D]
variable (P : MorphismProperty D) (Q : MorphismProperty C) [Q.IsMultiplicative] (F : C ⥤ D) (X : D)

namespace CostructuredArrow

variable [P.IsStableUnderBaseChange]
  [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
  [PreservesLimitsOfShape WalkingCospan F] [HasPullbacks C] [HasPullbacks D]

instance : PreservesLimitsOfShape WalkingCospan (CostructuredArrow.toOver P F X) := by
  have : PreservesLimitsOfShape WalkingCospan
      (CostructuredArrow.toOver P F X ⋙ Over.forget P ⊤ X) := by
    change PreservesLimitsOfShape WalkingCospan <|
      CostructuredArrow.forget P ⊤ F X ⋙ CategoryTheory.CostructuredArrow.toOver F X
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

end CostructuredArrow

end MorphismProperty

end CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

variable {S : Scheme.{u}}

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]

instance IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
    {ι : Type*} [Small.{u} ι] {C : Type*} [Category C] [HasColimitsOfShape (Discrete ι) C]
    (L : C ⥤ Scheme.{u}) [PreservesColimitsOfShape (Discrete ι) L] (X : Scheme.{u}) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape (Discrete ι) := by
  refine CostructuredArrow.isClosedUnderColimitsOfShape ?_ ?_ ?_ _
  · intro D _
    exact Sigma.cocone _
  · intro D
    exact coproductIsCoproduct' _
  · intro D _ X s h
    exact IsZariskiLocalAtSource.sigmaDesc (h ⟨·⟩)

variable [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]

instance : HasFiniteCoproducts (P.CostructuredArrow ⊤ Scheme.Spec S) where
  out n := by
    have : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
        (Discrete (Fin n)) := by
      apply IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
    apply MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimitsOfShape

/-- `CostructuredArrow.toOver Scheme.Spec S` preserves binary coproducts.
This follows because `proj ⋙ Spec` preserves coproducts (as `proj` creates and `Spec`
preserves), `Over.forget S` reflects colimits (since it creates them), and
`toOver ⋙ Over.forget = proj ⋙ Spec`. -/
noncomputable instance : PreservesColimitsOfShape (Discrete WalkingPair)
    (CategoryTheory.CostructuredArrow.toOver Scheme.Spec S) := by
  have : PreservesColimitsOfShape (Discrete WalkingPair)
      (CategoryTheory.CostructuredArrow.toOver Scheme.Spec S ⋙
        CategoryTheory.Over.forget S) := by
    show PreservesColimitsOfShape (Discrete WalkingPair) <|
      CategoryTheory.CostructuredArrow.proj Scheme.Spec S ⋙ Scheme.Spec
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (CategoryTheory.Over.forget S)

instance : PreservesColimitsOfShape (Discrete WalkingPair)
    (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S) := by
  haveI : (MorphismProperty.commaObj Scheme.Spec (.fromPUnit S) P).IsClosedUnderColimitsOfShape
      (Discrete WalkingPair) := by
    apply IsZariskiLocalAtSource.isClosedUnderColimitsOfShape_discrete
  haveI : HasColimitsOfShape (Discrete WalkingPair)
      (P.CostructuredArrow ⊤ Scheme.Spec S) := inferInstance
  haveI : HasColimitsOfShape (Discrete WalkingPair)
      (Comma Scheme.Spec (Functor.fromPUnit S)) :=
    inferInstanceAs <| HasColimitsOfShape _ (CostructuredArrow Scheme.Spec S)
  haveI : CreatesColimitsOfShape (Discrete WalkingPair)
      (MorphismProperty.CostructuredArrow.forget P ⊤ Scheme.Spec S) :=
    MorphismProperty.Comma.forgetCreatesColimitsOfShapeOfClosed
      (L := Scheme.Spec) (R := Functor.fromPUnit S) P (Discrete WalkingPair)
  have : PreservesColimitsOfShape (Discrete WalkingPair)
      (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S ⋙
        MorphismProperty.Over.forget P ⊤ S) := by
    show PreservesColimitsOfShape (Discrete WalkingPair) <|
      MorphismProperty.CostructuredArrow.forget P ⊤ Scheme.Spec S ⋙
        CategoryTheory.CostructuredArrow.toOver Scheme.Spec S
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (MorphismProperty.Over.forget P ⊤ S)

instance : FinitaryExtensive (P.CostructuredArrow ⊤ Scheme.Spec S) :=
  CategoryTheory.finitaryExtensive_of_preserves_and_reflects_isomorphism
    (MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S)

instance : Preregular (P.CostructuredArrow ⊤ Scheme.Spec S) := by
  apply Preregular.of_hasPullbacks_of_effectiveEpi_fst
  intro X Y Z f g hg
  let F := MorphismProperty.CostructuredArrow.toOver P Scheme.Spec S
  -- The key step: show the underlying scheme map of g is surjective.
  -- This requires: `EffectiveEpi g` in `P.CostructuredArrow ⊤ Scheme.Spec S` implies
  -- `Surjective (F.map g).left`.
  --
  -- NOTE: Per `blueprint/src/chapters/pro-categories.tex` (`remark:et-not-precoherent-topology`),
  -- this is explicitly *open* in the mathematical literature: "it is not clear to the authors
  -- if effective epimorphisms in `affet(X)` are still surjective." So this step cannot be
  -- proved with the current hypotheses on `P`; it would require either:
  --   (a) original research establishing the surjectivity, or
  --   (b) replacing `Preregular.of_hasPullbacks_of_effectiveEpi_fst` with a different
  --       construction (e.g. via `Functor.reflects_preregular` using cover density and
  --       an `EffectivelyEnough` instance from affine open covers — but this requires
  --       extra hypotheses ensuring `Preregular (MorphismProperty.Over P ⊤ S)`).
  haveI hsur_g : Surjective (F.map g).left := by
    sorry
  -- Show the underlying scheme morphism of pullback.fst in the Over category is surjective.
  haveI : Surjective (pullback.fst (F.map f) (F.map g)).left := by
    show Surjective ((MorphismProperty.Over.forget P ⊤ S ⋙ CategoryTheory.Over.forget S).map
      (pullback.fst (F.map f) (F.map g)))
    rw [← pullbackComparison_comp_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Surjective) _ _).mpr (by
      dsimp
      haveI : Surjective ((CategoryTheory.Over.forget S).map
        ((MorphismProperty.Over.forget P ⊤ S).map (F.map g))) := hsur_g
      infer_instance)
  -- pullback.fst in Over category is EffectiveEpi (from Surjective → EffectiveEpi)
  -- NOTE: This step needs EffectiveEpi from Surjective for general P, which may not hold.
  -- For P = @Etale, this is Scheme.Etale.effectiveEpi_of_surjective.
  -- Attempt: reduce to effective-epi at the scheme level via the two forgetful functors.
  -- `MorphismProperty.Over.forget P ⊤ S ⋙ Over.forget S` should reflect effective epis,
  -- and then we need `EffectiveEpi` of the underlying scheme morphism. The pullback.fst
  -- is surjective; for `P = @Etale` it is also LocallyOfFinitePresentation + Flat (since
  -- `F.map f` and `F.map g` carry the étale property which is base-change stable), so the
  -- scheme map is an effective epi by `AlgebraicGeometry.Scheme` instance in Fpqc.lean.
  -- For general `P` with only the listed typeclasses, the underlying scheme map is only
  -- surjective; we'd need extra hypotheses (e.g. `P ⊆ Flat ⊓ LocallyOfFinitePresentation`)
  -- to conclude.
  haveI : EffectiveEpi (pullback.fst (F.map f) (F.map g)) := by
    apply (MorphismProperty.Over.forget P ⊤ S ⋙ CategoryTheory.Over.forget S).effectiveEpi_of_map
    -- Goal (after `dsimp`):
    --   `EffectiveEpi (Over.Hom.left (MorphismProperty.Comma.Hom.hom`
    --   `  (pullback.fst (F.map f) (F.map g))))`
    -- i.e. the underlying scheme morphism is an effective epi.
    -- We have `Surjective` of it (via the prior `Surjective (pullback.fst …).left` step).
    -- Mathlib provides `EffectiveEpi` from `Surjective + Flat + LocallyOfFinitePresentation`
    -- (`Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`). For `P = @Etale` the pullback inherits
    -- these properties via base change, so `infer_instance` succeeds. For arbitrary `P`
    -- with only `[IsZariskiLocalAtSource P, IsStableUnderBaseChange P, HasOfPostcompProperty P P,
    -- IsMultiplicative P]`, the scheme map is only surjective; we would need additional
    -- hypotheses (e.g. `P ≤ Flat ⊓ LocallyOfFinitePresentation`) to invoke that instance.
    sorry
  -- F preserves pullbacks and reflects effective epis, so transfer back
  apply F.effectiveEpi_of_map
  rw [show F.map (pullback.fst f g) =
    (PreservesPullback.iso F f g).hom ≫ pullback.fst (F.map f) (F.map g)
    from (PreservesPullback.iso_hom_fst F f g).symm]
  infer_instance

noncomputable
def Cover.etaleAffineRefinement (𝒰 : S.Cover (precoverage @Etale)) :
    S.AffineCover @Etale where
  I₀ := (𝒰.bind fun j ↦ (𝒰.X j).affineCover.changeProp (fun _ ↦ inferInstance)).I₀
  X _ := _
  f := (𝒰.bind fun j => (𝒰.X j).affineCover.changeProp fun _ ↦ inferInstance).f
  idx := Cover.idx (𝒰.bind fun j => (𝒰.X j).affineCover.changeProp fun _ ↦ inferInstance)
  covers := Cover.covers (𝒰.bind fun j => (𝒰.X j).affineCover.changeProp fun _ ↦ inferInstance)
  map_prop j := by
    simp [Cover.changeProp]
    have : IsOpenImmersion ((𝒰.X j.fst).affineCover.f j.snd) := inferInstance
    have : Etale (𝒰.f j.fst) := 𝒰.map_prop _
    exact MorphismProperty.comp_mem _ _ _ (IsZariskiLocalAtSource.of_isOpenImmersion _) ‹_›

namespace AffineEtale

instance : (AffineEtale.Spec S).ReflectsEffectiveEpis :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).ReflectsEffectiveEpis

instance effectiveEpi_of_surjective {S : Scheme} {X Y : S.AffineEtale} (f : X ⟶ Y)
    [Surjective (Spec.map f.left.unop)] : EffectiveEpi f := by
  apply (AffineEtale.Spec S).effectiveEpi_of_map
  have : Surjective ((AffineEtale.Spec S).map f).left := ‹_›
  infer_instance

instance : HasPullbacks S.AffineEtale :=
  inferInstanceAs <| HasPullbacks (MorphismProperty.CostructuredArrow _ _ _ _)

-- Question: What are the effective epimorphisms of `AffineEtale S`?
-- See blueprint remark:et-not-precoherent-topology for discussion.
-- The `Preregular` instance for the general `P.CostructuredArrow ⊤ Scheme.Spec S`
-- (defined above, with sorry for the key surjectivity step) provides this.

instance preregular : Preregular (AffineEtale S) :=
  inferInstanceAs <| Preregular (MorphismProperty.CostructuredArrow _ _ _ _)

instance precoherent : Precoherent (AffineEtale S) :=
  inferInstanceAs <| Precoherent (MorphismProperty.CostructuredArrow _ _ _ _)

end AffineEtale

end Scheme

end AlgebraicGeometry
