/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.DevissageHomological

/-!
# The derived base change transformation on fibrant complexes

On a fibrant bounded below complex, the derived base change transformation is
computed by a concrete comparison morphism of complexes; isomorphy is detected
degreewise on homology, and the class of complexes on which the transformation is an
isomorphism has the two-out-of-three property for short exact sequences.
-/

universe w v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

/-! ## The derived base change transformation on fibrant complexes -/

namespace AlgebraicGeometry.Scheme

open CochainComplex.Plus.modelCategoryQuillen

variable {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X'.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S'.smallEtaleTopology Ab.{u + 1})]
/- The typeclass searches for empty limit shapes on bounded below complexes of abelian
sheaves explore pathological candidate paths (consuming tens of gigabytes before
succeeding), so we register the cheap instance paths explicitly, layer by layer, for
all four schemes of the base change square. -/

section InstanceCache

variable (Y : Scheme.{u})

noncomputable instance :
    HasLimitsOfShape (Discrete PEmpty.{1}) (Sheaf Y.smallEtaleTopology Ab.{u + 1}) :=
  HasFiniteLimits.out _

noncomputable instance :
    HasLimitsOfShape (Discrete PEmpty.{1})
      (CochainComplex (Sheaf Y.smallEtaleTopology Ab.{u + 1}) ℤ) :=
  HomologicalComplex.instHasLimitsOfShape

noncomputable instance :
    HasLimitsOfShape (Discrete PEmpty.{1})
      (CochainComplex.Plus (Sheaf Y.smallEtaleTopology Ab.{u + 1})) :=
  hasLimitsOfShape_of_closedUnderLimits _ _

noncomputable instance : HasTerminal
    (CochainComplex.Plus (Sheaf Y.smallEtaleTopology Ab.{u + 1})) := inferInstance

end InstanceCache

/-- The class of bounded below complexes of abelian sheaves on the small étale site of
`X` on which the derived base change transformation is an isomorphism. -/
def BaseChangeIso
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) : Prop :=
  IsIso ((derivedBaseChangeNatTrans f g f' g' w).app
    ((DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).obj M))

/-- The class `BaseChangeIso` is invariant under quasi-isomorphisms. -/
lemma baseChangeIso_iff_of_quasiIso
    {M N : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})} (ψ : M ⟶ N)
    (hψ : QuasiIso ψ.hom) :
    BaseChangeIso f g f' g' w M ↔ BaseChangeIso f g f' g' w N := by
  haveI : IsIso ((DerivedCategoryPlus.Q
      (Sheaf X.smallEtaleTopology Ab.{u + 1})).map ψ) :=
    (DerivedCategoryPlus.isIso_Q_map_iff_quasiIso ψ).mpr hψ
  exact NatTrans.isIso_app_iff_of_isIso (derivedBaseChangeNatTrans f g f' g' w)
    ((DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).map ψ)

set_option synthInstance.maxHeartbeats 100000 in
-- the `IsIso` searches on composites over the four sheaf categories are large
/-- On a fibrant bounded below complex (i.e., a bounded below complex of injectives),
the left unit of the derived base change transformation is an isomorphism. -/
lemma isIso_derivedBaseChangeUnitLeft_app
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) [IsFibrant M] :
    IsIso ((derivedBaseChangeUnitLeft f g).app M) := by
  dsimp only [derivedBaseChangeUnitLeft]
  rw [NatTrans.comp_app, NatTrans.comp_app]
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app]
  haveI h := (etalePushforward f).isIso_rightDerivedPlusUnit_app (FibrantObject.mk M)
  haveI : IsIso ((etalePushforward f).rightDerivedPlusUnit.app M) := h
  infer_instance

/-- The comparison morphism `g^* f_* M ⟶ f'_* J` of bounded below complexes attached
to a replacement `j : g'^* M ⟶ J`. If `M` is fibrant and `j` is a fibrant replacement,
the derived base change transformation at `Q.obj M` is an isomorphism iff this concrete
morphism of complexes is a quasi-isomorphism. -/
noncomputable def baseChangeComparison
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    {J : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})}
    (j : (etalePullback g').mapCochainComplexPlus.obj M ⟶ J) :
    (etalePushforward f ⋙ etalePullback g).mapCochainComplexPlus.obj M ⟶
      (etalePushforward f').mapCochainComplexPlus.obj J :=
  (NatTrans.mapCochainComplexPlus (etaleBaseChangeNatTrans f g f' g' w)).app M ≫
    (Functor.mapCochainComplexPlusComp (etalePullback g')
      (etalePushforward f')).hom.app M ≫
    (etalePushforward f').mapCochainComplexPlus.map j

/-- **Factorization of the derived base change transformation on fibrant objects**:
for a fibrant bounded below complex `M` on `X_ét` and a fibrant replacement
`j : g'^* M ⟶ J`, the value of the derived base change transformation at `Q.obj M`
equals, up to composition with isomorphisms on both sides, the image under `Q` of the
concrete comparison morphism `g^* f_* M ⟶ f'_* J`. -/
lemma exists_fac_derivedBaseChangeNatTrans_app
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) [IsFibrant M]
    {J : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})} [IsFibrant J]
    (j : (etalePullback g').mapCochainComplexPlus.obj M ⟶ J) (hj : QuasiIso j.hom) :
    ∃ (uL : (DerivedCategoryPlus.Q _).obj
        ((etalePushforward f ⋙ etalePullback g).mapCochainComplexPlus.obj M) ⟶
        (derivedPushforward f ⋙ derivedPullback g).obj ((DerivedCategoryPlus.Q _).obj M))
      (tail : (DerivedCategoryPlus.Q _).obj
        ((etalePushforward f').mapCochainComplexPlus.obj J) ⟶
        (derivedPullback g' ⋙ derivedPushforward f').obj ((DerivedCategoryPlus.Q _).obj M)),
      IsIso uL ∧ IsIso tail ∧
      uL ≫ (derivedBaseChangeNatTrans f g f' g' w).app ((DerivedCategoryPlus.Q _).obj M) =
        (DerivedCategoryPlus.Q _).map (baseChangeComparison f g f' g' w M j) ≫ tail := by
  -- Step 1: the factorization property of the right derived descent
  have fac : (derivedBaseChangeUnitLeft f g).app M ≫
      (derivedBaseChangeNatTrans f g f' g' w).app ((DerivedCategoryPlus.Q _).obj M) =
        (derivedBaseChangeUnitRight f g f' g' w).app M :=
    Functor.rightDerived_fac_app _ (derivedBaseChangeUnitLeft f g)
      (CochainComplex.Plus.quasiIso _) _ (derivedBaseChangeUnitRight f g f' g' w) M
  -- Step 2: the left unit is invertible on fibrant objects
  haveI hL : IsIso ((derivedBaseChangeUnitLeft f g).app M) :=
    isIso_derivedBaseChangeUnitLeft_app f g M
  -- Step 3: unfold the right unit
  have happ : (derivedBaseChangeUnitRight f g f' g' w).app M =
      (DerivedCategoryPlus.Q _).map
        ((NatTrans.mapCochainComplexPlus (etaleBaseChangeNatTrans f g f' g' w)).app M) ≫
      (DerivedCategoryPlus.Q _).map
        ((Functor.mapCochainComplexPlusComp (etalePullback g')
          (etalePushforward f')).hom.app M) ≫
      ((etalePushforward f').rightDerivedPlusUnit).app
        ((etalePullback g').mapCochainComplexPlus.obj M) ≫
      (derivedPushforward f').map
        (((etalePullback g').mapDerivedCategoryPlusFactors).inv.app M) := by
    dsimp only [derivedBaseChangeUnitRight]
    rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
    simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app]
  -- Step 4: replace the unit at `g'^* M` using naturality along `j`
  haveI huJ : IsIso (((etalePushforward f').rightDerivedPlusUnit).app J) := by
    haveI := (etalePushforward f').isIso_rightDerivedPlusUnit_app (FibrantObject.mk J)
    exact this
  haveI hQj : IsIso ((DerivedCategoryPlus.Q _).map j) :=
    (DerivedCategoryPlus.isIso_Q_map_iff_quasiIso j).mpr hj
  have hunit : ((etalePushforward f').rightDerivedPlusUnit).app
      ((etalePullback g').mapCochainComplexPlus.obj M) =
      ((DerivedCategoryPlus.Q _).map ((etalePushforward f').mapCochainComplexPlus.map j) ≫
        ((etalePushforward f').rightDerivedPlusUnit).app J) ≫
        inv ((derivedPushforward f').map ((DerivedCategoryPlus.Q _).map j)) := by
    refine (IsIso.eq_comp_inv _).mpr ?_
    exact (((etalePushforward f').rightDerivedPlusUnit).naturality j).symm
  -- Step 5: assemble
  have hcomp : (DerivedCategoryPlus.Q _).map (baseChangeComparison f g f' g' w M j) =
      (DerivedCategoryPlus.Q _).map
        ((NatTrans.mapCochainComplexPlus (etaleBaseChangeNatTrans f g f' g' w)).app M) ≫
      (DerivedCategoryPlus.Q _).map
        ((Functor.mapCochainComplexPlusComp (etalePullback g')
          (etalePushforward f')).hom.app M) ≫
      (DerivedCategoryPlus.Q _).map
        ((etalePushforward f').mapCochainComplexPlus.map j) := by
    simp only [baseChangeComparison, Functor.map_comp]
  have hEq : (derivedBaseChangeUnitRight f g f' g' w).app M =
      (DerivedCategoryPlus.Q _).map (baseChangeComparison f g f' g' w M j) ≫
      (((etalePushforward f').rightDerivedPlusUnit).app J ≫
        inv ((derivedPushforward f').map ((DerivedCategoryPlus.Q _).map j)) ≫
        (derivedPushforward f').map
          (((etalePullback g').mapDerivedCategoryPlusFactors).inv.app M)) := by
    rw [happ, hunit, hcomp]
    simp only [Category.assoc]
  exact ⟨(derivedBaseChangeUnitLeft f g).app M, _, hL, inferInstance, fac.trans hEq⟩

/-- **Unfolding of the derived base change transformation on fibrant objects**: for a
fibrant bounded below complex `M` on `X_ét` and a fibrant replacement `j : g'^* M ⟶ J`,
the derived base change transformation is an isomorphism at `Q.obj M` iff the concrete
comparison morphism `g^* f_* M ⟶ f'_* J` is a quasi-isomorphism. -/
lemma baseChangeIso_iff_quasiIso_baseChangeComparison
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) [IsFibrant M]
    {J : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})} [IsFibrant J]
    (j : (etalePullback g').mapCochainComplexPlus.obj M ⟶ J) (hj : QuasiIso j.hom) :
    BaseChangeIso f g f' g' w M ↔
      QuasiIso (baseChangeComparison f g f' g' w M j).hom := by
  obtain ⟨uL, tail, hu, ht, heq⟩ :=
    exists_fac_derivedBaseChangeNatTrans_app f g f' g' w M j hj
  have h1 : BaseChangeIso f g f' g' w M ↔
      IsIso ((DerivedCategoryPlus.Q _).map (baseChangeComparison f g f' g' w M j) ≫
        tail) := by
    unfold BaseChangeIso
    rw [← heq, isIso_comp_left_iff]
  rw [h1, isIso_comp_right_iff]
  exact DerivedCategoryPlus.isIso_Q_map_iff_quasiIso _

/-- Per-degree version of
`baseChangeIso_iff_quasiIso_baseChangeComparison`: on a fibrant complex, the induced
map on the `q`-th homology of the derived base change transformation is an isomorphism
iff the `q`-th homology of the concrete comparison morphism is. -/
lemma isIso_homologyMap_baseChangeComparison_iff
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) [IsFibrant M]
    {J : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})} [IsFibrant J]
    (j : (etalePullback g').mapCochainComplexPlus.obj M ⟶ J) (hj : QuasiIso j.hom)
    (q : ℤ) :
    IsIso ((DerivedCategoryPlus.homologyFunctor
        (Sheaf S'.smallEtaleTopology Ab.{u + 1}) q).map
      ((derivedBaseChangeNatTrans f g f' g' w).app ((DerivedCategoryPlus.Q _).obj M))) ↔
    IsIso (HomologicalComplex.homologyMap
      (baseChangeComparison f g f' g' w M j).hom q) := by
  obtain ⟨uL, tail, hu, ht, heq⟩ :=
    exists_fac_derivedBaseChangeNatTrans_app f g f' g' w M j hj
  have h2 : (DerivedCategoryPlus.homologyFunctor _ q).map uL ≫
      (DerivedCategoryPlus.homologyFunctor _ q).map
        ((derivedBaseChangeNatTrans f g f' g' w).app ((DerivedCategoryPlus.Q _).obj M)) =
      (DerivedCategoryPlus.homologyFunctor _ q).map
        ((DerivedCategoryPlus.Q _).map (baseChangeComparison f g f' g' w M j)) ≫
      (DerivedCategoryPlus.homologyFunctor _ q).map tail := by
    rw [← Functor.map_comp, heq, Functor.map_comp]
  haveI : IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map uL) := inferInstance
  haveI : IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map tail) := inferInstance
  rw [← isIso_comp_left_iff ((DerivedCategoryPlus.homologyFunctor _ q).map uL), h2,
    isIso_comp_right_iff]
  have key : IsIso ((DerivedCategoryPlus.Q _ ⋙
      DerivedCategoryPlus.homologyFunctor _ q).map
        (baseChangeComparison f g f' g' w M j)) ↔
      IsIso ((CochainComplex.Plus.ι _ ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q).map
          (baseChangeComparison f g f' g' w M j)) := by
    rw [← NatIso.naturality_1 (DerivedCategoryPlus.homologyFunctorFactors _ q)
      (baseChangeComparison f g f' g' w M j), isIso_comp_left_iff, isIso_comp_right_iff]
  exact key

/-- The induced maps on homology of the derived base change transformation transfer
along isomorphisms in the derived category. -/
lemma isIso_homologyMap_derivedBaseChangeNatTrans_app_iff_of_isIso
    {K₁ K₂ : DerivedCategoryPlus (Sheaf X.smallEtaleTopology Ab.{u + 1})} (e : K₁ ⟶ K₂)
    [IsIso e] (q : ℤ) :
    IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map
      ((derivedBaseChangeNatTrans f g f' g' w).app K₁)) ↔
    IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map
      ((derivedBaseChangeNatTrans f g f' g' w).app K₂)) :=
  NatTrans.isIso_app_iff_of_isIso
    (Functor.whiskerRight (derivedBaseChangeNatTrans f g f' g' w)
      (DerivedCategoryPlus.homologyFunctor _ q)) e

end AlgebraicGeometry.Scheme
