/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.AlgebraicGeometry.Sites.DerivedPushforward

/-!
# Derived pushforward of an exact functor

For an *exact* functor `G : A ⥤ B` between abelian categories no derivation is
necessary: the unit `G.rightDerivedPlusUnit` of the total right derived functor is an
isomorphism on *every* bounded below complex
(`Functor.isIso_rightDerivedPlusUnit_of_exact`), and `G.rightDerivedPlus` is naturally
isomorphic to the induced functor `G.mapDerivedCategoryPlus`
(`Functor.rightDerivedPlusIsoMapDerivedCategoryPlus`). In particular the homology of
`G.rightDerivedPlus` on an object concentrated in degree `0` is `G` in degree `0` and
vanishes in all other degrees.

We specialize to the pushforward of abelian sheaves along a morphism of schemes on the
small étale sites:

- `AlgebraicGeometry.Scheme.derivedPushforwardIsoOfExact`: if `etalePushforward f`
  preserves finite colimits (it always preserves finite limits, being a right adjoint),
  then `derivedPushforward f` is the underived pushforward, applied degreewise.
- `AlgebraicGeometry.Scheme.isZero_homology_derivedPushforward_single` and
  `AlgebraicGeometry.Scheme.homologyDerivedPushforwardSingleIso`: the corresponding
  computation `R^q f_* F = 0` for `q ≠ 0` and `R^0 f_* F ≅ f_* F`.
- `AlgebraicGeometry.Scheme.isIso_derivedBaseChangeNatTrans_app_of_preservesFiniteColimits`:
  if the pushforwards along both vertical morphisms of a commutative square are exact
  and the underived base change transformation is an isomorphism, then the derived base
  change transformation is an isomorphism on every bounded below complex.
-/

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

section MapCochainComplexPlus

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]

instance NatTrans.isIso_mapCochainComplexPlus {F G : C ⥤ D} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (τ : F ⟶ G) [IsIso τ] :
    IsIso (NatTrans.mapCochainComplexPlus τ) := by
  haveI : IsIso (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)) :=
    inferInstanceAs (IsIso (NatIso.mapHomologicalComplex (asIso τ) (ComplexShape.up ℤ)).hom)
  haveI : ∀ (K : CochainComplex.Plus C), IsIso ((NatTrans.mapCochainComplexPlus τ).app K) :=
    fun K ↦ by
      haveI : IsIso ((CochainComplex.Plus.ι D).map
          ((NatTrans.mapCochainComplexPlus τ).app K)) := by
        rw [NatTrans.mapCochainComplexPlus_app_ι]
        infer_instance
      exact isIso_of_fully_faithful (CochainComplex.Plus.ι D) _
  exact NatIso.isIso_of_isIso_app _

end MapCochainComplexPlus

section Exact

variable {A : Type*} [Category* A] {B : Type*} [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategoryPlus.{w} A] [HasDerivedCategoryPlus.{w} B]

variable (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

instance Functor.isRightDerivedFunctor_mapDerivedCategoryPlus :
    G.mapDerivedCategoryPlus.IsRightDerivedFunctor
      G.mapDerivedCategoryPlusFactors.inv (CochainComplex.Plus.quasiIso A) :=
  inferInstanceAs ((Localization.lift _ G.mapCochainComplexPlus_inverts
      (DerivedCategoryPlus.Q A)).IsRightDerivedFunctor
    (Localization.fac _ G.mapCochainComplexPlus_inverts (DerivedCategoryPlus.Q A)).inv
    (CochainComplex.Plus.quasiIso A))

section SingleHomology

/-- The homology of `G.mapDerivedCategoryPlus` on an object concentrated in degree `0`
is computed by the single complex on the image: the derived category plus construction
commutes with `singleFunctor` and `homologyFunctor` for an exact functor. -/
noncomputable def Functor.homologyMapDerivedCategoryPlusSingleIso (n : ℤ) (X : A) :
    (DerivedCategoryPlus.homologyFunctor B n).obj
        (G.mapDerivedCategoryPlus.obj ((DerivedCategoryPlus.singleFunctor A 0).obj X)) ≅
      ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj (G.obj X)).homology n :=
  (DerivedCategoryPlus.homologyFunctor B n).mapIso
      (G.mapDerivedCategoryPlusFactors.app _) ≪≫
    (DerivedCategoryPlus.homologyFunctorFactors B n).app _ ≪≫
    (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) n).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).app X)

/-- For an exact functor `G`, the homology of `G.mapDerivedCategoryPlus` on an object
concentrated in degree `0` vanishes in nonzero degrees. -/
lemma Functor.isZero_homology_mapDerivedCategoryPlus_singleFunctor_obj
    (X : A) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategoryPlus.homologyFunctor B n).obj
      (G.mapDerivedCategoryPlus.obj ((DerivedCategoryPlus.singleFunctor A 0).obj X))) :=
  (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 (G.obj X) n hn).of_iso
    (G.homologyMapDerivedCategoryPlusSingleIso n X)

/-- For an exact functor `G`, the degree `0` homology of `G.mapDerivedCategoryPlus` on
an object concentrated in degree `0` is the image of the object under `G`. -/
noncomputable def Functor.homologyMapDerivedCategoryPlusSingleZeroIso (X : A) :
    (DerivedCategoryPlus.homologyFunctor B 0).obj
        (G.mapDerivedCategoryPlus.obj ((DerivedCategoryPlus.singleFunctor A 0).obj X)) ≅
      G.obj X :=
  G.homologyMapDerivedCategoryPlusSingleIso 0 X ≪≫
    (HomologicalComplex.homologyFunctorSingleIso B (ComplexShape.up ℤ) 0).app (G.obj X)

end SingleHomology

section RightDerivedPlus

variable [EnoughInjectives A]

/-- The unit of the total right derived functor of an exact functor is an
isomorphism. -/
lemma Functor.isIso_rightDerivedPlusUnit_of_exact : IsIso G.rightDerivedPlusUnit :=
  Functor.isIso_of_isRightDerivedFunctor_of_inverts G.rightDerivedPlus
    G.rightDerivedPlusUnit G.mapCochainComplexPlus_inverts

/-- The unit of the total right derived functor of an exact functor is an isomorphism
on every bounded below complex, not only on the fibrant ones
(cf. `Functor.isIso_rightDerivedPlusUnit_app`). -/
lemma Functor.isIso_rightDerivedPlusUnit_app_of_exact (K : CochainComplex.Plus A) :
    IsIso (G.rightDerivedPlusUnit.app K) :=
  have := G.isIso_rightDerivedPlusUnit_of_exact
  inferInstance

/-- The total right derived functor of an exact functor is naturally isomorphic to the
induced functor on bounded below derived categories: no derivation is necessary. -/
noncomputable def Functor.rightDerivedPlusIsoMapDerivedCategoryPlus :
    G.rightDerivedPlus ≅ G.mapDerivedCategoryPlus :=
  Functor.rightDerivedUnique G.rightDerivedPlus G.mapDerivedCategoryPlus
    G.rightDerivedPlusUnit G.mapDerivedCategoryPlusFactors.inv
    (CochainComplex.Plus.quasiIso A)

/-- The comparison isomorphism `Functor.rightDerivedPlusIsoMapDerivedCategoryPlus` is
compatible with the units of both right derived functor structures. -/
lemma Functor.rightDerivedPlusUnit_whiskerLeft_rightDerivedPlusIsoMapDerivedCategoryPlus :
    G.rightDerivedPlusUnit ≫ Functor.whiskerLeft (DerivedCategoryPlus.Q A)
        G.rightDerivedPlusIsoMapDerivedCategoryPlus.hom =
      G.mapDerivedCategoryPlusFactors.inv := by
  dsimp only [Functor.rightDerivedPlusIsoMapDerivedCategoryPlus]
  simp

end RightDerivedPlus

end Exact

end CategoryTheory

namespace AlgebraicGeometry.Scheme

open CategoryTheory MorphismProperty

section DerivedPushforwardExact

variable {X S : Scheme.{u}} (f : X ⟶ S)

instance : PreservesFiniteLimits (etalePushforward f) :=
  haveI : PreservesLimitsOfSize.{0, 0} (smallPushforward f @Etale Ab.{u + 1}) :=
    (smallPullbackPushforwardAdj f @Etale Ab.{u + 1}).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

variable [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})]

/-- If the pushforward of abelian sheaves along `f` is exact (it always preserves
finite limits, so this amounts to `PreservesFiniteColimits`), the derived pushforward
is the underived pushforward, applied degreewise. -/
noncomputable def derivedPushforwardIsoOfExact
    [PreservesFiniteColimits (etalePushforward f)] :
    derivedPushforward f ≅ (etalePushforward f).mapDerivedCategoryPlus :=
  (etalePushforward f).rightDerivedPlusIsoMapDerivedCategoryPlus

/-- If the pushforward of abelian sheaves along `f` is exact, the higher derived
pushforwards of a single sheaf vanish: `R^q f_* F = 0` for `q ≠ 0`. -/
theorem isZero_homology_derivedPushforward_single
    [PreservesFiniteColimits (etalePushforward f)]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategoryPlus.homologyFunctor
        (Sheaf S.smallEtaleTopology Ab.{u + 1}) n).obj ((derivedPushforward f).obj
      ((DerivedCategoryPlus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))) :=
  ((etalePushforward f).isZero_homology_mapDerivedCategoryPlus_singleFunctor_obj F n hn).of_iso
    ((DerivedCategoryPlus.homologyFunctor (Sheaf S.smallEtaleTopology Ab.{u + 1}) n).mapIso
      ((derivedPushforwardIsoOfExact f).app _))

/-- If the pushforward of abelian sheaves along `f` is exact, the degree `0` derived
pushforward of a single sheaf is the underived pushforward: `R^0 f_* F ≅ f_* F`. -/
noncomputable def homologyDerivedPushforwardSingleIso
    [PreservesFiniteColimits (etalePushforward f)]
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) :
    (DerivedCategoryPlus.homologyFunctor
        (Sheaf S.smallEtaleTopology Ab.{u + 1}) 0).obj ((derivedPushforward f).obj
      ((DerivedCategoryPlus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F)) ≅
      (etalePushforward f).obj F :=
  (DerivedCategoryPlus.homologyFunctor (Sheaf S.smallEtaleTopology Ab.{u + 1}) 0).mapIso
      ((derivedPushforwardIsoOfExact f).app _) ≪≫
    (etalePushforward f).homologyMapDerivedCategoryPlusSingleZeroIso F

end DerivedPushforwardExact

section DerivedBaseChange

variable {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X'.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S'.smallEtaleTopology Ab.{u + 1})]

/-- If the pushforward along `f` is exact, the natural transformation exhibiting
`Rf_* ⋙ g^*` as a functor under `f_* ⋙ g^*` is an isomorphism. -/
lemma isIso_derivedBaseChangeUnitLeft [PreservesFiniteColimits (etalePushforward f)] :
    IsIso (derivedBaseChangeUnitLeft f g) := by
  haveI := (etalePushforward f).isIso_rightDerivedPlusUnit_of_exact
  dsimp only [derivedBaseChangeUnitLeft]
  infer_instance

omit [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})] in
/-- If the pushforward along `f'` is exact and the underived base change transformation
is an isomorphism, the natural transformation from `f_* ⋙ g^*` on complexes to
`g'^* ⋙ Rf'_*` is an isomorphism. -/
lemma isIso_derivedBaseChangeUnitRight [PreservesFiniteColimits (etalePushforward f')]
    [IsIso (etaleBaseChangeNatTrans f g f' g' w)] :
    IsIso (derivedBaseChangeUnitRight f g f' g' w) := by
  haveI := (etalePushforward f').isIso_rightDerivedPlusUnit_of_exact
  dsimp only [derivedBaseChangeUnitRight]
  infer_instance

/-- If the pushforwards along `f` and `f'` are exact and the underived base change
transformation is an isomorphism on every abelian sheaf, then the derived base change
transformation is an isomorphism on every bounded below complex. -/
theorem isIso_derivedBaseChangeNatTrans_app_of_preservesFiniteColimits
    [PreservesFiniteColimits (etalePushforward f)]
    [PreservesFiniteColimits (etalePushforward f')]
    (hbc : ∀ (F : Sheaf X.smallEtaleTopology Ab.{u + 1}),
      IsIso ((etaleBaseChangeNatTrans f g f' g' w).app F))
    (K : DerivedCategoryPlus (Sheaf X.smallEtaleTopology Ab.{u + 1})) :
    IsIso ((derivedBaseChangeNatTrans f g f' g' w).app K) := by
  haveI := hbc
  haveI : IsIso (etaleBaseChangeNatTrans f g f' g' w) := NatIso.isIso_of_isIso_app _
  haveI := isIso_derivedBaseChangeUnitLeft f g
  haveI := isIso_derivedBaseChangeUnitRight f g f' g' w
  haveI : (DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).EssSurj :=
    Localization.essSurj _ (CochainComplex.Plus.quasiIso _)
  rw [← NatTrans.isIso_app_iff_of_iso _
    ((DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).objObjPreimageIso K)]
  exact IsIso.of_isIso_fac_left
    ((derivedPushforward f ⋙ derivedPullback g).rightDerived_fac_app
      (derivedBaseChangeUnitLeft f g) (CochainComplex.Plus.quasiIso _)
      (derivedPullback g' ⋙ derivedPushforward f')
      (derivedBaseChangeUnitRight f g f' g' w) _)

/-- If the pushforwards along `f` and `f'` are exact and the underived base change
transformation is an isomorphism, then so is the derived base change transformation. -/
theorem isIso_derivedBaseChangeNatTrans_of_preservesFiniteColimits
    [PreservesFiniteColimits (etalePushforward f)]
    [PreservesFiniteColimits (etalePushforward f')]
    [IsIso (etaleBaseChangeNatTrans f g f' g' w)] :
    IsIso (derivedBaseChangeNatTrans f g f' g' w) :=
  haveI : ∀ K, IsIso ((derivedBaseChangeNatTrans f g f' g' w).app K) := fun K ↦
    isIso_derivedBaseChangeNatTrans_app_of_preservesFiniteColimits f g f' g' w
      (fun _ ↦ inferInstance) K
  NatIso.isIso_of_isIso_app _

end DerivedBaseChange

end AlgebraicGeometry.Scheme
