/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.FinitePushforwardStalkFormula
import Proetale.Mathlib.AlgebraicGeometry.Sites.ExactDerivedPushforward

/-!
# Exactness of the pushforward along a finite morphism

Let `f : Y ⟶ X` be a finite morphism of schemes. In this file we prove that the
pushforward `f_*` of abelian sheaves on the small étale sites is **exact**, i.e. it
preserves finite colimits (it always preserves finite limits, being a right adjoint).
This is the first half of blueprint `lemma:pbc-finite`.

The proof rests on the stalk formula
`AlgebraicGeometry.Scheme.Etale.exists_forall_isIso_pushforwardStalkToPiStalk`
(`Proetale.Etale.FinitePushforwardStalkFormula`): the stalk of `f_* F` at a geometric
point `x̄` of `X` is the *finite* product of the stalks of `F` at the geometric points
of `Y` above `x̄`. Since the stalk functors are left adjoints, they preserve
epimorphisms; a finite product of epimorphisms in `Ab` is an epimorphism, so `f_*`
preserves epimorphisms because epimorphisms of abelian sheaves are detected on stalks
(`AlgebraicGeometry.Scheme.epi_of_forall_epi_sheafFiber_geometricPoint`). An additive
functor between abelian categories which preserves epimorphisms and kernels preserves
homology, hence all finite colimits.

## Main results

- `AlgebraicGeometry.Scheme.epi_of_forall_epi_sheafFiber_geometricPoint`: epimorphisms
  of abelian sheaves on the small étale site are detected on stalks at geometric points.
- `AlgebraicGeometry.Scheme.Etale.preservesEpimorphisms_etalePushforward`: the
  pushforward along a finite morphism preserves epimorphisms.
- `AlgebraicGeometry.Scheme.Etale.preservesFiniteColimits_etalePushforward`: **the
  pushforward along a finite morphism is exact**.
- `AlgebraicGeometry.Scheme.Etale.isZero_homology_derivedPushforward_single_of_isFinite`:
  the higher direct images along a finite morphism vanish, `R^q f_* F = 0` for `q ≠ 0`.
- `AlgebraicGeometry.Scheme.Etale.homologyDerivedPushforwardSingleIso_of_isFinite`:
  `H^0(R f_* F) ≅ f_* F`.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme

section EpiStalk

variable {X : Scheme.{u}}

open GrothendieckTopology in
/-- **Epimorphisms of abelian sheaves on the small étale site are detected on stalks**
at the geometric points of `X`. -/
theorem epi_of_forall_epi_sheafFiber_geometricPoint
    {K L : Sheaf X.smallEtaleTopology Ab.{u + 1}} (φ : K ⟶ L)
    (h : ∀ p : X, Epi ((Etale.geometricPoint (X.sepClosurePoint p)).sheafFiber.map φ)) :
    Epi φ := by
  haveI (Φ : (ObjectProperty.ofObj fun p : X ↦
      Point.ulift.{u + 1} (Etale.geometricPoint (X.sepClosurePoint p))).FullSubcategory) :
      Epi (Φ.obj.sheafFiber.map φ) := by
    obtain ⟨Φ, ⟨p⟩⟩ := Φ
    exact ((MorphismProperty.epimorphisms Ab.{u + 1}).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (Point.uliftSheafFiberIso
          (Etale.geometricPoint (X.sepClosurePoint p)))).app (Arrow.mk φ))).2 (h p)
  exact (isConservativeFamilyOfPoints_geometricPoint_ulift.jointlyReflectEpimorphisms
    Ab.{u + 1}).epi φ

end EpiStalk

namespace Etale

attribute [local instance] finite_maximalSpectrum_fiberSections

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- **The pushforward along a finite morphism preserves epimorphisms**: on stalks at a
geometric point `x̄` of `X` it is, by the stalk formula, the finite product of the maps
on the stalks at the geometric points of `Y` above `x̄`. -/
instance preservesEpimorphisms_etalePushforward [IsFinite f] :
    (etalePushforward f).PreservesEpimorphisms where
  preserves {F G} φ hφ := by
    refine epi_of_forall_epi_sheafFiber_geometricPoint _ fun p ↦ ?_
    obtain ⟨y, hy, hiso⟩ :=
      exists_forall_isIso_pushforwardStalkToPiStalk f (X.sepClosurePoint p)
    set ε := Spec.map (CommRingCat.ofHom (algebraMap
      (SeparableClosure (X.residueField p))
      (AlgebraicClosure (SeparableClosure (X.residueField p))))) with hε
    haveI := hiso F
    haveI := hiso G
    have hnat : (geometricPoint (X.sepClosurePoint p)).sheafFiber.map
          ((etalePushforward f).map φ) ≫
          pushforwardStalkToPiStalk f (X.sepClosurePoint p) ε y hy G =
        pushforwardStalkToPiStalk f (X.sepClosurePoint p) ε y hy F ≫
          Limits.Pi.map fun m ↦ (geometricPoint (y m)).sheafFiber.map φ := by
      refine Pi.hom_ext _ _ fun m ↦ ?_
      rw [Category.assoc, pushforwardStalkToPiStalk_π, Category.assoc, Limits.Pi.map_π,
        pushforwardStalkToPiStalk_π_assoc]
      exact pushforwardStalkToStalk_naturality f (X.sepClosurePoint p) ε (y m) (hy m) φ
    haveI : Epi (pushforwardStalkToPiStalk f (X.sepClosurePoint p) ε y hy F ≫
        Limits.Pi.map fun m ↦ (geometricPoint (y m)).sheafFiber.map φ) := by
      haveI (m : MaximalSpectrum (fiberSections f (X.sepClosurePoint p))) :
          Epi ((geometricPoint (y m)).sheafFiber.map φ) := inferInstance
      infer_instance
    rw [← hnat] at this
    have h2 : Epi (((geometricPoint (X.sepClosurePoint p)).sheafFiber.map
          ((etalePushforward f).map φ) ≫
          pushforwardStalkToPiStalk f (X.sepClosurePoint p) ε y hy G) ≫
        inv (pushforwardStalkToPiStalk f (X.sepClosurePoint p) ε y hy G)) :=
      epi_comp _ _
    simpa using h2

/-- **The pushforward along a finite morphism is exact** (the first half of blueprint
`lemma:pbc-finite`): it preserves all finite colimits. Together with the (automatic)
preservation of finite limits, this says that `f_*` is an exact functor on abelian
sheaves over the small étale sites. -/
instance preservesFiniteColimits_etalePushforward [IsFinite f] :
    PreservesFiniteColimits (etalePushforward f) := by
  haveI : (etalePushforward f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  haveI (A B : Sheaf Y.smallEtaleTopology Ab.{u + 1}) (ψ : A ⟶ B) :
      PreservesColimit (parallelPair ψ 0) (etalePushforward f) :=
    Functor.PreservesHomology.preservesCokernel _ ψ
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

section Derived

variable [HasDerivedCategoryPlus.{u + 1} (Sheaf Y.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]

/-- **The higher direct images along a finite morphism vanish**: `R^q f_* F = 0` for
`q ≠ 0` (the derived half of the first part of blueprint `lemma:pbc-finite`). -/
theorem isZero_homology_derivedPushforward_single_of_isFinite [IsFinite f]
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategoryPlus.homologyFunctor
        (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj ((derivedPushforward f).obj
      ((DerivedCategoryPlus.singleFunctor (Sheaf Y.smallEtaleTopology Ab.{u + 1}) 0).obj F))) :=
  isZero_homology_derivedPushforward_single f F n hn

/-- The zeroth direct image along a finite morphism is the pushforward:
`H^0(R f_* F) ≅ f_* F`. -/
noncomputable def homologyDerivedPushforwardSingleIsoOfIsFinite [IsFinite f]
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    (DerivedCategoryPlus.homologyFunctor
        (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj ((derivedPushforward f).obj
      ((DerivedCategoryPlus.singleFunctor (Sheaf Y.smallEtaleTopology Ab.{u + 1}) 0).obj F)) ≅
      (etalePushforward f).obj F :=
  homologyDerivedPushforwardSingleIso f F

end Derived

end Etale

end AlgebraicGeometry.Scheme
