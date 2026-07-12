/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.FieldTheory.SeparableClosure
import Proetale.Mathlib.CategoryTheory.Elements
import Proetale.Mathlib.CategoryTheory.Sites.Point.ULift

/-!
# Geometric points of the small étale site

A geometric point `x : Spec Ω ⟶ X` of a scheme `X` with `Ω` separably closed defines a
point (in the sense of sites, `CategoryTheory.GrothendieckTopology.Point`) of the small
étale site of `X`: the fiber functor sends an étale `X`-scheme `U` to the set of lifts
of `x` to `U`. We construct this point (`AlgebraicGeometry.Scheme.Etale.geometricPoint`)
by restricting the point of the big étale site defined in mathlib
(`AlgebraicGeometry.Scheme.geometricFiber`) along the inclusion
`X.Etale ⥤ Over X` of the small étale site.

The associated fiber functor on sheaves (`Point.sheafFiber`) is the stalk functor at the
geometric point.

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.geometricPoint`: the point of `X.smallEtaleTopology`
  associated to a geometric point of `X`.

-/

universe v' u' u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

instance : HasFiniteLimits X.Etale :=
  inferInstanceAs <| HasFiniteLimits (MorphismProperty.Over @Etale ⊤ X)

instance : PreservesFiniteLimits (Etale.forget X) :=
  inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.forget @Etale ⊤ X)

instance : RepresentablyFlat (Etale.forget X) :=
  flat_of_preservesFiniteLimits _

instance : (Etale.forget X).LocallyCoverDense (X.overGrothendieckTopology @Etale) :=
  inferInstanceAs <|
    (MorphismProperty.Over.forget @Etale ⊤ X).LocallyCoverDense
      (X.overGrothendieckTopology @Etale)

/-- The inclusion of the small étale site of `X` into the category of `X`-schemes
equipped with the étale topology preserves covers: the topology on the source is the
induced topology. -/
lemma coverPreserving_etaleForget :
    CoverPreserving X.smallEtaleTopology (X.overGrothendieckTopology @Etale)
      (Etale.forget X) :=
  Functor.inducedTopology_coverPreserving
    (MorphismProperty.Over.forget @Etale ⊤ X) (X.overGrothendieckTopology @Etale)

namespace Etale

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (x : Spec (CommRingCat.of Ω) ⟶ X)

/-- The affine étale neighbourhoods of a geometric point are initial among all étale
neighbourhoods. -/
instance initial_pre_affineEtaleSpec :
    (CategoryOfElements.pre (AffineEtale.Spec X)
      (Etale.forget X ⋙ ((geometricFiber Ω).over x).fiber)).Initial := by
  set F : X.Etale ⥤ Type u := Etale.forget X ⋙ ((geometricFiber Ω).over x).fiber with hF
  · refine Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ (fun p ↦ ?_)
    obtain ⟨U, u⟩ := p
    -- `φ` is the geometric point of `U` given by the element `u`.
    let φ : Spec (CommRingCat.of Ω) ⟶ U.left := u.val
    -- refine it by an affine open neighbourhood, i.e. a member of the affine cover
    obtain ⟨i, y, hy⟩ := U.left.affineCover.exists_eq (φ.base default)
    -- lift `φ` through the open immersion `W ⟶ U.left`
    have hrange : Set.range φ.base ⊆ Set.range (U.left.affineCover.f i).base := by
      rintro - ⟨t, rfl⟩
      rw [Unique.eq_default t]
      exact ⟨y, hy⟩
    set W : Scheme.{u} := U.left.affineCover.X i with hW
    let φ' : Spec (CommRingCat.of Ω) ⟶ W := IsOpenImmersion.lift _ φ hrange
    -- the affine étale neighbourhood given by `Spec Γ(W, ⊤)`
    haveI : Etale (W.isoSpec.inv ≫ U.left.affineCover.f i ≫ U.hom) := by
      have : Etale (U.left.affineCover.f i) := inferInstance
      infer_instance
    refine ⟨⟨AffineEtale.mk (W.isoSpec.inv ≫ U.left.affineCover.f i ≫ U.hom),
      ⟨φ' ≫ W.isoSpec.hom, ?_⟩⟩,
      ⟨⟨MorphismProperty.Over.homMk (W.isoSpec.inv ≫ U.left.affineCover.f i)
        (by simp) trivial, ?_⟩⟩⟩
    · show (φ' ≫ W.isoSpec.hom) ≫ W.isoSpec.inv ≫ U.left.affineCover.f i ≫ U.hom = x
      have hu : φ ≫ U.hom = x := u.property
      rw [← hu]
      simp [φ']
    · refine Subtype.ext ?_
      show (φ' ≫ W.isoSpec.hom) ≫ W.isoSpec.inv ≫ U.left.affineCover.f i = φ
      simp [φ', IsOpenImmersion.lift_fac]

/-- The étale neighbourhoods of a geometric point admit an initial small family, given
by the affine étale neighbourhoods. -/
instance initiallySmall_elements :
    InitiallySmall.{u}
      (Etale.forget X ⋙ ((geometricFiber Ω).over x).fiber).Elements :=
  initiallySmall_of_initial_of_essentiallySmall
    (CategoryOfElements.pre (AffineEtale.Spec X)
      (Etale.forget X ⋙ ((geometricFiber Ω).over x).fiber))

/-- A geometric point `x : Spec Ω ⟶ X` with `Ω` separably closed defines a point of the
small étale site of `X` whose fiber functor sends an étale `X`-scheme `U` to the set of
lifts of `x` to `U`. -/
noncomputable def geometricPoint : X.smallEtaleTopology.Point :=
  ((geometricFiber Ω).over x).comap (Etale.forget X) coverPreserving_etaleForget

/-- Constructor for elements of the fiber of `geometricPoint x` over an étale
`X`-scheme `U`: a lift of `x` to `U`. -/
def geometricPoint.mkFiber {U : X.Etale} (φ : Spec (CommRingCat.of Ω) ⟶ U.left)
    (h : φ ≫ U.hom = x) : (geometricPoint x).fiber.obj U :=
  ⟨φ, h⟩

@[simp]
lemma geometricPoint.mkFiber_val {U : X.Etale} (φ : Spec (CommRingCat.of Ω) ⟶ U.left)
    (h : φ ≫ U.hom = x) : (geometricPoint.mkFiber x φ h).val = φ :=
  rfl

lemma geometricPoint.fiber_map {U V : X.Etale} (g : U ⟶ V)
    (u : (geometricPoint x).fiber.obj U) :
    ((geometricPoint x).fiber.map g u).val = u.val ≫ g.left :=
  rfl

end Etale

section SepClosurePoint

variable (X) in
/-- The canonical geometric point of `X` over a point `p`, with values in the separable
closure of the residue field at `p`. -/
noncomputable def sepClosurePoint (p : X) :
    Spec (CommRingCat.of (SeparableClosure (X.residueField p))) ⟶ X :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (X.residueField p) (SeparableClosure (X.residueField p)))) ≫
    X.fromSpecResidueField p

/-- Every point of an étale `X`-scheme `U` underlies a lift of the canonical geometric
point of `X` at its image: étale morphisms induce finite separable residue field
extensions, which embed into the separable closure. -/
lemma exists_geometricPoint_fiber_sepClosurePoint (U : X.Etale) (q : U.left) :
    ∃ u : (Etale.geometricPoint (X.sepClosurePoint (U.hom q))).fiber.obj U,
      u.val.base default = q := by
  haveI : Etale U.hom := U.prop
  -- embed the residue field at `q` into the separable closure of the one at `p`;
  -- the residue field extension is separable because `U.hom` is étale
  letI : Algebra (X.residueField (U.hom.base q)) (U.left.residueField q) :=
    (U.hom.residueFieldMap q).hom.toAlgebra
  haveI : Algebra.IsSeparable (X.residueField (U.hom.base q)) (U.left.residueField q) :=
    FormallyUnramified.instIsSeparableCarrierResidueFieldCoeContinuousMapCarrierCarrierCommRingCatHomTopCatBaseOfLocallyOfFiniteType
      (f := U.hom) (x := q)
  let b : U.left.residueField q →ₐ[X.residueField (U.hom q)]
      SeparableClosure (X.residueField (U.hom q)) := IsSepClosed.lift
  have hfac : U.hom.residueFieldMap q ≫ CommRingCat.ofHom b.toRingHom =
      CommRingCat.ofHom (algebraMap (X.residueField (U.hom q))
        (SeparableClosure (X.residueField (U.hom q)))) := by
    ext1
    exact b.comp_algebraMap
  refine ⟨Etale.geometricPoint.mkFiber _
    (Spec.map (CommRingCat.ofHom b.toRingHom) ≫ U.left.fromSpecResidueField q) ?_, ?_⟩
  · have hnat : U.left.fromSpecResidueField q ≫ U.hom =
        Spec.map (U.hom.residueFieldMap q) ≫ X.fromSpecResidueField (U.hom q) :=
      (U.hom.SpecMap_residueFieldMap_fromSpecResidueField q).symm
    rw [Category.assoc, hnat, ← Category.assoc, ← Spec.map_comp, hfac]
    rfl
  · show U.left.fromSpecResidueField q ((Spec.map (CommRingCat.ofHom b.toRingHom)) default) = q
    exact fromSpecResidueField_apply q _

open GrothendieckTopology in
/-- The geometric points of `X` with values in the separable closures of the residue
fields form a conservative family of points of the small étale site: a sieve all of
whose fibers are jointly surjective is a covering sieve (SGA 4 IV 6.5 (a), VIII 3.5). -/
theorem isConservativeFamilyOfPoints_geometricPoint :
    (ObjectProperty.ofObj fun p : X ↦
      Etale.geometricPoint (X.sepClosurePoint p)).IsConservativeFamilyOfPoints := by
  refine ObjectProperty.IsConservativeFamilyOfPoints.mk' (fun U S hS ↦ ?_)
  -- it suffices to refine `S` by an étale cover
  show S ∈ X.smallGrothendieckTopology @Etale U
  rw [mem_smallGrothendieckTopology]
  -- every point `q` of `U` is in the image of an arrow of `S`, because the canonical
  -- geometric point at `q` lifts through an arrow of `S`
  have key : ∀ q : U.left, ∃ (V : X.Etale) (g : V ⟶ U), S g ∧ ∃ y, g.left y = q := by
    intro q
    obtain ⟨u, hu⟩ := exists_geometricPoint_fiber_sepClosurePoint U q
    let Φ : (ObjectProperty.ofObj fun p : X ↦
        Etale.geometricPoint (X.sepClosurePoint p)).FullSubcategory :=
      ⟨Etale.geometricPoint (X.sepClosurePoint (U.hom q)), ⟨U.hom q⟩⟩
    obtain ⟨V, g, hg, v, hv⟩ := hS Φ u
    have hval : v.val ≫ g.left = u.val := congrArg Subtype.val hv
    refine ⟨V, g, hg, v.val.base default, ?_⟩
    have hcomp : g.left (v.val.base default) = (v.val ≫ g.left).base default := rfl
    rw [hcomp, hval]
    exact hu
  choose V g hgS hgq using key
  -- assemble the chosen arrows into an étale cover of `U`
  haveI (q : U.left) : Etale ((g q).left) := by
    have : Etale ((g q).left ≫ U.hom) := by
      rw [MorphismProperty.Over.w (g q)]
      exact (V q).prop
    exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ U.hom U.prop this
  let 𝒰 : U.left.Cover (precoverage @Etale) :=
    Cover.mkOfCovers U.left (fun q ↦ (V q).left) (fun q ↦ (g q).left)
      (fun q ↦ ⟨q, hgq q⟩) (fun q ↦ inferInstance)
  letI (q : U.left) : (𝒰.X q).Over X := ⟨(V q).hom⟩
  letI : U.left.Over X := ⟨U.hom⟩
  letI : 𝒰.Over X :=
    { over := inferInstance
      isOver_map := fun q ↦ ⟨MorphismProperty.Over.w (g q)⟩ }
  refine ⟨𝒰, inferInstance, fun q ↦ (V q).prop, ?_⟩
  rintro - - ⟨q⟩
  exact hgS q

open GrothendieckTopology in
instance : HasEnoughPoints.{u} X.smallEtaleTopology :=
  ⟨_, inferInstance, isConservativeFamilyOfPoints_geometricPoint⟩

open GrothendieckTopology in
/-- The universe lifts of the geometric points form a conservative family of
`Type (u + 1)`-valued points of the small étale site. This allows checking isomorphisms
of sheaves valued in categories concrete over `Type (u + 1)` (such as `Ab.{u + 1}`) on
stalks at geometric points. -/
theorem isConservativeFamilyOfPoints_geometricPoint_ulift :
    (ObjectProperty.ofObj fun p : X ↦
        Point.ulift.{u + 1}
          (Etale.geometricPoint (X.sepClosurePoint p))).IsConservativeFamilyOfPoints :=
  ObjectProperty.IsConservativeFamilyOfPoints.ulift.{u + 1}
    isConservativeFamilyOfPoints_geometricPoint

open GrothendieckTopology in
instance : HasEnoughPoints.{u + 1} X.smallEtaleTopology :=
  ⟨_, inferInstance, isConservativeFamilyOfPoints_geometricPoint_ulift⟩

open GrothendieckTopology in
/-- A morphism of sheaves on the small étale site of `X` valued in a suitable concrete
category over `Type (u + 1)` (e.g. `Ab.{u + 1}`) is an isomorphism if and only if it
induces isomorphisms on stalks at the geometric points of `X`. -/
theorem isIso_iff_sheafFiber_geometricPoint {A : Type u'} [Category.{v'} A]
    [HasColimitsOfSize.{u + 1, u + 1} A]
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (M N : A), FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {K L : Sheaf X.smallEtaleTopology A} (f : K ⟶ L) :
    IsIso f ↔ ∀ p : X,
      IsIso ((Point.ulift.{u + 1}
        (Etale.geometricPoint (X.sepClosurePoint p))).sheafFiber.map f) := by
  rw [(isConservativeFamilyOfPoints_geometricPoint_ulift.jointlyReflectIsomorphisms
    A).isIso_iff]
  constructor
  · exact fun h p ↦ h ⟨_, ⟨p⟩⟩
  · rintro h ⟨Φ, ⟨p⟩⟩
    exact h p

open GrothendieckTopology in
/-- Version of `isIso_iff_sheafFiber_geometricPoint` with the stalks computed as
colimits over the `u`-small categories of étale neighbourhoods. -/
theorem isIso_iff_sheafFiber_geometricPoint' {A : Type u'} [Category.{v'} A]
    [HasColimitsOfSize.{u, u} A] [HasColimitsOfSize.{u + 1, u + 1} A]
    {FC : A → A → Type*} {CC : A → Type (u + 1)}
    [∀ (M N : A), FunLike (FC M N) (CC M) (CC N)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {K L : Sheaf X.smallEtaleTopology A} (f : K ⟶ L) :
    IsIso f ↔ ∀ p : X,
      IsIso ((Etale.geometricPoint (X.sepClosurePoint p)).sheafFiber.map f) := by
  rw [isIso_iff_sheafFiber_geometricPoint f]
  refine forall_congr' fun p ↦ ?_
  exact (MorphismProperty.isomorphisms A).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso
      (Point.uliftSheafFiberIso
        (Etale.geometricPoint (X.sepClosurePoint p)))).app (Arrow.mk f))

end SepClosurePoint

end AlgebraicGeometry.Scheme
