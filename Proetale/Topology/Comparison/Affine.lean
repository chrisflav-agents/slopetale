/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.CategoryTheory.Limits.Preserves.Limits
import Proetale.Topology.Comparison.Etale
import Proetale.Topology.Coherent.Affine
import Proetale.Mathlib.CategoryTheory.Sites.Continuous
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Basic
import Proetale.Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Proetale.Pro.PresheafColimit
import Proetale.Morphisms.ProAffineEtale
import Proetale.Topology.LocalProperties
import Proetale.Algebra.IndWeaklyEtale
import Proetale.Mathlib.CategoryTheory.Sites.Grothendieck
import Proetale.Mathlib.CategoryTheory.Sites.Hypercover.Zero
import Proetale.Mathlib.AlgebraicGeometry.Sites.AffineRefinement

/-!
# Affine pro-étale site

In this file we study the small affine pro-étale site of a scheme `S`: Its objects
are affine schemes `X` that can be written as `X = limᵢ Xᵢ` where `Xᵢ` is an
affine étale `S`-scheme.
-/

universe w u

open CategoryTheory MorphismProperty Limits

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : C ⥤ D) (R : D ⥤ C)
  {A : Type*} [Category A]

namespace MorphismProperty

variable {J : Type*} [Category* J] {C : Type*} [Category* C]
variable {P Q : MorphismProperty C} [Q.IsMultiplicative]

@[simps!]
def Over.lift' (D : J ⥤ C) {S : C} (s : D ⟶ (Functor.const J).obj S)
    (hs : ∀ j, P (s.app j)) (hD : ∀ {i j} (f : i ⟶ j), Q (D.map f)) :
    J ⥤ P.Over Q S :=
  Over.lift (CategoryTheory.Over.lift D s) hs hD

@[simps]
def Over.iteratedLift {S : C} (D : J ⥤ P.Over Q S)
    {X : P.Over Q S}
    (s : D ⟶ (Functor.const J).obj X) (hs : ∀ j, P (s.app j).left)
    (hD : ∀ {i j} (f : i ⟶ j), Q (D.map f).left := by cat_disch) :
    J ⥤ P.Over Q X.left where
  obj j := Over.mk _ (s.app j).left (hs j)
  map {i j} f := Over.homMk (D.map f).left
    (by simpa [-NatTrans.naturality] using congr($(s.naturality f).left)) (hD f)

end MorphismProperty

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The pro-étale affine site is the full subcategory of the pro-étale site where every
object can be written as a cofiltered limit of affine étale schemes over `S`. -/
def AffineProEt (S : Scheme.{u}) : Type (u + 1) :=
  proAffineEtale.Over ⊤ S

abbrev AffineProEt.ofEtale {S : Scheme.{u}} {X : Scheme.{u}} [IsAffine X] (f : X ⟶ S)
    [Etale f] :
    S.AffineProEt :=
  .mk _ f (.of_isAffine _)

variable (S : Scheme.{u})
variable (A : Type*) [Category A]

noncomputable instance : Category S.AffineProEt :=
  inferInstanceAs <| Category <| proAffineEtale.Over ⊤ S

namespace AffineProEt

variable {S}

@[simps!]
def mk {X : Scheme.{u}} (f : X ⟶ S) (hf : proAffineEtale f) : S.AffineProEt :=
  MorphismProperty.Over.mk _ _ hf

lemma proAffineEtale_hom {X Y : S.AffineProEt} (f : X ⟶ Y) : proAffineEtale f.left :=
  MorphismProperty.of_postcomp _ _ Y.hom Y.prop <| by simpa using X.prop

-- TODO: move me
instance {X Y : S.ProEt} (f : X ⟶ Y) : WeaklyEtale f.left :=
  letI hX : WeaklyEtale X.hom := X.prop
  letI hY : WeaklyEtale Y.hom := Y.prop
  letI hcomp : WeaklyEtale (f.left ≫ Y.hom) := Over.w f ▸ hX
  @WeaklyEtale.of_comp _ _ _ f.left Y.hom hcomp hY

/-- The inclusion of the affine pro-étale site into the pro-étale site. -/
@[simps! map]
def toProEt (S : Scheme.{u}) : S.AffineProEt ⥤ S.ProEt :=
  MorphismProperty.Over.changeProp _ proAffineEtale_le_weaklyEtale le_rfl

@[simp]
lemma toProEt_obj_left (X : S.AffineProEt) : ((toProEt S).obj X).left = X.left := rfl

@[simp]
lemma toProEt_obj_hom (X : S.AffineProEt) : ((toProEt S).obj X).hom = X.hom := rfl

instance : (toProEt S).Full :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ proAffineEtale_le_weaklyEtale _).Full
instance : (toProEt S).Faithful :=
  inferInstanceAs <| (MorphismProperty.Over.changeProp _ proAffineEtale_le_weaklyEtale le_rfl).Faithful

/-- Every object of `S.AffineProEt` has affine underlying scheme. -/
instance (X : S.AffineProEt) : IsAffine X.left :=
  AlgebraicGeometry.proAffineEtale_isAffine_source X.prop

/-- `proAffineEtale` is closed under `WalkingCospan`-limits in `Over S`: the pullback
of a cospan in `Over S` whose three objects have `proAffineEtale` structural maps
again has `proAffineEtale` structural map. This is the affine-target replacement for
`MorphismProperty.Over.closedUnderLimitsOfShape_pullback`: `proAffineEtale` is *not*
stable under arbitrary base change, but it is stable along `IsAffineHom` morphisms,
and the cospan legs we base-change along here are maps between affine schemes. -/
instance : (proAffineEtale.overObj (X := S)).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    haveI : ∀ j : WalkingCospan, IsAffine (p.diag.obj j).left := fun j =>
      AlgebraicGeometry.proAffineEtale_isAffine_source (p.prop_diag_obj j)
    haveI : IsAffineHom (p.diag.map WalkingCospan.Hom.inl).left :=
      isAffineHom_of_isAffine _
    -- The explicit type annotation forces Lean to compose `Over.forget S` with `p.diag`
    -- and unfold to `.left`, matching the `IsAffineHom` instance above.
    have h : IsPullback ((p.π.app .left).left) ((p.π.app .right).left)
        ((p.diag.map WalkingCospan.Hom.inl).left) ((p.diag.map WalkingCospan.Hom.inr).left) :=
      IsPullback.of_isLimit_cone <|
        Limits.isLimitOfPreserves (CategoryTheory.Over.forget S) p.isLimit
    rw [MorphismProperty.overObj_iff,
      show Y.hom = (p.π.app .left).left ≫ (p.diag.obj .left).hom by simp]
    refine proAffineEtale.comp_mem _ _ ?_ (p.prop_diag_obj _)
    refine MorphismProperty.IsStableUnderBaseChangeAlong.of_isPullback h.flip ?_
    exact MorphismProperty.of_postcomp _ _ (p.diag.obj WalkingCospan.one).hom
      (p.prop_diag_obj .one) (by simpa using p.prop_diag_obj .right)

instance : HasPullbacks (AffineProEt S) := by
  apply +allowSynthFailures MorphismProperty.Comma.hasLimitsOfShape_of_closedUnderLimitsOfShape
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (Over S))
  · exact inferInstanceAs ((proAffineEtale.overObj (X := S)).IsClosedUnderLimitsOfShape _)

/-- The affine pro-étale site embeds densely in the pro-étale site. The key ingredient
of the proof is the commutative algebra lemma `RingHom.WeaklyEtale.exists_indEtale_comp`. -/
instance isCoverDense_toProEt : (toProEt S).IsCoverDense (ProEt.topology S) := by
  wlog hS : ∃ R, S = Spec R generalizing S
  · let X (i : S.affineCover.I₀) : S.AffineProEt := .ofEtale (S.affineCover.f i)
    let f (i : S.affineCover.I₀) : (toProEt S).obj (X i) ⟶ .mk (𝟙 S) := Over.homMk (S.affineCover.f i)
    refine .of_coversTop _ _ (fun i : S.affineCover.I₀ ↦ X i) ?_ ?_
    · dsimp
      rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ (.mk (𝟙 S))]
      · refine GrothendieckTopology.superset_covering
          (S := Sieve.ofArrows _ f) _ ?_ ?_
        · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
          intro i
          -- TODO: make this a separate lemma
          rw [Sieve.mem_ofObjects_iff]
          use i
          constructor
          exact 𝟙 _
        · apply Precoverage.generate_mem_toGrothendieck
          simp only [ProEt.precoverage, Precoverage.mem_comap_iff, Functor.comp_obj,
            ProEt.forget_obj, Over.forget_obj, ProEt.mk_left, Presieve.map_ofArrows,
            toProEt_obj_left, Functor.comp_map, ProEt.forget_map, Over.forget_map]
          apply zariskiPrecoverage_le_propQCPrecoverage
          exact S.affineCover.mem₀
      · apply MorphismProperty.Over.mkIdTerminal
    · intro i
      have h1 : inverseImage (@WeaklyEtale)
          (MorphismProperty.Over.forget @WeaklyEtale ⊤ S ⋙ CategoryTheory.Over.forget S) = ⊤ := by
        rw [eq_top_iff]
        intro X Y f _
        simp only [inverseImage_iff, Functor.comp_obj, Comma.forget_obj, Over.forget_obj,
          Functor.comp_map, Comma.forget_map, Over.forget_map]
        infer_instance
      have h2 : proAffineEtale.inverseImage
          (MorphismProperty.Over.forget proAffineEtale ⊤ S ⋙ CategoryTheory.Over.forget S) = ⊤ := by
        rw [eq_top_iff]
        intro X Y f _
        exact proAffineEtale_hom _
      let eL : Over (X i) ≌ (X i).left.AffineProEt :=
        (CategoryTheory.MorphismProperty.Comma.equivOfEqTop _ _ h2 rfl rfl).symm.trans
          (MorphismProperty.Over.iteratedSliceEquiv _)
      let eR : (X i).left.ProEt ≌ Over ((toProEt S).obj (X i)) :=
        (MorphismProperty.Over.iteratedSliceEquiv <| (toProEt S).obj (X i)).symm.trans
            (CategoryTheory.MorphismProperty.Comma.equivOfEqTop _ _ h1)
      let e : Over.post (X := X i) (toProEt S) ≅
          (eL.functor ⋙ (toProEt <| (X i).left)) ⋙ eR.functor := by
        refine NatIso.ofComponents ?_ ?_
        · intro A
          refine Over.isoMk ?_ ?_
          · exact MorphismProperty.Over.isoMk (Iso.refl _) (by simp [eL, eR])
          · cat_disch
        · cat_disch
      rw [CategoryTheory.Functor.IsCoverDense.iff_of_natIso e]
      rw [CategoryTheory.Functor.IsCoverDense.comp_iff_of_isCoverDense]
      rw [CategoryTheory.Functor.IsCoverDense.comp_iff_of_isEquivalence]
      have heq : eR.functor.inducedTopology
          ((ProEt.topology S).over ((toProEt S).obj ((fun i ↦ X i) i))) =
            ProEt.topology _ := by
        rw [ProEt.topology_eq_inducedTopology, ProEt.topology_eq_inducedTopology]
        dsimp
        ext U R
        -- Apply `mem_over_iff` once more on both sides to reduce both memberships
        -- to `proetaleTopology` evaluated on `U.left`, then unfold the composite
        -- pushforwards. Both sides become `Sieve.functorPushforward F R ∈
        -- proetaleTopology U.left` for definitionally equal functors `F`.
        rw [Functor.mem_inducedTopology_sieves_iff, GrothendieckTopology.mem_over_iff,
          Functor.mem_inducedTopology_sieves_iff, GrothendieckTopology.mem_over_iff,
          Functor.mem_inducedTopology_sieves_iff, GrothendieckTopology.mem_over_iff]
        dsimp only [Sieve.overEquiv, Equiv.coe_fn_mk]
        refine iff_of_eq ?_
        congr 1
        · -- Establish LHS sieve = RHS sieve by merging both into a single
          -- composite-functor pushforward and using definitional equality.
          have hL : Sieve.functorPushforward (CategoryTheory.Over.forget S)
              (Sieve.functorPushforward (ProEt.forget S)
                (Sieve.functorPushforward (CategoryTheory.Over.forget ((toProEt S).obj (X i)))
                  (Sieve.functorPushforward eR.functor R))) =
              Sieve.functorPushforward
                (eR.functor ⋙ CategoryTheory.Over.forget ((toProEt S).obj (X i)) ⋙
                  ProEt.forget S ⋙ CategoryTheory.Over.forget S) R := by
            rw [Sieve.functorPushforward_comp eR.functor _ R,
                Sieve.functorPushforward_comp
                  (CategoryTheory.Over.forget ((toProEt S).obj (X i)))
                  (ProEt.forget S ⋙ CategoryTheory.Over.forget S) _,
                Sieve.functorPushforward_comp (ProEt.forget S)
                  (CategoryTheory.Over.forget S) _]
          have hR : Sieve.functorPushforward (CategoryTheory.Over.forget (X i).left)
              (Sieve.functorPushforward (ProEt.forget (X i).left) R) =
              Sieve.functorPushforward
                (ProEt.forget (X i).left ⋙ CategoryTheory.Over.forget (X i).left) R := by
            rw [Sieve.functorPushforward_comp]
          exact hL.trans hR.symm
      rw [heq]
      exact this ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hS
  constructor
  intro U
  wlog hU : ∃ (S : CommRingCat.{u}) (g : Spec S ⟶ Spec R) (_ : WeaklyEtale g),
      U = .mk g generalizing U
  · let X (i : U.left.affineCover.I₀) : (Spec R).ProEt :=
      @Scheme.ProEt.mk _ _ (U.left.affineCover.f i ≫ U.hom)
        (MorphismProperty.comp_mem (W := @WeaklyEtale) _ _ inferInstance U.prop)
    let f (i : U.left.affineCover.I₀) : X i ⟶ U :=
      haveI : WeaklyEtale (U.left.affineCover.f i ≫ U.hom) :=
        MorphismProperty.comp_mem (W := @WeaklyEtale) _ _ inferInstance U.prop
      Over.homMk (U.left.affineCover.f i) rfl
    have H (i) := this (X i) ⟨_, U.left.affineCover.f i ≫ U.hom, _, rfl⟩
    refine GrothendieckTopology.transitive_of_presieve (.ofArrows _ f) ?_ _ ?_
    · apply Precoverage.generate_mem_toGrothendieck
      apply zariskiPrecoverage_le_propQCPrecoverage
      simp only [Functor.comp_obj, ProEt.forget_obj, Over.forget_obj, Presieve.map_ofArrows,
        Functor.comp_map, ProEt.forget_map, Over.forget_map]
      exact U.left.affineCover.mem₀
    · intro Y g ⟨i⟩
      refine GrothendieckTopology.superset_covering _ ?_ (H i)
      exact Sieve.le_pullback_coverByImage (toProEt (Spec R)) (f i)
  obtain ⟨S, g, hg, rfl⟩ := hU
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  simp only [WeaklyEtale.Spec_iff] at hg
  obtain ⟨T, _, g, h₁, h₂, h₃⟩ := hg.exists_indEtale_comp
  let U : AffineProEt (Spec R) := mk (Spec.map (CommRingCat.ofHom g) ≫ Spec.map φ) <| by
    rwa [← Spec.map_comp, proAffineEtale_Spec_iff]
  let g' : (toProEt _).obj U ⟶ ProEt.mk (Spec.map φ) :=
    Over.homMk (Spec.map <| CommRingCat.ofHom g) rfl
  haveI : IsAffine U.left := by dsimp [U]; infer_instance
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective] at h₂
  haveI : Surjective (Over.Hom.left (Comma.Hom.hom g')) := by
    dsimp [g']
    constructor
    exact h₂.right
  haveI : QuasiCompact (Over.Hom.left (Comma.Hom.hom g')) := by
    dsimp [g']
    infer_instance
  refine GrothendieckTopology.superset_covering (S := .generate <| .singleton g') _ ?_ ?_
  · rw [Sieve.generate_le_iff]
    intro _ _ ⟨⟩
    apply Presieve.in_coverByImage
  · apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.precoverage]
    simp only [Precoverage.mem_comap_iff, Functor.comp_obj, ProEt.forget_obj, Over.forget_obj,
      ProEt.mk_left, Presieve.map_singleton, toProEt_obj_left, Functor.comp_map, ProEt.forget_map,
      Over.forget_map]
    refine Hom.singleton_mem_propQCPrecoverage (f := g'.hom.left) ?_
    show WeaklyEtale (Spec.map (CommRingCat.ofHom g))
    rw [WeaklyEtale.Spec_iff]
    exact h₁.weaklyEtale

instance : (toProEt S).LocallyCoverDense (ProEt.zariskiTopology S) := by
  -- `LocallyCoverDense` only quantifies over `X : AffineProEt` (NOT over arbitrary
  -- `Y : ProEt`), so we may use that `X.left` is affine and `X.hom : X.left → S`
  -- is `proAffineEtale`. The basic-open affine cover of `X.left` gives, for any
  -- Zariski cover sieve `T` of `(toProEt).obj X`, a refinement contained in
  -- `T ∩ image(toProEt)`:
  --
  --   * each basic open `D(f) ↪ X.left` is an open immersion of affine schemes,
  --     hence `Etale` and source `IsAffine`, hence
  --     `proAffineEtale (D(f) ↪ X.left)` by `proAffineEtale.of_isAffine`;
  --   * composing with `X.hom` (proAffineEtale) yields `proAffineEtale (D(f) → S)`
  --     by `proAffineEtale.IsStableUnderComposition`;
  --   * so each `D(f)` defines an object of `AffineProEt S`, and the basic-open
  --     family is a Zariski cover (open immersion family with surjective union).
  --
  -- NOTE: `IsCoverDense (ProEt.zariskiTopology)` does NOT hold in general
  -- (a generic `Y : ProEt` has `Y.hom` only `WeaklyEtale`, so its affine opens
  -- need not be `proAffineEtale` over `S`). Hence we must prove
  -- `LocallyCoverDense` directly rather than via `locallyCoverDense_of_isCoverDense`.
  refine ⟨fun {X} T => ?_⟩
  -- zariskiTopology S = (Over.forget WeaklyEtale ⊤ S).inducedTopology (overGrothendieckTopology @IsOpenImmersion S)
  -- so T.property is definitionally: T.val.functorPushforward (Over.forget ...) ∈ overGrothendieckTopology ...
  -- We state hTP at X.toComma so that after rw, the cover is over X.toComma.left = X.left.
  have hTP : T.val.functorPushforward (MorphismProperty.Over.forget @WeaklyEtale ⊤ S) ∈
      S.overGrothendieckTopology @IsOpenImmersion X.toComma :=
    T.property
  obtain ⟨𝒰, h𝒰, hle⟩ :=
    (AlgebraicGeometry.Scheme.mem_overGrothendieckTopology (S := S) (P := @IsOpenImmersion)
      X.toComma _).mp hTP
  -- 𝒰 : Cover (precoverage @IsOpenImmersion) X.toComma.left (= X.left definitionally)
  -- h𝒰 : 𝒰.Over S
  -- hle : 𝒰.toPresieveOver ≤ (T.val.functorPushforward (Over.forget WeaklyEtale ⊤ S)).arrows
  -- Extract surjectivity for the basic-open refinement
  have hcov : ⋃ j, Set.range (𝒰.f j).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    simp only [Set.mem_iUnion, Set.mem_range]
    obtain ⟨j, y, hy⟩ := Scheme.Cover.exists_eq 𝒰 x
    exact ⟨j, y, hy⟩
  haveI hXAff : IsAffine X.toComma.left := proAffineEtale_isAffine_source X.prop
  obtain ⟨idx, g, e, hmem, he⟩ :=
    AlgebraicGeometry.exists_basicOpen_lift_of_isAffine_cover 𝒰.f hcov
  -- idx : X.toComma.left → 𝒰.I₀
  -- g : X.toComma.left → Γ(X.toComma.left, ⊤)
  -- e : ∀ x, (X.toComma.left.basicOpen (g x) : Scheme) ⟶ 𝒰.X (idx x)
  -- hmem : ∀ x, x ∈ X.toComma.left.basicOpen (g x)
  -- he : ∀ x, e x ≫ 𝒰.f (idx x) = (X.toComma.left.basicOpen (g x)).ι
  -- Build AffineProEt objects Zx x and morphisms ix x : Zx x ⟶ X
  let Zx : X.toComma.left → S.AffineProEt := fun x =>
    AffineProEt.mk ((X.toComma.left.basicOpen (g x)).ι ≫ X.hom)
      (proAffineEtale.comp_mem _ _ (proAffineEtale.of_isAffine _) X.prop)
  let ix : ∀ x, Zx x ⟶ X := fun x =>
    MorphismProperty.Over.homMk (X.toComma.left.basicOpen (g x)).ι
  -- Show each (toProEt S).map (ix x) ∈ T.val
  have hix : ∀ x : X.toComma.left, T.val ((toProEt S).map (ix x)) := by
    intro x
    -- (𝒰.f (idx x)).asOver S ∈ (T.val.functorPushforward (Over.forget WeaklyEtale ⊤ S)).arrows
    have hjx : 𝒰.toPresieveOver ((𝒰.f (idx x)).asOver S) := ⟨idx x⟩
    obtain ⟨Z_j, h_j, k_j, hTh_j, hcomp_j⟩ :=
      hle ((𝒰.X (idx x)).asOver S) ((𝒰.f (idx x)).asOver S) hjx
    -- hTh_j : T.val h_j
    -- hcomp_j : (𝒰.f (idx x)).asOver S = k_j ≫ (Over.forget WeaklyEtale ⊤ S).map h_j
    -- Extract the scheme-level factoring k_j.left ≫ h_j.left = 𝒰.f (idx x)
    have hk_over : k_j.left ≫ h_j.left = 𝒰.f (idx x) := by
      have heq := congr_arg Over.Hom.left hcomp_j
      simp only [Over.comp_left, OverClass.asOverHom_left, MorphismProperty.Comma.forget_map,
        MorphismProperty.Comma.Hom.hom_left] at heq
      exact heq.symm
    -- Z_j.hom = h_j.left ≫ X.hom (from the Over condition on h_j)
    have hZj : Z_j.hom = h_j.left ≫ X.hom := by
      have := h_j.toCommaMorphism.w
      simp at this
      exact this.symm
    -- (e x ≫ k_j.left) ≫ h_j.left = (X.left.basicOpen (g x)).ι
    have h_assoc : (e x ≫ k_j.left) ≫ h_j.left = (X.toComma.left.basicOpen (g x)).ι :=
      (Category.assoc _ _ _).trans ((congrArg (e x ≫ ·) hk_over).trans (he x))
    -- Build the over-condition for f_x : (toProEt S).obj (Zx x) ⟶ Z_j
    -- ((e x ≫ k_j.left) ≫ Z_j.hom = (e x ≫ k_j.left) ≫ (h_j.left ≫ X.hom)
    --   = ((e x ≫ k_j.left) ≫ h_j.left) ≫ X.hom = (X.left.basicOpen (g x)).ι ≫ X.hom = (Zx x).hom
    have heq : (e x ≫ k_j.left) ≫ Z_j.hom = (Zx x).hom :=
      (congrArg ((e x ≫ k_j.left) ≫ ·) hZj).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.hom) h_assoc).trans rfl))
    -- f_x : (toProEt S).obj (Zx x) ⟶ Z_j in ProEt S
    let f_x : (toProEt S).obj (Zx x) ⟶ Z_j :=
      MorphismProperty.Over.homMk (e x ≫ k_j.left) heq
    -- T.val (f_x ≫ h_j) by downward closure; then identify with (toProEt S).map (ix x)
    have hT_comp : T.val (f_x ≫ h_j) := T.val.downward_closed hTh_j f_x
    have heq_map : f_x ≫ h_j = (toProEt S).map (ix x) := by
      apply MorphismProperty.Over.Hom.ext
      exact h_assoc
    rw [← heq_map]
    exact hT_comp
  -- Prove the goal: the sieve (T.val.functorPullback (toProEt S)).functorPushforward (toProEt S)
  -- is in zariskiTopology S ((toProEt S).obj X).
  -- Use mem_toGrothendieck_smallPretopology: it suffices to provide, for each x : X.left,
  -- a ProEt-morphism f : Zx x ⟶ X with IsOpenImmersion f.left and T.val ((toProEt S).map (ix x)).
  simp only [ProEt.zariskiTopology,
    AlgebraicGeometry.Scheme.smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology]
  apply (AlgebraicGeometry.Scheme.mem_toGrothendieck_smallPretopology _ _).mpr
  intro x
  refine ⟨(toProEt S).obj (Zx x), (toProEt S).map (ix x), ⟨x, hmem x⟩, ?_,
    inferInstanceAs (IsOpenImmersion (X.left.basicOpen (g x)).ι), rfl⟩
  -- Show (T.val.functorPullback (toProEt S)).functorPushforward (toProEt S) ((toProEt S).map (ix x))
  exact ⟨Zx x, ix x, 𝟙 _, hix x, (Category.id_comp _).symm⟩

variable (S)

noncomputable def topology : GrothendieckTopology S.AffineProEt :=
  (toProEt S).inducedTopology (ProEt.topology S)

noncomputable def zariskiTopology : GrothendieckTopology S.AffineProEt :=
  (toProEt S).inducedTopology (ProEt.zariskiTopology S)

instance : (toProEt S).IsContinuous (topology S) (ProEt.topology S) := by
  dsimp [topology]
  infer_instance

instance : (toProEt S).IsDenseSubsite (topology S) (ProEt.topology S) where
  functorPushforward_mem_iff := by rfl

/-- Restriction along inclusion of the affine pro-étale site into the pro-étale site induces an
equivalence of categories of sheaves of `Ab.{u + 1}`, or more generally any category
having large enough limits. -/
instance isEquivalence_sheafPushforwardContinuous_toProEt {A : Type*} [Category* A]
    [HasLimitsOfSize.{u, u + 1} A] :
    ((toProEt.{u} S).sheafPushforwardContinuous A
      (topology S) (ProEt.topology S)).IsEquivalence :=
  inferInstance

instance : (toProEt S).IsContinuous (topology S) (ProEt.topology S) := by
  change (toProEt S).IsContinuous ((toProEt S).inducedTopology (ProEt.topology S))
    (ProEt.topology S)
  infer_instance

/-- The restriction of sheafs on the pro-étale site to sheaf on the affine pro-étale site. -/
noncomputable
def sheafPushforward :
    Sheaf (ProEt.topology S) A ⥤ Sheaf (AffineProEt.topology S) A :=
  (toProEt S).sheafPushforwardContinuous _ _ _

/-- If `q : Z ⟶ X` is a morphism in the affine pro-étale site `S.AffineProEt` whose underlying
scheme map `q.hom.left` is surjective, then for any other arrow `g : Y ⟶ X` the second projection
of the (categorical) pullback in `S.AffineProEt` is also surjective on underlying schemes.
This uses that `proAffineEtale.overObj` is closed under `WalkingCospan`-limits (the instance at the
top of this file), so the forgetful functor `S.AffineProEt ⥤ Over S` creates this pullback, and
hence the further forgetful `Over S ⥤ Scheme` preserves it (the latter preserves all connected
limits). The scheme-level base change is then surjective by
`MorphismProperty.IsStableUnderBaseChange @Surjective`. -/
private lemma AffineProEt.surjective_pullback_snd
    {S : Scheme.{u}} {X Y Z : S.AffineProEt}
    (q : Z ⟶ X) (g : Y ⟶ X) (hq : Surjective q.hom.left) :
    Surjective (Limits.pullback.snd q g).hom.left := by
  -- Bridge `overObj` and `commaObj` closure instances (they are def-equal but TC search
  -- doesn't unfold one to the other).
  haveI hclosed :
      (proAffineEtale.commaObj (𝟭 Scheme.{u}) (Functor.fromPUnit.{0} S)).IsClosedUnderLimitsOfShape
        WalkingCospan :=
    inferInstanceAs ((proAffineEtale.overObj (X := S)).IsClosedUnderLimitsOfShape WalkingCospan)
  haveI : HasLimitsOfShape WalkingCospan
      (CategoryTheory.Comma (𝟭 Scheme.{u}) (Functor.fromPUnit.{0} S)) :=
    inferInstanceAs (HasLimitsOfShape WalkingCospan (CategoryTheory.Over S))
  -- Spell out the limit cone of `cospan q g` in `S.AffineProEt`.
  have hpb_aff : IsPullback (Limits.pullback.fst q g) (Limits.pullback.snd q g) q g :=
    IsPullback.of_hasPullback q g
  -- The forgetful functor `S.AffineProEt ⥤ Over S` creates `WalkingCospan` limits and hence
  -- preserves them.
  have hF₁ : IsPullback ((Limits.pullback.fst q g).hom) ((Limits.pullback.snd q g).hom)
      q.hom g.hom := by
    let F : S.AffineProEt ⥤ CategoryTheory.Over S :=
      MorphismProperty.Over.forget proAffineEtale ⊤ S
    haveI hlim : HasLimit (Limits.cospan q g ⋙ F) := Limits.hasLimitOfHasLimitsOfShape _
    haveI hcr : CreatesLimit (Limits.cospan q g) F :=
      MorphismProperty.Comma.forgetCreatesLimitOfClosed _ (Limits.cospan q g)
    haveI : HasLimit (Limits.cospan q g) :=
      hasLimit_of_created (Limits.cospan q g) F
    haveI : PreservesLimit (Limits.cospan q g) F :=
      preservesLimit_of_createsLimit_and_hasLimit (Limits.cospan q g) F
    exact hpb_aff.map F
  -- `Over S ⥤ Scheme` preserves connected limits (e.g. `WalkingCospan`).
  have h : IsPullback ((Limits.pullback.fst q g).hom.left)
      ((Limits.pullback.snd q g).hom.left) q.hom.left g.hom.left :=
    hF₁.map (CategoryTheory.Over.forget S)
  exact MorphismProperty.of_isPullback h hq

/-- Building block for round-24 OBJ C, sub-step (d): the canonical coproduct of a finite
family of étale-source affine morphisms to `S` is in `proAffineEtale`.

Given a finite family `f i : X i ⟶ S` where each `X i` is affine and each `f i` is
étale, the universal coproduct map `Sigma.desc f : ∐ᵢ X i ⟶ S` is `proAffineEtale`.
The proof reduces to: (i) finite ⨿ of affines is affine; (ii) étale is local at the
source, hence `Sigma.desc` of étales is étale (`IsZariskiLocalAtSource.sigmaDesc`); and
(iii) any `(Etale ⊓ ofObjectProperty IsAffine ⊤)`-morphism is in `proAffineEtale` via
`MorphismProperty.le_pro`.

For the *general* case where each `f i` is only assumed to be `proAffineEtale`
(not étale), one combines this single-stage version with the per-`i` cofiltered
presentations of `f i` (yielding a joint cofiltered diagram on `J := ∀ i, Jᵢ`)
and the fact that finite coproducts commute with cofiltered limits of affine
schemes (deeper categorical input, reducing on the ring side to "finite products
commute with filtered colimits in `CommRingCat`"). That deeper step is the
round-25 work.

`Sigma.desc` is taken in `Scheme.{u}`. -/
private lemma _root_.AlgebraicGeometry.proAffineEtale_sigmaDesc_etale
    {S : Scheme.{u}} {ι : Type u} [Fintype ι]
    {X : ι → Scheme.{u}} [∀ i, IsAffine (X i)]
    (f : ∀ i, X i ⟶ S) [∀ i, @Etale _ _ (f i)] :
    proAffineEtale (Limits.Sigma.desc f) := by
  haveI : IsAffine (∐ fun i => X i) := inferInstance
  refine MorphismProperty.le_pro _ _ ⟨?_, ?_⟩
  · exact IsZariskiLocalAtSource.sigmaDesc inferInstance
  · rw [ofObjectProperty_top_right_iff]
    infer_instance

/-- Helper (round 18 OBJ D, "H1"): given a cover sieve in the affine pro-étale topology of an
affine pro-étale object `Y`, there exists a single affine pro-étale arrow `q : Z ⟶ Y` lying in
the sieve with surjective underlying scheme map, together with base-change witnesses needed
to identify the pullback of the singleton sieve along any arrow of the cover with a fresh
singleton sieve generated by a surjective arrow. This is the packaged existential consumed
by `Presieve.isSheafFor_subsieve_aux` inside the body of `isSheaf` (branch2).

Mathematical content:

1. Unfold `AffineProEt.topology` via `IsDenseSubsite.functorPushforward_mem_iff` to obtain
   a qc weakly-étale cover of `(toProEt S).obj Y` in `ProEt.topology S`.
2. Extract a finite qc subcover via `mem_propQCPrecoverage_iff_exists_quasiCompactCover`.
3. For each cover member `X_i → Y.left`, take a finite affine open cover of `X_i` (each
   `U_{ij}` is affine).
4. The disjoint union `Z := ∐_{(i,j)} U_{ij}` is a finite coproduct of affines, hence affine,
   and `Z → Y.left` is a single qc surjective weakly-étale morphism.
5. Lift back through the affine-vs-pro-étale dense subsite to an `AffineProEt` arrow.
6. Base-change part: use `Sieve.pullbackArrows_comm` + `Presieve.pullback_singleton` to
   reduce the sieve equality to a singleton on the scheme pullback `pullback.snd q g`,
   then verify surjectivity via `MorphismProperty.IsStableUnderBaseChange @Surjective`
   together with the fact that `MorphismProperty.Over.forget proAffineEtale ⊤ S` creates
   pullbacks (via the `IsClosedUnderLimitsOfShape WalkingCospan` instance above).

This is the affine analogue of the construction at lines 247-298 (the WLOG-affine branch
of `isCoverDense_toProEt`), generalised from a single ProEt cover of `Spec R` to a sieve
of an arbitrary `AffineProEt S` object. Estimated effort: 100-160 LOC. -/
private lemma AffineProEt.exists_singleton_refinement
    {S : Scheme.{u}} {Y : S.AffineProEt} (T : Sieve Y)
    (hT : T.functorPushforward (AffineProEt.toProEt S) ∈
      ProEt.topology S ((AffineProEt.toProEt S).obj Y)) :
    ∃ (Z : S.AffineProEt) (q : Z ⟶ Y),
      T.arrows q ∧ Surjective q.hom.left ∧
      (∀ ⦃W : S.AffineProEt⦄ ⦃g : W ⟶ Y⦄, T.arrows g →
        ∃ (Z' : S.AffineProEt) (q' : Z' ⟶ W),
          Surjective q'.hom.left ∧
          (Sieve.generate (Presieve.singleton q)).pullback g =
            Sieve.generate (Presieve.singleton q')) := by
  -- Strategy: (steps 1-6 in the docstring above). This packages the singleton refinement
  -- that bridges qc weakly-étale covers of an `AffineProEt` object to single surjective
  -- arrows in the `AffineProEt` category. The construction extends the affine WLOG branch
  -- of `isCoverDense_toProEt` (file lines 247-298) to handle arbitrary sieves rather than
  -- only ProEt-side cover sieves.
  --
  -- Round 21 partial progress: the base-change clause is FULLY closed using
  -- `AffineProEt.surjective_pullback_snd` (proven round 20, at L448) together with
  -- `Sieve.pullbackArrows_comm` and `Presieve.pullback_singleton`. The remaining
  -- single scoped `sorry` covers the cofiltered-descent extraction of
  -- `q : Z ⟶ Y` with `T.arrows q ∧ Surjective q.hom.left`, namely:
  --
  --   (a) From `hT : T.functorPushforward (toProEt S) ∈ ProEt.topology S _`, extract
  --       a finite qc weakly-étale family `{V_i → (toProEt S).obj Y}` whose images
  --       cover (via the inductive description of `Precoverage.toGrothendieck`).
  --   (b) Each member `V_i → (toProEt S).obj Y` factors through `(toProEt S).map f_i`
  --       with `f_i : W_i ⟶ Y` in `T` (definition of `functorPushforward`).
  --   (c) Refine each `V_i` by a finite affine open cover (basic-open data on the
  --       affine `Y.left`-pullback) to ensure all pieces are affine.
  --   (d) Take the disjoint union `Z₀ := ∐ V_{ij}` (finite ∐ of affines = affine);
  --       on the proAffineEtale side, finite coproducts commute with cofiltered
  --       limits in the affine category (via `Spec ⊣` to a filtered colimit of
  --       finite products of étale algebras over each transition stage).
  --   (e) Apply `RingHom.WeaklyEtale.exists_indEtale_comp` (or the analogous
  --       `Algebra.WeaklyEtale.exists_indEtale`) on the resulting weakly-étale ring
  --       map `Γ(Y) → Γ(Z₀)` to produce a single ind-étale faithfully flat
  --       extension `Γ(Y) → A`, giving `q : Spec A ⟶ Y` in `S.AffineProEt`.
  --       Surjectivity follows from `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`
  --       (cf. L278); membership in `T` follows by downward closure since `Spec A`
  --       factors through `Z₀ → V_i → (toProEt S).map f_i` for any covering `i`.
  --
  -- Estimated remaining LOC: 80-150. The infrastructure pieces (a)–(b) are routine
  -- (use `Precoverage.mem_iff_exists_zeroHypercover` after unfolding `ProEt.topology`);
  -- (c) is bookkeeping; (d) requires the finite-coproduct-of-proAffineEtale lemma
  -- (likely a new helper in `Proetale/Morphisms/ProAffineEtale.lean`); (e) parallels
  -- L269-298 of the existing `isCoverDense_toProEt` proof and uses
  -- `RingHom.WeaklyEtale.exists_indEtale_comp` directly.
  obtain ⟨Z, q, hqmem, hqsurj⟩ :
      ∃ (Z : S.AffineProEt) (q : Z ⟶ Y),
        T.arrows q ∧ Surjective q.hom.left := by
    -- (a)+(b) sub-extraction (round 22). The `T.functorPushforward (toProEt S)`
    -- topology-membership `hT` unfolds via
    -- `Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition` to a
    -- `ProEt.precoverage S`-cover `R0` together with `hR0_le : R0 ≤
    -- (T.functorPushforward (toProEt S)).arrows`, and then via
    -- `Precoverage.mem_iff_exists_zeroHypercover` to a concrete `ZeroHypercover`
    -- `𝒰0` of `(toProEt S).obj Y` in `ProEt.precoverage S`. Each `𝒰0.f i`
    -- factors through `(toProEt S).map f_i` for some `f_i : W_i ⟶ Y` in `T`
    -- (definition of `Sieve.functorPushforward`). This yields the (a)+(b) data
    -- of the docstring plan.
    --
    -- (c)+(d)+(e): the remaining sub-steps construct a single surjective
    -- arrow `q : Z ⟶ Y` in `S.AffineProEt` from the family `{f_i}` by:
    --   (c) refining each `W_i` by an affine open cover,
    --   (d) taking the disjoint union `∐ U_{ij}` (finite ∐ of affines = affine),
    --       and using cofiltered descent on `proAffineEtale.commaObj` for finite
    --       coproducts,
    --   (e) applying `RingHom.WeaklyEtale.exists_indEtale_comp` on the
    --       resulting weakly étale ring map `Γ(Y) → Γ(Z₀)` to package as a
    --       single faithfully flat ind-étale extension and bundle as a
    --       `proAffineEtale`-arrow.
    -- These three are deep enough that this prover leaves them as the single
    -- scoped sorry below; see `task_results/Topology_Comparison_Affine.lean.md`
    -- for the planned proof outline.
    classical
    -- (a) Unfold `hT` via `mem_toGrothendieck_iff_of_isStableUnderComposition`
    --     to a `ProEt.precoverage S`-cover `R0` of `(toProEt S).obj Y` with
    --     `R0 ≤ T.functorPushforward (toProEt S)`.
    obtain ⟨R0, hR0_mem, hR0_le⟩ :=
      (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
        (J := ProEt.precoverage S)).mp hT
    -- Extract a ZeroHypercover from the precoverage membership.
    obtain ⟨𝒰0, hR0_eq⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR0_mem
    -- (b) Each `𝒰0.f i` factors through `(toProEt S).map (f_i : W_i ⟶ Y)` for
    --     some `f_i ∈ T` by definition of `Sieve.functorPushforward`. Package
    --     this data via `Classical.choice`.
    have hfactor : ∀ i : 𝒰0.I₀,
        ∃ (W : S.AffineProEt) (a : 𝒰0.X i ⟶ (toProEt S).obj W) (f_i : W ⟶ Y),
          T.arrows f_i ∧ 𝒰0.f i = a ≫ (toProEt S).map f_i := by
      intro i
      have hi : (T.functorPushforward (toProEt S)).arrows (𝒰0.f i) :=
        hR0_le _ _ (hR0_eq ▸ Presieve.ofArrows.mk i)
      obtain ⟨W, f_i, a, hfi, hcomp⟩ := hi
      exact ⟨W, a, f_i, hfi, hcomp⟩
    choose W₀ a₀ f₀ hf₀mem hf₀comp using hfactor
    -- (c) Refine each `W₀ i` by the canonical affine open cover of its underlying
    -- scheme. For each `i : 𝒰0.I₀` and `j : (W₀ i).left.affineCover.I₀`,
    -- `(W₀ i).left.affineCover.X j` is affine and `(W₀ i).left.affineCover.f j`
    -- is an open immersion (hence étale). Bundle each affine piece as an
    -- `S.AffineProEt` object `U i j` with structure map
    -- `(W₀ i).left.affineCover.f j ≫ (W₀ i).hom`, and record the canonical arrow
    -- `qU i j : U i j ⟶ W₀ i` in `S.AffineProEt`. Composing through `f₀ i`
    -- gives a 2-indexed family of arrows `qU i j ≫ f₀ i : U i j ⟶ Y` lying in
    -- `T` by downward closure, with affine source.
    let U (i : 𝒰0.I₀) (j : (W₀ i).left.affineCover.I₀) : S.AffineProEt :=
      AffineProEt.mk ((W₀ i).left.affineCover.f j ≫ (W₀ i).hom)
        (proAffineEtale.comp_mem _ _ (proAffineEtale.of_isAffine _) (W₀ i).prop)
    let qU (i : 𝒰0.I₀) (j : (W₀ i).left.affineCover.I₀) : U i j ⟶ W₀ i :=
      MorphismProperty.Over.homMk ((W₀ i).left.affineCover.f j)
    have hqUmem (i : 𝒰0.I₀) (j : (W₀ i).left.affineCover.I₀) :
        T.arrows (qU i j ≫ f₀ i) :=
      T.downward_closed (hf₀mem i) (qU i j)
    -- (d)+(e) DEFERRED — see docstring plan: take the disjoint union
    -- `Z₀ := ∐_{(i,j)} U i j` (finite ∐ of affines = affine; cofiltered
    -- descent on `proAffineEtale.commaObj`), and apply
    -- `RingHom.WeaklyEtale.exists_indEtale_comp` on the resulting weakly étale
    -- ring map `Γ(Y) → Γ(Z₀)` to bundle the output as a single
    -- `proAffineEtale`-arrow `q : Z ⟶ Y` with `T.arrows q` and
    -- `Surjective q.hom.left`. Bookkeeping data (a)+(b)+(c) now in scope:
    -- `𝒰0 : ZeroHypercover (ProEt.precoverage S) ((toProEt S).obj Y)` with
    -- `hR0_le`, per-`i` tuple `(W₀ i, a₀ i, f₀ i, hf₀mem i, hf₀comp i)`, and
    -- per-`(i, j)` tuple `(U i j, qU i j, hqUmem i j)` with `U i j` affine.
    --
    -- ROUND 25 OBSTRUCTION DISCOVERED (Path B does NOT directly close the goal):
    -- The required `T.arrows q` for the produced `q : Z ⟶ Y` is the bottleneck.
    -- Sieves in `AffineProEt(S)` are closed under PRECOMPOSITION only — not under
    -- coproduct desc. The two natural Path-B candidates each fail this clause:
    --
    --   (P1) `q := Sigma.desc f₀ : ∐ W₀ i → Y` (as a `proAffineEtale`-arrow once
    --        the deferred finite-coproduct closure is proven):
    --        each `f₀ i ∈ T`, but `Sigma.desc f₀` is NOT a precomposition of any
    --        single `f₀ i`. Sieves do not have closure under `Sigma.desc`, so
    --        `T.arrows (Sigma.desc f₀)` is unprovable in general.
    --
    --   (P2) `q := (Spec A ⟶ Y)` from `RingHom.WeaklyEtale.exists_indEtale_comp`
    --        on `Γ(Y) → Γ(Z₀)`:
    --        `A` is the ind-étale closure of `Γ(Y)` inside `∏ Γ(W₀ i)`. There is
    --        no natural ring hom `Γ(W₀ i) → A` over `Γ(Y)` (only the reverse:
    --        `A → ∏ Γ(W₀ i) → Γ(W₀ i)`), so `Spec A ⟶ Y` does NOT factor
    --        through any single `f₀ i` in `AffineProEt(S)`, hence cannot be
    --        shown in `T` by downward closure.
    --
    -- A SINGLE surjective `q ∈ T` requires either:
    --   (R1) A modified statement weakening `T.arrows q` to
    --        `Sieve.generate (Presieve.singleton q) ≤ T` (still strong enough
    --        for the consumer at L772-798), OR
    --   (R2) Establishing closure of cover sieves under finite coproducts in
    --        `AffineProEt(S)` — i.e., proving that if `{f_i : W_i ⟶ Y} ⊆ T`
    --        jointly covers `Y` then there is a single coproduct arrow
    --        `q : ∐ W_i ⟶ Y` *in* `T`. This requires the cover sieve to be
    --        of "finite-coproduct-stable" shape, which is NOT a generic
    --        property of sieves in arbitrary Grothendieck topologies.
    --
    -- Both (R1) and (R2) are statement-level changes beyond a prover's mandate.
    -- The deeper fix is to refactor `exists_singleton_refinement`'s conclusion
    -- to (R1)'s form, then propagate the refactor through the L772-798 use site
    -- (which only needs `generate (singleton q) ≤ T` to apply
    -- `Presieve.isSheafFor_subsieve_aux`; `T.arrows q` is sufficient but not
    -- necessary).
    --
    -- Path-A (the general `finiteCoproduct_mem_proAffineEtale` route) is also
    -- blocked: it requires finite-coproducts-commute-with-cofiltered-limits
    -- (deferred in `Proetale/Morphisms/ProAffineEtale.lean:91,134`), AND even
    -- once Path-A is done, the `T.arrows` obligation remains unresolved.
    --
    -- This prover leaves the existential as `sorry`; see
    -- `task_results/Topology_Comparison_Affine.lean.md` for the recommended
    -- statement refactor (R1) and migration plan.
    sorry
  refine ⟨Z, q, hqmem, hqsurj, ?_⟩
  intro W g hg
  refine ⟨Limits.pullback q g, Limits.pullback.snd q g,
    AffineProEt.surjective_pullback_snd q g hqsurj, ?_⟩
  -- `(Sieve.generate (singleton q)).pullback g = Sieve.generate (singleton (pullback.snd q g))`,
  -- via `Sieve.pullbackArrows_comm` + `Presieve.pullback_singleton`.
  rw [← Sieve.pullbackArrows_comm g (Presieve.singleton q), Presieve.pullback_singleton]

/-- To show a presheaf of types is a sheaf on the affine pro-étale site, it suffices to show
it is a Zariksi sheaf and satifies the sheaf condition for single surjective morphisms. -/
lemma isSheaf {F : (AffineProEt S)ᵒᵖ ⥤ Type*}
    (h₁ : Presheaf.IsSheaf (zariskiTopology S) F)
    (h₂ : ∀ {U V : AffineProEt S} (f : U ⟶ V) [Surjective f.hom.left],
      (Presieve.singleton f).IsSheafFor F) :
    Presheaf.IsSheaf (topology S) F := by
  -- Strategy: The `AffineProEt.topology` is generated by Zariski covers together
  -- with singleton surjective qc covers. The proof of `isCoverDense_toProEt`
  -- (above) shows every cover of `U : AffineProEt` decomposes (via
  -- `GrothendieckTopology.transitive_of_presieve` applied with the affineCover
  -- of `U.left`) into:
  --   * a Zariski cover refining `U` by affine pieces `(U.left.affineCover i) → U`;
  --   * followed by, on each piece, a single surjective qc cover obtained from
  --     `WeaklyEtale.exists_indEtale_comp` and `Hom.singleton_mem_propQCPrecoverage`.
  -- Sheaf-ness on this transitive decomposition reduces to `h₁` (for Zariski step)
  -- and `h₂` (for the singleton-surjective step) via:
  --   * `Presheaf.IsSheaf.isSheafFor_of_transitive` (or similar transitivity lemma),
  --   * the `Sieve.bind` description matching the proof of `isCoverDense_toProEt`.
  -- TODO: formalize this. The structural skeleton is to apply
  -- `Presheaf.isSheaf_iff_isSheaf_forall` followed by transitivity on each cover.
  -- Strategy: apply `Presieve.isSheafFor_trans` with `T_Zar` the Zariski cover
  -- of `X` by basic opens of `X.left`, and `R` as the target sieve.
  -- branch1 (`IsSheafFor F T_Zar`) and branch3 (separatedness of `T_Zar.pullback f`)
  -- both follow from `h₁` (F is a Zariski sheaf). branch2 (singleton refinement
  -- on basic-open pieces via `exists_indEtale_comp` + `h₂`) remains open.
  rw [isSheaf_iff_isSheaf_of_type] at h₁ ⊢
  intro X R hR
  have hR' : R.functorPushforward (toProEt S) ∈ ProEt.topology S ((toProEt S).obj X) := hR
  classical
  haveI : IsAffine X.left := inferInstance
  -- Basic-open data on X.left from the trivial cover `{𝟙 X.left}`.
  obtain ⟨_, g, _, hmem, _⟩ :=
    AlgebraicGeometry.exists_basicOpen_lift_of_isAffine_cover (X := X.left)
      (f := fun (_ : Unit) => 𝟙 X.left)
      (by
        rw [Set.eq_univ_iff_forall]
        intro x
        refine Set.mem_iUnion.mpr ⟨(), ?_⟩
        exact ⟨x, by simp⟩)
  -- Build the basic-open pieces `Zx x` and inclusion arrows `ix x` (cf. L347–352).
  let Zx : X.left → S.AffineProEt := fun x =>
    AffineProEt.mk ((X.left.basicOpen (g x)).ι ≫ X.hom)
      (proAffineEtale.comp_mem _ _ (proAffineEtale.of_isAffine _) X.prop)
  let ix : ∀ x, Zx x ⟶ X := fun x =>
    MorphismProperty.Over.homMk (X.left.basicOpen (g x)).ι
  let T_Zar : Sieve X := Sieve.generate (Presieve.ofArrows _ ix)
  -- Membership in the AffineProEt zariski topology: definitionally,
  -- `T_Zar.functorPushforward (toProEt S) ∈ ProEt.zariskiTopology S _`.
  have hT_Zar_pf : T_Zar.functorPushforward (toProEt S) ∈
      ProEt.zariskiTopology S ((toProEt S).obj X) := by
    simp only [ProEt.zariskiTopology,
      AlgebraicGeometry.Scheme.smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology]
    apply (AlgebraicGeometry.Scheme.mem_toGrothendieck_smallPretopology _ _).mpr
    intro x
    refine ⟨(toProEt S).obj (Zx x), (toProEt S).map (ix x), ⟨x, hmem x⟩, ?_,
      inferInstanceAs (IsOpenImmersion (X.left.basicOpen (g x)).ι), rfl⟩
    -- Show `T_Zar.functorPushforward (toProEt S) ((toProEt S).map (ix x))`.
    refine ⟨Zx x, ix x, 𝟙 _, ?_, (Category.id_comp _).symm⟩
    exact ⟨Zx x, 𝟙 _, ix x, ⟨x⟩, Category.id_comp _⟩
  have hT_Zar_mem : T_Zar ∈ zariskiTopology S X := hT_Zar_pf
  refine Presieve.isSheafFor_trans F T_Zar R (h₁ T_Zar hT_Zar_mem) ?branch3 ?branch2
  case branch3 =>
    -- For each f ∈ R, the pullback `T_Zar.pullback f` is still a Zariski cover
    -- of the domain, by pullback stability of the Grothendieck topology.
    intro Y f _
    exact (h₁ _ ((zariskiTopology S).pullback_stable f hT_Zar_mem)).isSeparatedFor
  case branch2 =>
    -- ∀ f ∈ T_Zar (basic-open piece `Zx → X`), IsSheafFor F (R.pullback f).
    -- Strategy: `R.pullback f ∈ topology S (dom f)` by pullback stability of the
    -- induced topology. Apply the singleton refinement
    -- `WeaklyEtale.exists_indEtale_comp` on the affine `dom(f).left` to obtain a
    -- single surjective qc cover refining `R.pullback f`; apply `h₂` to get
    -- `IsSheafFor F (singleton g)`; bridge to `R.pullback f` via
    -- `Presieve.isSheafFor_subsieve_aux`. The separatedness side condition for
    -- the bridge follows from applying `h₂` once more to the base-changed
    -- singleton along each arrow of `R.pullback f` (the pullback of a surjective
    -- qc affine étale morphism remains surjective qc affine étale).
    intro Y f hf
    -- Pullback stability: `R.pullback f ∈ topology S Y` since `R ∈ topology S X`.
    have hRpb : R.pullback f ∈ topology S Y :=
      (topology S).pullback_stable f hR
    -- Unfolding via `inducedTopology`: equivalently,
    -- `(R.pullback f).functorPushforward (toProEt S) ∈ ProEt.topology S ((toProEt S).obj Y)`.
    have hRpb_pf : (R.pullback f).functorPushforward (toProEt S) ∈
        ProEt.topology S ((toProEt S).obj Y) := hRpb
    -- SINGLE-SORRY PACKAGE: we extract, in one go, the singleton refinement plus
    -- the base-change identification needed for the separatedness side condition
    -- of `Presieve.isSheafFor_subsieve_aux`. The construction of `q` mirrors
    -- lines 250-298 (the affine wlog branch of `isCoverDense_toProEt`): pick a
    -- member of the ProEt cover, apply `RingHom.WeaklyEtale.exists_indEtale_comp`
    -- on the affine source `Y.left` to get a faithfully flat ind-étale extension,
    -- and package as a `proAffineEtale` arrow `q : Z ⟶ Y` in `S.AffineProEt`.
    -- Base-change stability of `Surjective`/`QuasiCompact`/`proAffineEtale` along
    -- arrows in `AffineProEt S` (which uses `HasPullbacks` from L148) yields the
    -- base-changed singleton `q' : Z' ⟶ W` and the sieve identification.
    --
    -- DEFERRED: full construction is ~80-150 LOC of careful manipulation.
    -- Packaged here as a single existential `singleton_refinement` so that the
    -- application of `Presieve.isSheafFor_subsieve_aux` is fully formalized.
    obtain ⟨Z, q, hqmem, hqsurj, basechange⟩ :=
      AffineProEt.exists_singleton_refinement (R.pullback f) hRpb_pf
    -- Apply `Presieve.isSheafFor_subsieve_aux` with the subsieve generated by `{q}`.
    -- (a) `(generate (singleton q) : Presieve Y) ≤ (R.pullback f : Presieve Y)`:
    -- any morphism factoring through `q` lies in `R.pullback f` by downward closure.
    have hSq_le : (Sieve.generate (Presieve.singleton q) : Presieve Y) ≤
        (R.pullback f : Presieve Y) := by
      rintro W g ⟨T, a, b, ⟨⟩, rfl⟩
      exact (R.pullback f).downward_closed hqmem a
    -- (b) `IsSheafFor F (generate (singleton q) : Presieve Y)`: from `h₂ q` +
    -- `isSheafFor_iff_generate`.
    have hSq_sheaf :
        Presieve.IsSheafFor F (Sieve.generate (Presieve.singleton q) : Presieve Y) := by
      haveI := hqsurj
      exact (Presieve.isSheafFor_iff_generate _).mp (h₂ q)
    -- (c) Separatedness side condition: use `basechange` to identify the pulled
    -- back sieve with `generate (singleton q')`, then apply `h₂ q'`.
    have htrans : ∀ ⦃W : AffineProEt S⦄ ⦃g : W ⟶ Y⦄, (R.pullback f).arrows g →
        Presieve.IsSeparatedFor F
          ((Sieve.generate (Presieve.singleton q)).pullback g : Presieve W) := by
      intro W g hg
      obtain ⟨Z', q', hq'surj, heq⟩ := basechange hg
      rw [heq]
      haveI := hq'surj
      exact ((Presieve.isSheafFor_iff_generate _).mp (h₂ q')).isSeparatedFor
    -- Finally, apply `isSheafFor_subsieve_aux`.
    exact Presieve.isSheafFor_subsieve_aux F hSq_le hSq_sheaf htrans

end AffineProEt

noncomputable def ProEt.baseChange {S T : Scheme.{u}} (f : S ⟶ T) :
    T.ProEt ⥤ S.ProEt :=
  MorphismProperty.Over.pullback _ _ f

noncomputable def AffineProEt.baseChange {S T : Scheme.{u}} (f : S ⟶ T) [IsAffineHom f] :
    T.AffineProEt ⥤ S.AffineProEt :=
  MorphismProperty.Over.pullback _ _ f

/-- The inclusion of the affine étale site into the affine pro-étale site. -/
noncomputable def AffineEtale.toAffineProEt (S : Scheme.{u}) :
    S.AffineEtale ⥤ S.AffineProEt :=
  MorphismProperty.CostructuredArrow.pre Scheme.Spec (𝟭 _) S
    (by
      intro X Y f ⟨hf, hf'⟩
      rw [ofObjectProperty_top_right_iff, Functor.comp_id, essImage_Spec] at hf'
      exact .of_isAffine f)
    (by simp)

/-- The topology on the affine pro-étale site is generated by limits
of `1`-hypercovers in the affine étale site. -/
instance :
    (GrothendieckTopology.oneHypercoverRelativelyRepresentable.{u}
      (AffineEtale.toAffineProEt S) (Type u)
      (AffineEtale.topology S) (AffineProEt.topology S)).IsGenerating := by
  -- Strategy: For each affine pro-étale `X` (`X = lim Xᵢ` with `Xᵢ` affine étale
  -- over `S`), a basis of `AffineProEt.topology` covers of `X` is obtained from
  -- `1`-hypercovers of the `Xᵢ` in `AffineEtale`, pulled back to `X`. This is
  -- precisely the content of `oneHypercoverRelativelyRepresentable` being a
  -- generating system for the induced topology.
  --
  -- Concrete decomposition:
  --   1. Use the cofiltered presentation `X.prop : proAffineEtale X.hom` —
  --      `X = lim_i X_i` with `X_i ∈ AffineEtale S`.
  --   2. Given any cover `R ∈ AffineProEt.topology X`, transfer via
  --      `(toProEt S).inducedTopology` to a `ProEt.topology`-cover, and reduce
  --      (using `WeaklyEtale.exists_indEtale_comp`) to a finite-stage `X_i`-cover
  --      coming from `AffineEtale.topology`.
  --   3. Take its `oneHypercover` lift in `AffineEtale` (via
  --      `Pretopology.toGrothendieck` of the small-étale pretopology).
  --   4. Pull back through `toAffineProEt` and along the transition `X → X_i`.
  -- Mathlib infrastructure needed: `GrothendieckTopology.IsGenerating.of_le`
  -- or similar (compare `oneHypercoverRelativelyRepresentable.IsGenerating`
  -- instances already present in Mathlib's `Sites/Hypercover/Zero.lean`).
  -- TODO: formalize via the universal property of `inducedTopology` and the
  -- fact that `AffineEtale ⥤ AffineProEt` is cofinal in the relevant slice
  -- category (each object of `AffineProEt` is a cofiltered limit of objects
  -- coming from `AffineEtale`).
  refine ⟨fun {X} T hT => ?_⟩
  -- Given `T ∈ AffineProEt.topology S X`, we must exhibit a `OneHypercover` `E`
  -- of `X` in `AffineProEt.topology` that satisfies the
  -- `oneHypercoverRelativelyRepresentable` predicate (i.e. has a
  -- `RelativeLimitPresentation` from `AffineEtale.toAffineProEt S` over some
  -- cofiltered `I`, with the appropriate sieve₀, sieve₁ membership conditions),
  -- and whose `sieve₀` refines `T`.
  --
  -- Unfold `hT` to a ProEt-cover (definitional via `IsDenseSubsite.functorPushforward_mem_iff`).
  have hT' : T.functorPushforward (AffineProEt.toProEt S) ∈
      ProEt.topology S ((AffineProEt.toProEt S).obj X) := hT
  -- (a) Extract the cofiltered presentation `X.left = lim_{j : J} D.obj j` of `X.prop`.
  --     Each `D.obj j` is in `(Etale ⊓ IsAffine over S)`, so projects to an `AffineEtale S`.
  obtain ⟨J, instJ, instCofJ, D, t, s, hLim, hData⟩ := X.prop
  -- For convenience, abbreviate `IsAffine` of each stage.
  haveI hAff : ∀ j, IsAffine (D.obj j) := fun j => by
    have := (hData j).1.2
    rwa [ofObjectProperty_top_right_iff] at this
  haveI hEt : ∀ j, Etale (t.app j) := fun j => (hData j).1.1
  -- Promote each `(D.obj j, t.app j)` to an `AffineEtale S` object by composing
  -- with the canonical iso `D.obj j ≅ Spec Γ(D.obj j)` (since `D.obj j` is affine).
  --
  -- Strategy decomposed into named sub-witnesses.
  -- (a) Cofiltered presentation `X.left = lim Xᵢ` (now extracted above).
  -- (b)–(c) Factor each `R`-morphism through a finite-stage `Xᵢ` via
  --     `WeaklyEtale.exists_indEtale_comp`, building an étale cover of `Xᵢ`.
  -- (d) Build `RelativeLimitPresentation` data (`pres`, `pres₀`, `pres₁`).
  -- (e) Verify `sieve₀`, `sieve₁` membership in `AffineEtale.topology Xᵢ`.
  -- (f) The resulting `OneHypercover.sieve₀` refines `T` by construction.
  --
  -- DEEP GAP: steps (b)–(f) require non-trivial cofiltered descent infrastructure
  -- that is not yet in Mathlib (notably: a scheme-level analogue of
  -- `WeaklyEtale.exists_indEtale_comp` for arrows landing in `lim Dⱼ`, plus a
  -- lift `AffineEtale-OneHypercover-at-Xᵢ → AffineProEt-OneHypercover-at-X` that
  -- preserves the `RelativeLimitPresentation` structure). Session 28 review
  -- estimated 160–240 LOC; realistic estimate including required helpers is
  -- closer to 500–800 LOC.
  refine ⟨?E, ?hE_predicate, ?hE_refines⟩
  case E =>
    -- The OneHypercover of X in AffineProEt.topology S, constructed via pullback
    -- of a stage-`i` AffineEtale OneHypercover along `X → Xᵢ`. Requires the
    -- spreading lemma to choose `i`; depends on (b)–(c) above.
    exact sorry
  case hE_predicate =>
    -- The oneHypercoverRelativelyRepresentable witness — to be built from
    -- the extracted cofiltered presentation `(J, D, t, s, hLim)`. Requires the
    -- `OneHypercover.RelativeLimitPresentation` constructed in (d) above.
    -- The `I = J` (the indexing category extracted from `X.prop`).
    -- The `PreservesLimitsOfShape` follows from
    -- `Limits.preservesFiniteLimits_of_filteredColimits_in_Type` once the
    -- multicospan-shape is finite (it is, for any `OneHypercover`).
    exact sorry
  case hE_refines =>
    -- The sieve generated by E.f refines T: each E.f a factors through a member of T
    -- by construction (the étale cover of `Xᵢ` was extracted from `T`'s pushforward).
    exact sorry

end AlgebraicGeometry.Scheme
