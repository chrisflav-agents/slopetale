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
  rw [isSheaf_iff_isSheaf_of_type] at h₁ ⊢
  intro X R hR
  -- Unfold `hR` to the form `R.functorPushforward (toProEt S) ∈ ProEt.topology S _`.
  -- This is definitional because `topology S := (toProEt S).inducedTopology _`
  -- and `Functor.mem_inducedTopology_sieves_iff` is `Iff.rfl`. The
  -- `IsDenseSubsite` instance at L417 records this with `by rfl`.
  sorry

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
  refine ⟨fun {X} S hS => ?_⟩
  -- Given `S ∈ AffineProEt.topology S X`, we must exhibit a `OneHypercover`
  -- `E` of `X` (in `AffineProEt.topology`) that is a relative-limit
  -- presentation of `1`-hypercovers in `AffineEtale.topology`, and whose
  -- `sieve₀` refines `S`. The full construction goes through
  -- `WeaklyEtale.exists_indEtale_comp` and the cofiltered presentation
  -- `X.prop : proAffineEtale X.hom`.
  sorry

end AlgebraicGeometry.Scheme
