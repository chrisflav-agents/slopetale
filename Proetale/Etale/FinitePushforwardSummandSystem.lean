/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.FinitePushforwardStalkCofinal

/-!
# The system of split summands over the étale neighbourhood stages

This file continues stage C of the program towards the stalk formula for pushforwards
along finite morphisms (blueprint `lemma:pbc-finite`), building on
`Proetale.Etale.FinitePushforwardStalkIso` and
`Proetale.Etale.FinitePushforwardStalkCofinal`.

Let `f : Y ⟶ X` be a morphism of schemes, `x : Spec Ω ⟶ X` a geometric point,
`p₁` an étale neighbourhood stage of `x` carrying a family of idempotent sections
`es : ι → Γ(U₁ ×_X Y)` of the fiber (the *splitting stage*), `i : ι` a distinguished
index, and `y : Spec Ω' ⟶ Y` a geometric point of `Y` over `x` together with a
character `χ` of the fiber sections compatible with evaluation at `y` and not killing
the distinguished idempotent.

## The summand system

- `AlgebraicGeometry.Scheme.Etale.SummandIndex`: the cofiltered category of affine
  étale neighbourhood stages refining the splitting stage `p₁`, with the initial
  projection `AlgebraicGeometry.Scheme.Etale.stageFunctor` to the étale neighbourhoods
  of `x`.
- `AlgebraicGeometry.Scheme.Etale.summand`: the split summand over a stage `g`, i.e.
  the basic open of the restriction `AlgebraicGeometry.Scheme.Etale.esAt` of the
  distinguished idempotent to the fiber over `g`, as an object of the small étale site
  of `Y`.
- `AlgebraicGeometry.Scheme.Etale.summandPoint` /
  `AlgebraicGeometry.Scheme.Etale.summandFunctor`: the lifted geometric point of each
  summand and the resulting functor from the summand indices to the étale
  neighbourhoods of `y`, with transition maps
  `AlgebraicGeometry.Scheme.Etale.summandMap`.

## The summand sections colimit and its identification

- `AlgebraicGeometry.Scheme.Etale.summandSections`: the colimit of the section rings
  `Γ(summand g)` over the summand system, together with the germ comparison
  `AlgebraicGeometry.Scheme.Etale.summandSectionsToStrictLocalization` to the strict
  localization of `Y` at `y` and the restriction map
  `AlgebraicGeometry.Scheme.Etale.fiberSectionsToSummandSections` from the fiber
  sections, compatible with the comparison map of
  `Proetale.Etale.FinitePushforwardStalkCofinal`
  (`fiberSectionsToSummandSections_summandSectionsToStrictLocalization`).
- `AlgebraicGeometry.Scheme.Etale.surjective_fiberSectionsToSummandSections` and
  `AlgebraicGeometry.Scheme.Etale.isLocalization_awaySelf_summandSections`: for finite
  `f` and a complete orthogonal family of idempotents, the summand sections are the
  localization of the fiber sections away from the distinguished idempotent
  `e = (toFiberSections f x p₁) (es i)`; in particular the restriction map is
  surjective. Stage-wise this is the localization of an affine scheme at a basic open
  of an idempotent.
- `AlgebraicGeometry.Scheme.Etale.eval_toSummandSections` and
  `AlgebraicGeometry.Scheme.Etale.exists_isUnit_map_of_isUnit`: evaluation of germs of
  summand sections at the lifted point, and descent of invertibility in the colimit to
  a finite stage. These feed the cofinality argument identifying the localization of
  the fiber sections at the maximal ideal of `χ` with the strict localization of `Y`
  at `y` downstream.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

/-!
### Localizations away from an idempotent

For an idempotent `e` of a commutative ring `R`, the localization `R[e⁻¹]` is very
simple: the image of `e` is `1`, the localization map is surjective and its kernel is
the annihilator of `e`. These are the model facts for the stage-wise comparison of the
summand sections with the fiber sections.
-/

section AwayIdempotent

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

private lemma algebraMap_away_eq_one {e : R} (he : IsIdempotentElem e)
    [IsLocalization.Away e S] : algebraMap R S e = 1 := by
  have hu : IsUnit (algebraMap R S e) :=
    IsLocalization.map_units S (⟨e, Submonoid.mem_powers e⟩ : Submonoid.powers e)
  have h2 : algebraMap R S e * algebraMap R S e = algebraMap R S e * 1 := by
    rw [← map_mul, he.eq, mul_one]
  exact hu.mul_left_cancel h2

private lemma surjective_algebraMap_away {e : R} (he : IsIdempotentElem e)
    [IsLocalization.Away e S] : Function.Surjective (algebraMap R S) := by
  intro z
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers e) z
  refine ⟨a, ?_⟩
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  have hs : algebraMap R S (s : R) = 1 := by
    rw [← hn, map_pow, algebraMap_away_eq_one he, one_pow]
  rw [← IsLocalization.mk'_spec S a s, hs, mul_one]

private lemma algebraMap_away_eq_zero_iff {e : R} (he : IsIdempotentElem e)
    [IsLocalization.Away e S] (z : R) :
    algebraMap R S z = 0 ↔ e * z = 0 := by
  constructor
  · intro h
    obtain ⟨m, hmz⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers e) S z).mp h
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp m.2
    have hcz : e ^ n * z = 0 := by
      rw [hn]
      exact hmz
    cases n with
    | zero =>
      rw [pow_zero, one_mul] at hcz
      rw [hcz, mul_zero]
    | succ m =>
      rwa [he.pow_succ_eq] at hcz
  · intro h
    have h2 := congrArg (algebraMap R S) h
    rwa [map_mul, map_zero, algebraMap_away_eq_one he, one_mul] at h2

end AwayIdempotent

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X) (p₁ : (geometricPoint x).fiber.Elements)

/-!
### The index category of stages refining the splitting stage

The summand system is indexed by the affine étale neighbourhood stages of `x` refining
the splitting stage `p₁`. This category is cofiltered and its projection to the étale
neighbourhoods of `x` is initial, because the affine étale neighbourhoods are initial
among all étale neighbourhoods.
-/

/-- The index category of the summand system: affine étale neighbourhood stages of `x`
together with a refinement map to the splitting stage `p₁`. -/
noncomputable abbrev SummandIndex : Type (u + 1) :=
  CostructuredArrow
    (CategoryOfElements.pre (AffineEtale.Spec X) (geometricPoint x).fiber) p₁

instance : IsCofiltered (SummandIndex x p₁) :=
  (Functor.initial_iff_isCofiltered_costructuredArrow
    (CategoryOfElements.pre (AffineEtale.Spec X) (geometricPoint x).fiber)).mp
    inferInstance p₁

/-- The projection from the summand indices to the étale neighbourhood stages of `x`,
forgetting the refinement map to the splitting stage. It is initial. -/
noncomputable def stageFunctor : SummandIndex x p₁ ⥤ (geometricPoint x).fiber.Elements :=
  CostructuredArrow.proj
      (CategoryOfElements.pre (AffineEtale.Spec X) (geometricPoint x).fiber) p₁ ⋙
    CategoryOfElements.pre (AffineEtale.Spec X) (geometricPoint x).fiber

instance : (stageFunctor x p₁).Initial :=
  Functor.initial_comp _ _

instance : FinallySmall.{u} (SummandIndex x p₁)ᵒᵖ :=
  finallySmall_of_essentiallySmall _

instance : HasColimitsOfShape (SummandIndex x p₁)ᵒᵖ CommRingCat.{u} :=
  hasColimitsOfShape_of_finallySmall _ _

instance : PreservesColimitsOfShape (SummandIndex x p₁)ᵒᵖ
    (CategoryTheory.forget CommRingCat.{u}) :=
  FinallySmall.preservesColimitsOfShape_of_isFiltered _ _

/-- The étale neighbourhood stage of `x` underlying a summand index. -/
noncomputable abbrev stage (g : SummandIndex x p₁) : (geometricPoint x).fiber.Elements :=
  (stageFunctor x p₁).obj g

/-- The refinement map from a summand-index stage to the splitting stage. -/
noncomputable abbrev stageHom (g : SummandIndex x p₁) : stage x p₁ g ⟶ p₁ :=
  g.hom

instance isAffine_stage (g : SummandIndex x p₁) : IsAffine (stage x p₁ g).1.left :=
  inferInstanceAs (IsAffine (Spec (unop g.left.1.left)))

/-!
### The restricted idempotents and the split summands
-/

variable {ι : Type u} (es : ι → Γ(((Over.pullback @Etale ⊤ f).obj p₁.1).left, ⊤)) (i : ι)

/-- The restriction of the idempotent sections of the splitting stage to the fiber over
a summand-index stage. -/
noncomputable def esAt (g : SummandIndex x p₁) (j : ι) :
    Γ(((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left, ⊤) :=
  ((fiberSectionsDiagram f x).map (op (stageHom x p₁ g))).hom (es j)

/-- The restricted idempotents have the same image in the fiber sections as the
original family. -/
lemma toFiberSections_esAt (g : SummandIndex x p₁) (j : ι) :
    (toFiberSections f x (stage x p₁ g)).hom (esAt f x p₁ es g j) =
      (toFiberSections f x p₁).hom (es j) :=
  toFiberSections_w_apply f x (stageHom x p₁ g) (es j)

/-- The restricted idempotents are compatible with the transition maps of the summand
indices, as sections of the fiber sections diagram. -/
lemma esAt_map {g g' : SummandIndex x p₁} (t : g' ⟶ g) (j : ι) :
    ((fiberSectionsDiagram f x).map (op ((stageFunctor x p₁).map t))).hom
        (esAt f x p₁ es g j) = esAt f x p₁ es g' j := by
  have hw : (stageFunctor x p₁).map t ≫ stageHom x p₁ g = stageHom x p₁ g' :=
    CostructuredArrow.w t
  have h1 : (fiberSectionsDiagram f x).map (op (stageHom x p₁ g)) ≫
      (fiberSectionsDiagram f x).map (op ((stageFunctor x p₁).map t)) =
      (fiberSectionsDiagram f x).map (op (stageHom x p₁ g')) := by
    rw [← Functor.map_comp]
    exact congrArg (fiberSectionsDiagram f x).map (congrArg Quiver.Hom.op hw)
  have h2 := congrArg (fun φ => CommRingCat.Hom.hom φ (es j)) h1
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h2

/-- Variant of `AlgebraicGeometry.Scheme.Etale.esAt_map` for the transition maps of the
fibers, spelled with `appTop`. -/
lemma appTop_esAt {g g' : SummandIndex x p₁} (t : g' ⟶ g) (j : ι) :
    ((((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map t).val).left).appTop).hom
        (esAt f x p₁ es g j) = esAt f x p₁ es g' j := by
  have hmap : (fiberSectionsDiagram f x).map (op ((stageFunctor x p₁).map t)) =
      (((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map t).val).left).appTop :=
    Scheme.Γ_map_op _
  rw [← hmap]
  exact esAt_map f x p₁ es t j

/-- The split summand over a summand-index stage: the basic open of the restriction of
the distinguished idempotent to the fiber, as an object of the small étale site of
`Y`. -/
noncomputable def summand (g : SummandIndex x p₁) : Y.Etale :=
  basicOpenSummand ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1) (esAt f x p₁ es g) i

lemma summand_hom (g : SummandIndex x p₁) :
    (summand f x p₁ es i g).hom =
      ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
          (esAt f x p₁ es g i)).ι ≫
        ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).hom :=
  rfl

/-- The split summands are affine for finite `f`: they are basic opens of the affine
fibers over the affine stages. -/
instance [IsFinite f] (g : SummandIndex x p₁) : IsAffine (summand f x p₁ es i g).left := by
  haveI : IsAffine ((𝟭 Scheme.{u}).obj (stage x p₁ g).1.left) := isAffine_stage x p₁ g
  haveI : IsAffine (((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left) :=
    inferInstanceAs (IsAffine (pullback (stage x p₁ g).1.hom f))
  exact inferInstanceAs (IsAffine
    ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
      (esAt f x p₁ es g i)))

/-- The transition map of the fibers over a refinement of stages maps the basic open of
the restricted idempotent into the basic open at the coarser stage. -/
private lemma basicOpen_esAt_le {g g' : SummandIndex x p₁} (t : g' ⟶ g) :
    (((Over.pullback @Etale ⊤ f).obj (stage x p₁ g').1).left).basicOpen
        (esAt f x p₁ es g' i) ≤
      (((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map t).val).left) ⁻¹ᵁ
        ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
          (esAt f x p₁ es g i)) := by
  rw [Scheme.Hom.preimage_basicOpen_top, appTop_esAt f x p₁ es t i]

/-- The transition map of the summand system over a refinement of stages: the
restriction of the transition map of the fibers to the basic open summands. -/
noncomputable def summandMap {g g' : SummandIndex x p₁} (t : g' ⟶ g) :
    summand f x p₁ es i g' ⟶ summand f x p₁ es i g :=
  MorphismProperty.Over.homMk
    ((((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map t).val).left).resLE
      ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
        (esAt f x p₁ es g i))
      ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g').1).left).basicOpen
        (esAt f x p₁ es g' i))
      (basicOpen_esAt_le f x p₁ es i t))
    (by
      rw [summand_hom, summand_hom, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
        Category.assoc,
        MorphismProperty.Over.w ((Over.pullback @Etale ⊤ f).map
          ((stageFunctor x p₁).map t).val)])
    trivial

/-- The transition maps of the summand system commute with the open immersions into
the fibers. -/
@[reassoc]
lemma summandMap_left_ι {g g' : SummandIndex x p₁} (t : g' ⟶ g) :
    (summandMap f x p₁ es i t).left ≫
        ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
          (esAt f x p₁ es g i)).ι =
      ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g').1).left).basicOpen
          (esAt f x p₁ es g' i)).ι ≫
        (((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map t).val).left) :=
  Scheme.Hom.resLE_comp_ι _ _

private lemma summandMap_id (g : SummandIndex x p₁) :
    summandMap f x p₁ es i (𝟙 g) = 𝟙 (summand f x p₁ es i g) := by
  apply MorphismProperty.Over.Hom.ext
  rw [← cancel_mono ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
    (esAt f x p₁ es g i)).ι, summandMap_left_ι]
  have h1 : (((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map (𝟙 g)).val).left) =
      𝟙 (((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left) := by
    rw [CategoryTheory.Functor.map_id]
    change (((Over.pullback @Etale ⊤ f).map (𝟙 (stage x p₁ g).1)).left) = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  rw [h1, Category.comp_id]
  have h2 : (𝟙 (summand f x p₁ es i g) :
      summand f x p₁ es i g ⟶ summand f x p₁ es i g).left =
      𝟙 ((summand f x p₁ es i g).left) := rfl
  rw [h2, Category.id_comp]

private lemma summandMap_comp {g g' g'' : SummandIndex x p₁} (u : g'' ⟶ g') (t : g' ⟶ g) :
    summandMap f x p₁ es i (u ≫ t) =
      summandMap f x p₁ es i u ≫ summandMap f x p₁ es i t := by
  apply MorphismProperty.Over.Hom.ext
  rw [← cancel_mono ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
    (esAt f x p₁ es g i)).ι, summandMap_left_ι]
  have h1 : (((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map (u ≫ t)).val).left) =
      (((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map u).val).left) ≫
        (((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map t).val).left) := by
    rw [CategoryTheory.Functor.map_comp]
    change (((Over.pullback @Etale ⊤ f).map
      (((stageFunctor x p₁).map u).val ≫ ((stageFunctor x p₁).map t).val)).left) = _
    rw [CategoryTheory.Functor.map_comp]
    rfl
  have h2 : (summandMap f x p₁ es i u ≫ summandMap f x p₁ es i t).left =
      (summandMap f x p₁ es i u).left ≫ (summandMap f x p₁ es i t).left := rfl
  rw [h1, h2, Category.assoc, summandMap_left_ι, summandMap_left_ι_assoc]

/-!
### The lifted geometric points of the summands

The lift of the geometric point `y` to the fiber over a summand-index stage lands in
the basic open of the restricted idempotent, because the character `χ` does not vanish
on the distinguished idempotent. This equips each summand with a lifted point,
compatibly with the transition maps.
-/

variable {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
  (σ : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))
  (y : Spec (CommRingCat.of Ω') ⟶ Y) (hy : y ≫ f = σ ≫ x)
  (χ : fiberSections f x →+* Ω')
  (heval : fiberSectionsToStrictLocalization f x σ y hy ≫ strictLocalizationEval y =
    CommRingCat.ofHom χ)
  (hi : χ ((toFiberSections f x p₁).hom (es i)) ≠ 0)

include χ heval hi in
private lemma mem_basicOpen_esAt (g : SummandIndex x p₁) :
    (pullbackFiberLift f x σ y hy (stage x p₁ g).1 (stage x p₁ g).2).val.base default ∈
      (((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
        (esAt f x p₁ es g i) := by
  refine pullbackFiberLift_mem_basicOpen f x σ y hy χ heval (stage x p₁ g)
    (esAt f x p₁ es g i) ?_
  rw [toFiberSections_esAt f x p₁ es g i]
  exact hi

include χ heval hi in
private lemma range_subset_basicOpen_esAt (g : SummandIndex x p₁) :
    Set.range (pullbackFiberLift f x σ y hy (stage x p₁ g).1 (stage x p₁ g).2).val.base ⊆
      Set.range ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
        (esAt f x p₁ es g i)).ι.base := by
  rw [Scheme.Opens.range_ι]
  rintro - ⟨t, rfl⟩
  rw [Unique.eq_default t]
  exact mem_basicOpen_esAt f x p₁ es i σ y hy χ heval hi g

/-- **The lifted geometric point of a summand**: the lift of `y` to the fiber over a
summand-index stage factors through the basic open summand, giving an étale
neighbourhood structure on the summand. -/
noncomputable def summandPoint (g : SummandIndex x p₁) :
    (geometricPoint y).fiber.obj (summand f x p₁ es i g) :=
  geometricPoint.mkFiber y
    (IsOpenImmersion.lift
      ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
        (esAt f x p₁ es g i)).ι
      (pullbackFiberLift f x σ y hy (stage x p₁ g).1 (stage x p₁ g).2).val
      (range_subset_basicOpen_esAt f x p₁ es i σ y hy χ heval hi g))
    (by
      rw [summand_hom, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact (pullbackFiberLift f x σ y hy (stage x p₁ g).1 (stage x p₁ g).2).property)

/-- The lifted point of the summand recovers the lift of `y` to the fiber, after
composing with the open immersion into the fiber. -/
@[reassoc]
lemma summandPoint_val_ι (g : SummandIndex x p₁) :
    (summandPoint f x p₁ es i σ y hy χ heval hi g).val ≫
        ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
          (esAt f x p₁ es g i)).ι =
      (pullbackFiberLift f x σ y hy (stage x p₁ g).1 (stage x p₁ g).2).val :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The summand injection maps the lifted point of the summand to the lift of `y` to
the fiber**: the summand with its lifted point is an étale neighbourhood of `y`
refining the base-changed neighbourhood. -/
lemma summandPoint_inj (g : SummandIndex x p₁) :
    (geometricPoint y).fiber.map
        ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
          (esAt f x p₁ es g)).inj i)
        (summandPoint f x p₁ es i σ y hy χ heval hi g) =
      pullbackFiberLift f x σ y hy (stage x p₁ g).1 (stage x p₁ g).2 := by
  refine Subtype.ext ?_
  change (summandPoint f x p₁ es i σ y hy χ heval hi g).val ≫
    ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
      (esAt f x p₁ es g i)).ι = _
  exact summandPoint_val_ι f x p₁ es i σ y hy χ heval hi g

/-- The lifted points of the summands are compatible with the transition maps of the
summand system. -/
lemma fiber_map_summandMap {g g' : SummandIndex x p₁} (t : g' ⟶ g) :
    (geometricPoint y).fiber.map (summandMap f x p₁ es i t)
        (summandPoint f x p₁ es i σ y hy χ heval hi g') =
      summandPoint f x p₁ es i σ y hy χ heval hi g := by
  have h1 : (pullbackFiberLift f x σ y hy (stage x p₁ g').1 (stage x p₁ g').2).val ≫
      (((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map t).val).left) =
      (pullbackFiberLift f x σ y hy (stage x p₁ g).1 (stage x p₁ g).2).val :=
    congrArg Subtype.val
      ((pullbackElements f x σ y hy).map ((stageFunctor x p₁).map t)).property
  refine Subtype.ext ?_
  rw [← cancel_mono ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
    (esAt f x p₁ es g i)).ι]
  change ((summandPoint f x p₁ es i σ y hy χ heval hi g').val ≫
    (summandMap f x p₁ es i t).left) ≫ _ = _
  rw [Category.assoc, summandMap_left_ι, ← Category.assoc,
    summandPoint_val_ι f x p₁ es i σ y hy χ heval hi g',
    summandPoint_val_ι f x p₁ es i σ y hy χ heval hi g]
  exact h1

/-- **The summand system**: the functor from the summand indices to the étale
neighbourhoods of `y` sending a stage to its split summand with the lifted geometric
point. -/
noncomputable def summandFunctor :
    SummandIndex x p₁ ⥤ (geometricPoint y).fiber.Elements where
  obj g := ⟨summand f x p₁ es i g, summandPoint f x p₁ es i σ y hy χ heval hi g⟩
  map t := ⟨summandMap f x p₁ es i t,
    fiber_map_summandMap f x p₁ es i σ y hy χ heval hi t⟩
  map_id g := CategoryOfElements.ext _ _ _ (summandMap_id f x p₁ es i g)
  map_comp u t := CategoryOfElements.ext _ _ _ (summandMap_comp f x p₁ es i u t)

@[simp]
lemma summandFunctor_obj_fst (g : SummandIndex x p₁) :
    ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g).1 = summand f x p₁ es i g :=
  rfl

@[simp]
lemma summandFunctor_obj_snd (g : SummandIndex x p₁) :
    ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g).2 =
      summandPoint f x p₁ es i σ y hy χ heval hi g :=
  rfl

/-!
### The summand sections colimit
-/

/-- The diagram of the section rings of the split summands, i.e. the restriction of the
strict localization diagram of `y` along the summand system. Its colimit compares to
the strict localization of `Y` at `y` via `colimit.pre`. -/
noncomputable def summandSectionsDiagram : (SummandIndex x p₁)ᵒᵖ ⥤ CommRingCat.{u} :=
  (summandFunctor f x p₁ es i σ y hy χ heval hi).op ⋙ strictLocalizationDiagram y

lemma summandSectionsDiagram_obj (g : SummandIndex x p₁) :
    (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).obj (op g) =
      Γ((summand f x p₁ es i g).left, ⊤) :=
  rfl

/-- The colimit of the section rings of the split summands over the summand system. -/
noncomputable def summandSections : CommRingCat.{u} :=
  colimit (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi)

/-- The canonical map from the sections of a summand to the summand sections
colimit. -/
noncomputable def toSummandSections (g : SummandIndex x p₁) :
    Γ((summand f x p₁ es i g).left, ⊤) ⟶
      summandSections f x p₁ es i σ y hy χ heval hi :=
  colimit.ι (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi) (op g)

@[reassoc, elementwise]
lemma toSummandSections_w {g g' : SummandIndex x p₁} (t : g' ⟶ g) :
    (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map (op t) ≫
        toSummandSections f x p₁ es i σ y hy χ heval hi g' =
      toSummandSections f x p₁ es i σ y hy χ heval hi g :=
  colimit.w (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi) (op t)

/-- Every element of the summand sections comes from some stage. -/
lemma exists_toSummandSections_eq (w : summandSections f x p₁ es i σ y hy χ heval hi) :
    ∃ (g : SummandIndex x p₁) (b : Γ((summand f x p₁ es i g).left, ⊤)),
      (toSummandSections f x p₁ es i σ y hy χ heval hi g).hom b = w := by
  obtain ⟨⟨g⟩, b, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget CommRingCat)
      (colimit.isColimit (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi))) w
  exact ⟨g, b, rfl⟩

/-!
### The restriction map from the fiber sections

Restricting the sections of a fiber to its split summand is compatible with the
transition maps, so it induces a homomorphism from the fiber sections to the summand
sections, using that the summand indices are initial among all étale neighbourhood
stages of `x`.
-/

private lemma restrictToSummand_naturality {g g' : SummandIndex x p₁} (t : g' ⟶ g) :
    Scheme.Γ.map
        (((Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map t).val).left).op ≫
      Scheme.Γ.map ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g').1).left).basicOpen
        (esAt f x p₁ es g' i)).ι.op =
    Scheme.Γ.map ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
        (esAt f x p₁ es g i)).ι.op ≫
      Scheme.Γ.map ((summandMap f x p₁ es i t).left).op := by
  simp only [← Functor.map_comp, ← op_comp]
  rw [summandMap_left_ι]

/-- The stage-wise restriction to the split summands, as a morphism of diagrams from
the restricted fiber sections diagram to the summand sections diagram. -/
noncomputable def restrictToSummand :
    (stageFunctor x p₁).op ⋙ fiberSectionsDiagram f x ⟶
      summandSectionsDiagram f x p₁ es i σ y hy χ heval hi where
  app g := Scheme.Γ.map
    ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g.unop).1).left).basicOpen
      (esAt f x p₁ es g.unop i)).ι.op
  naturality _ _ t := restrictToSummand_naturality f x p₁ es i t.unop

/-- **The restriction map from the fiber sections to the summand sections**: the
composite of the colimit-restriction isomorphism along the initial functor
`stageFunctor` with the stage-wise restriction to the summands. -/
noncomputable def fiberSectionsToSummandSections :
    fiberSections f x ⟶ summandSections f x p₁ es i σ y hy χ heval hi :=
  inv (colimit.pre (fiberSectionsDiagram f x) (stageFunctor x p₁).op) ≫
    colimMap (restrictToSummand f x p₁ es i σ y hy χ heval hi)

/-- The stage-wise description of the restriction map from the fiber sections to the
summand sections. -/
@[reassoc]
lemma toFiberSections_fiberSectionsToSummandSections (g : SummandIndex x p₁) :
    toFiberSections f x (stage x p₁ g) ≫
        fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi =
      Scheme.Γ.map ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
          (esAt f x p₁ es g i)).ι.op ≫
        toSummandSections f x p₁ es i σ y hy χ heval hi g := by
  have h1 : colimit.ι ((stageFunctor x p₁).op ⋙ fiberSectionsDiagram f x) (op g) ≫
      colimit.pre (fiberSectionsDiagram f x) (stageFunctor x p₁).op =
      toFiberSections f x (stage x p₁ g) :=
    colimit.ι_pre (fiberSectionsDiagram f x) (stageFunctor x p₁).op (op g)
  rw [fiberSectionsToSummandSections, ← h1, Category.assoc, IsIso.hom_inv_id_assoc,
    ι_colimMap]
  rfl

/-!
### The germ comparison with the strict localization at `y`
-/

/-- **The germ comparison of the summand sections**: the canonical map from the summand
sections to the strict localization of `Y` at `y`, given by the colimit restriction
along the summand system. -/
noncomputable def summandSectionsToStrictLocalization :
    summandSections f x p₁ es i σ y hy χ heval hi ⟶ strictLocalization y :=
  colimit.pre (strictLocalizationDiagram y)
    (summandFunctor f x p₁ es i σ y hy χ heval hi).op

/-- The germ comparison restricted to a stage is the germ map of the summand with its
lifted point. -/
@[reassoc]
lemma toSummandSections_summandSectionsToStrictLocalization (g : SummandIndex x p₁) :
    toSummandSections f x p₁ es i σ y hy χ heval hi g ≫
        summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi =
      toStrictLocalization y
        ⟨summand f x p₁ es i g, summandPoint f x p₁ es i σ y hy χ heval hi g⟩ :=
  colimit.ι_pre (strictLocalizationDiagram y)
    (summandFunctor f x p₁ es i σ y hy χ heval hi).op (op g)

/-- **Compatibility of the restriction and germ maps**: the composite of the
restriction from the fiber sections to the summand sections with the germ comparison
is the comparison map from the fiber sections to the strict localization of `Y` at
`y`. -/
theorem fiberSectionsToSummandSections_summandSectionsToStrictLocalization :
    fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi ≫
        summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi =
      fiberSectionsToStrictLocalization f x σ y hy := by
  refine colimit.hom_ext fun P => ?_
  obtain ⟨p⟩ := P
  obtain ⟨w⟩ : Nonempty (CostructuredArrow (stageFunctor x p₁) p) := by
    haveI := Functor.Initial.out (F := stageFunctor x p₁) p
    infer_instance
  have hkey : toFiberSections f x (stage x p₁ w.left) ≫
      fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi ≫
        summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi =
      toFiberSections f x (stage x p₁ w.left) ≫
        fiberSectionsToStrictLocalization f x σ y hy := by
    rw [← Category.assoc, toFiberSections_fiberSectionsToSummandSections,
      Category.assoc, toSummandSections_summandSectionsToStrictLocalization,
      toFiberSections_fiberSectionsToStrictLocalization]
    exact toStrictLocalization_w y
      (p := ⟨summand f x p₁ es i w.left,
        summandPoint f x p₁ es i σ y hy χ heval hi w.left⟩)
      (q := (pullbackElements f x σ y hy).obj (stage x p₁ w.left))
      ⟨(cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ w.left).1)
          (esAt f x p₁ es w.left)).inj i,
        summandPoint_inj f x p₁ es i σ y hy χ heval hi w.left⟩
  have e₁ : stage x p₁ w.left ⟶ p := w.hom
  change toFiberSections f x p ≫ _ = toFiberSections f x p ≫ _
  rw [← toFiberSections_w f x e₁]
  simp only [Category.assoc]
  rw [hkey]

/-!
### The summand sections as a localization of the fiber sections

For finite `f` and a complete orthogonal family of idempotents `es`, the summand
sections are the localization of the fiber sections away from the distinguished
idempotent `e = (toFiberSections f x p₁) (es i)`. Stage-wise, the sections of the
summand are the localization of the affine fiber sections away from the restricted
idempotent, where the localization map is surjective with kernel the annihilator of
the idempotent.
-/

noncomputable instance : Algebra (fiberSections f x)
    (summandSections f x p₁ es i σ y hy χ heval hi) :=
  (fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi).hom.toAlgebra

lemma algebraMap_summandSections_eq :
    algebraMap (fiberSections f x) (summandSections f x p₁ es i σ y hy χ heval hi) =
      (fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi).hom :=
  rfl

section IsFinite

variable [IsFinite f]

private lemma isLocalization_away_esAt (g : SummandIndex x p₁) :
    IsLocalization.Away (esAt f x p₁ es g i)
      Γ(((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
        (esAt f x p₁ es g i)), ⊤) := by
  haveI : IsAffine ((𝟭 Scheme.{u}).obj (stage x p₁ g).1.left) := isAffine_stage x p₁ g
  haveI : IsAffine (((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left) :=
    inferInstanceAs (IsAffine (pullback (stage x p₁ g).1.hom f))
  infer_instance

omit [IsFinite f] in
private lemma isIdempotentElem_esAt (hidem : IsIdempotentElem (es i))
    (g : SummandIndex x p₁) : IsIdempotentElem (esAt f x p₁ es g i) :=
  hidem.map ((fiberSectionsDiagram f x).map (op (stageHom x p₁ g))).hom

private lemma Γ_map_ι_esAt_eq_one (hidem : IsIdempotentElem (es i))
    (g : SummandIndex x p₁) :
    (Scheme.Γ.map ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
        (esAt f x p₁ es g i)).ι.op).hom (esAt f x p₁ es g i) = 1 := by
  haveI : IsAffine ((𝟭 Scheme.{u}).obj (stage x p₁ g).1.left) := isAffine_stage x p₁ g
  haveI : IsAffine (((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left) :=
    inferInstanceAs (IsAffine (pullback (stage x p₁ g).1.hom f))
  haveI := isLocalization_away_esAt f x p₁ es i g
  exact algebraMap_away_eq_one
    (S := Γ(((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
      (esAt f x p₁ es g i)), ⊤))
    (isIdempotentElem_esAt f x p₁ es i hidem g)

private lemma surjective_Γ_map_ι_esAt (hidem : IsIdempotentElem (es i))
    (g : SummandIndex x p₁) :
    Function.Surjective (Scheme.Γ.map ((((Over.pullback @Etale ⊤ f).obj
      (stage x p₁ g).1).left).basicOpen (esAt f x p₁ es g i)).ι.op).hom := by
  haveI : IsAffine ((𝟭 Scheme.{u}).obj (stage x p₁ g).1.left) := isAffine_stage x p₁ g
  haveI : IsAffine (((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left) :=
    inferInstanceAs (IsAffine (pullback (stage x p₁ g).1.hom f))
  haveI := isLocalization_away_esAt f x p₁ es i g
  exact surjective_algebraMap_away
    (S := Γ(((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
      (esAt f x p₁ es g i)), ⊤))
    (isIdempotentElem_esAt f x p₁ es i hidem g)

private lemma Γ_map_ι_esAt_eq_zero_iff (hidem : IsIdempotentElem (es i))
    (g : SummandIndex x p₁)
    (a : Γ(((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left, ⊤)) :
    (Scheme.Γ.map ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
        (esAt f x p₁ es g i)).ι.op).hom a = 0 ↔ esAt f x p₁ es g i * a = 0 := by
  haveI : IsAffine ((𝟭 Scheme.{u}).obj (stage x p₁ g).1.left) := isAffine_stage x p₁ g
  haveI : IsAffine (((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left) :=
    inferInstanceAs (IsAffine (pullback (stage x p₁ g).1.hom f))
  haveI := isLocalization_away_esAt f x p₁ es i g
  exact algebraMap_away_eq_zero_iff
    (S := Γ(((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
      (esAt f x p₁ es g i)), ⊤))
    (isIdempotentElem_esAt f x p₁ es i hidem g) a

private lemma fiberSectionsToSummandSections_es_eq_one (hidem : IsIdempotentElem (es i)) :
    (fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi).hom
      ((toFiberSections f x p₁).hom (es i)) = 1 := by
  obtain ⟨g⟩ : Nonempty (SummandIndex x p₁) := IsCofiltered.nonempty
  have h2 := congrArg (fun t => CommRingCat.Hom.hom t (esAt f x p₁ es g i))
    (toFiberSections_fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  have h3 : (toSummandSections f x p₁ es i σ y hy χ heval hi g).hom
      ((Scheme.Γ.map ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1).left).basicOpen
        (esAt f x p₁ es g i)).ι.op).hom (esAt f x p₁ es g i)) = 1 := by
    rw [Γ_map_ι_esAt_eq_one f x p₁ es i hidem g, map_one]
  have h4 : (fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi).hom
      ((toFiberSections f x p₁).hom (es i)) =
      (fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi).hom
        ((toFiberSections f x (stage x p₁ g)).hom (esAt f x p₁ es g i)) :=
    congrArg (fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi).hom
      (toFiberSections_esAt f x p₁ es g i).symm
  exact (h4.trans h2).trans h3

/-- **Surjectivity of the restriction to the summand sections**: for finite `f` and a
complete orthogonal family of idempotents, every summand section comes from a fiber
section — stage-wise, the localization of a ring away from an idempotent is a quotient
of the ring. -/
theorem surjective_fiberSectionsToSummandSections [Fintype ι]
    (hes : CompleteOrthogonalIdempotents es) :
    Function.Surjective
      (fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi).hom := by
  intro w
  obtain ⟨g, b, rfl⟩ := exists_toSummandSections_eq f x p₁ es i σ y hy χ heval hi w
  obtain ⟨a, ha⟩ := surjective_Γ_map_ι_esAt f x p₁ es i (hes.idem i) g b
  refine ⟨(toFiberSections f x (stage x p₁ g)).hom a, ?_⟩
  have h2 := congrArg (fun t => CommRingCat.Hom.hom t a)
    (toFiberSections_fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2.trans
    (congrArg (toSummandSections f x p₁ es i σ y hy χ heval hi g).hom ha)

private lemma es_mul_eq_zero_of_eq_zero (hidem : IsIdempotentElem (es i))
    {z : fiberSections f x}
    (hz : (fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi).hom z = 0) :
    (toFiberSections f x p₁).hom (es i) * z = 0 := by
  obtain ⟨p, a, rfl⟩ := exists_toFiberSections_eq f x z
  obtain ⟨w⟩ : Nonempty (CostructuredArrow (stageFunctor x p₁) p) := by
    haveI := Functor.Initial.out (F := stageFunctor x p₁) p
    infer_instance
  set a₀ : Γ(((Over.pullback @Etale ⊤ f).obj (stage x p₁ w.left).1).left, ⊤) :=
    ((fiberSectionsDiagram f x).map (op w.hom)).hom a
  have hza : (toFiberSections f x (stage x p₁ w.left)).hom a₀ =
      (toFiberSections f x p).hom a :=
    toFiberSections_w_apply f x w.hom a
  -- the restriction of `a₀` to the summand has zero germ in the summand sections
  have h2 := congrArg (fun t => CommRingCat.Hom.hom t a₀)
    (toFiberSections_fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi w.left)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  set b₀ : Γ((summand f x p₁ es i w.left).left, ⊤) :=
    (Scheme.Γ.map ((((Over.pullback @Etale ⊤ f).obj (stage x p₁ w.left).1).left).basicOpen
      (esAt f x p₁ es w.left i)).ι.op).hom a₀
  have h3 : (toSummandSections f x p₁ es i σ y hy χ heval hi w.left).hom b₀ =
      (toSummandSections f x p₁ es i σ y hy χ heval hi w.left).hom 0 := by
    rw [map_zero]
    refine h2.symm.trans ?_
    exact (congrArg (fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi).hom
      hza).trans hz
  -- descend the vanishing to a later stage
  obtain ⟨k, t, ht⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (CategoryTheory.forget CommRingCat)
      (colimit.isColimit (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi)))
    (i := op w.left) b₀ 0).mp h3
  have h5 : ((summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map t).hom b₀ = 0 := by
    have h6 : ((summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map t).hom 0 = 0 :=
      map_zero _
    exact ht.trans h6
  -- transfer via the naturality of the stage-wise restriction
  set a₁ : Γ(((Over.pullback @Etale ⊤ f).obj (stage x p₁ k.unop).1).left, ⊤) :=
    ((fiberSectionsDiagram f x).map (op ((stageFunctor x p₁).map t.unop))).hom a₀ with ha₁
  have h7 := congrArg (fun φ => CommRingCat.Hom.hom φ a₀)
    ((restrictToSummand f x p₁ es i σ y hy χ heval hi).naturality t)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h7
  have h8 : (Scheme.Γ.map ((((Over.pullback @Etale ⊤ f).obj
      (stage x p₁ k.unop).1).left).basicOpen (esAt f x p₁ es k.unop i)).ι.op).hom a₁ = 0 :=
    h7.trans h5
  -- the kernel description at the later stage
  have h9 : esAt f x p₁ es k.unop i * a₁ = 0 :=
    (Γ_map_ι_esAt_eq_zero_iff f x p₁ es i hidem k.unop a₁).mp h8
  have h10 := congrArg (toFiberSections f x (stage x p₁ k.unop)).hom h9
  rw [map_mul, map_zero, toFiberSections_esAt f x p₁ es k.unop i] at h10
  have h11 : (toFiberSections f x (stage x p₁ k.unop)).hom a₁ =
      (toFiberSections f x (stage x p₁ w.left)).hom a₀ :=
    toFiberSections_w_apply f x ((stageFunctor x p₁).map t.unop) a₀
  rwa [h11, hza] at h10

/-- **The summand sections are the localization of the fiber sections away from the
distinguished idempotent**: for finite `f` and a complete orthogonal family of
idempotents `es` at the splitting stage, the colimit of the summand sections is the
localization of the fiber sections at the powers of
`e = (toFiberSections f x p₁) (es i)`, via the restriction map. -/
theorem isLocalization_awaySelf_summandSections [Fintype ι]
    (hes : CompleteOrthogonalIdempotents es) :
    IsLocalization.Away ((toFiberSections f x p₁).hom (es i))
      (summandSections f x p₁ es i σ y hy χ heval hi) := by
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have h2 : algebraMap (fiberSections f x)
        (summandSections f x p₁ es i σ y hy χ heval hi) (s : fiberSections f x) = 1 := by
      rw [algebraMap_summandSections_eq, ← hn, map_pow,
        fiberSectionsToSummandSections_es_eq_one f x p₁ es i σ y hy χ heval hi
          (hes.idem i), one_pow]
    rw [h2]
    exact isUnit_one
  · intro z
    obtain ⟨a, ha⟩ := surjective_fiberSectionsToSummandSections f x p₁ es i σ y hy χ
      heval hi hes z
    refine ⟨(a, 1), ?_⟩
    rw [OneMemClass.coe_one, map_one, mul_one, algebraMap_summandSections_eq, ha]
  · intro z₁ z₂ h
    rw [algebraMap_summandSections_eq] at h
    have h0 : (fiberSectionsToSummandSections f x p₁ es i σ y hy χ heval hi).hom
        (z₁ - z₂) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h
    have h1 := es_mul_eq_zero_of_eq_zero f x p₁ es i σ y hy χ heval hi (hes.idem i) h0
    refine ⟨⟨_, Submonoid.mem_powers ((toFiberSections f x p₁).hom (es i))⟩, ?_⟩
    change (toFiberSections f x p₁).hom (es i) * z₁ =
      (toFiberSections f x p₁).hom (es i) * z₂
    rw [← sub_eq_zero, ← mul_sub]
    exact h1

end IsFinite

/-!
### Evaluation and unit descent for summand sections
-/

/-- **Evaluation of germs of summand sections at the lifted point**: the value at `y`
of the germ of a summand section is its evaluation at the lifted geometric point of
the summand. -/
theorem eval_toSummandSections (g : SummandIndex x p₁)
    (b : Γ((summand f x p₁ es i g).left, ⊤)) :
    (strictLocalizationEval y).hom
        ((summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi).hom
          ((toSummandSections f x p₁ es i σ y hy χ heval hi g).hom b)) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom
        (((summandPoint f x p₁ es i σ y hy χ heval hi g).val.appTop).hom b) := by
  have h2 := congrArg (fun t => CommRingCat.Hom.hom t b)
    (toSummandSections_summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval
      hi g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  have h3 := congrArg (fun t => CommRingCat.Hom.hom t b)
    (toStrictLocalization_strictLocalizationEval y
      ⟨summand f x p₁ es i g, summandPoint f x p₁ es i σ y hy χ heval hi g⟩)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
  have h4 : ((summandPoint f x p₁ es i σ y hy χ heval hi g).val.appTop).hom b =
      (Scheme.Γ.map (summandPoint f x p₁ es i σ y hy χ heval hi g).val.op).hom b :=
    congrArg (fun t => CommRingCat.Hom.hom t b) (Scheme.Γ_map_op _).symm
  exact ((congrArg (strictLocalizationEval y).hom h2).trans h3).trans
    (congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom h4).symm

/-- Units of a filtered colimit of commutative rings descend to a stage. -/
private lemma exists_isUnit_colimit_map_of_isUnit {J : Type (u + 1)} [Category.{u} J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) [HasColimitsOfShape J CommRingCat.{u}]
    [PreservesColimitsOfShape J (CategoryTheory.forget CommRingCat.{u})]
    (j : J) (b : D.obj j) (hb : IsUnit ((colimit.ι D j).hom b)) :
    ∃ (k : J) (t : j ⟶ k), IsUnit ((D.map t).hom b) := by
  obtain ⟨c, hc⟩ := hb.exists_right_inv
  obtain ⟨jc, c₀, hc₀⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget CommRingCat) (colimit.isColimit D)) c
  have hc₀' : (colimit.ι D jc).hom c₀ = c := hc₀
  have e₁ := congrArg (fun φ => CommRingCat.Hom.hom φ b)
    (colimit.w D (IsFiltered.leftToMax j jc))
  have e₂ := congrArg (fun φ => CommRingCat.Hom.hom φ c₀)
    (colimit.w D (IsFiltered.rightToMax j jc))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e₁ e₂
  have hprod : (colimit.ι D (IsFiltered.max j jc)).hom
      ((D.map (IsFiltered.leftToMax j jc)).hom b *
        (D.map (IsFiltered.rightToMax j jc)).hom c₀) =
      (colimit.ι D (IsFiltered.max j jc)).hom 1 := by
    rw [map_mul, map_one, e₁, e₂, hc₀', hc]
  obtain ⟨k, t, ht⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (CategoryTheory.forget CommRingCat)
      (colimit.isColimit D)) _ _).mp hprod
  have ht' : (D.map t).hom ((D.map (IsFiltered.leftToMax j jc)).hom b) *
      (D.map t).hom ((D.map (IsFiltered.rightToMax j jc)).hom c₀) = 1 := by
    have h1 : (D.map t).hom ((D.map (IsFiltered.leftToMax j jc)).hom b *
        (D.map (IsFiltered.rightToMax j jc)).hom c₀) = (D.map t).hom 1 := ht
    rwa [map_one, map_mul] at h1
  refine ⟨k, IsFiltered.leftToMax j jc ≫ t, ?_⟩
  have hmap : (D.map (IsFiltered.leftToMax j jc ≫ t)).hom b =
      (D.map t).hom ((D.map (IsFiltered.leftToMax j jc)).hom b) := by
    rw [Functor.map_comp]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [hmap]
  exact IsUnit.of_mul_eq_one _ ht'

/-- **Units of the summand sections descend to a stage**: a summand section whose germ
in the summand sections colimit is invertible becomes invertible after restriction to
some finer stage. -/
theorem exists_isUnit_map_of_isUnit (g : SummandIndex x p₁)
    (b : Γ((summand f x p₁ es i g).left, ⊤))
    (hb : IsUnit ((toSummandSections f x p₁ es i σ y hy χ heval hi g).hom b)) :
    ∃ (g' : SummandIndex x p₁) (t : g' ⟶ g),
      IsUnit (((summandSectionsDiagram f x p₁ es i σ y hy χ heval hi).map
        (op t)).hom b) := by
  obtain ⟨k, t, ht⟩ := exists_isUnit_colimit_map_of_isUnit
    (summandSectionsDiagram f x p₁ es i σ y hy χ heval hi) (op g) b hb
  exact ⟨k.unop, t.unop, ht⟩

end AlgebraicGeometry.Scheme.Etale
