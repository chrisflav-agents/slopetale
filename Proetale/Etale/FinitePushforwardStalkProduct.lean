/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Proetale.Etale.FinitePushforwardSummandSystem

/-!
# The stalk of a finite pushforward as a product of summand-section colimits

This file is part 1 of stage D of the program towards the stalk formula for
pushforwards along finite morphisms (blueprint `lemma:pbc-finite`), building on
`Proetale.Etale.FinitePushforwardStalk`, `Proetale.Etale.FinitePushforwardStalkIso`
and `Proetale.Etale.FinitePushforwardSummandSystem`.

Let `f : Y ⟶ X` be a morphism of schemes, `x : Spec Ω ⟶ X` a geometric point, `p₁` an
étale neighbourhood stage of `x` carrying a complete orthogonal family of idempotent
sections `es : ι → Γ(U₁ ×_X Y)` of the fiber, and `F` an abelian sheaf on the small
étale site of `Y`. Over every stage `g` refining `p₁`, the restricted idempotents
decompose the fiber over `g` into its basic open summands, so the sections of `F` over
the fiber decompose as a finite product, compatibly with the transition maps. Since
the stalk of `f_* F` at `x` is the filtered colimit of these sections over the stages
(restricted along the initial functor `stageFunctor`), and filtered colimits commute
with finite products in `Ab` (AB5), the stalk decomposes as the finite product of the
colimits of the summand sections.

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.summandObjFunctor`: the split summands as a functor
  `SummandIndex x p₁ ⥤ Y.Etale` (no geometric point data needed), with the diagram of
  sections `AlgebraicGeometry.Scheme.Etale.summandSheafDiagram` of `F` over it.
- `AlgebraicGeometry.Scheme.Etale.pullbackStageSheafDiagram`: the diagram of the
  sections of `F` over the fibers of the stages, i.e. the restriction of the
  pushforward-stalk colimit diagram along `stageFunctor`
  (`AlgebraicGeometry.Scheme.Etale.pullbackStageSheafDiagram_eq`).
- `AlgebraicGeometry.Scheme.Etale.pullbackStageProdIso`: the stage-wise product
  decomposition of the fiber sections, natural in the stage, with objectwise
  description `AlgebraicGeometry.Scheme.Etale.stageProdIsoApp` and projections the
  restrictions to the summands
  (`AlgebraicGeometry.Scheme.Etale.pullbackStageProdIso_hom_app_π`).
- `AlgebraicGeometry.Scheme.Etale.colimitPiSummandIso`: the interchange of the
  filtered colimit over the stages with the finite product over the summands, via
  exactness of filtered colimits in `Ab.{u + 1}`.
- `AlgebraicGeometry.Scheme.Etale.pushforwardStalkIsoColimitPiSummand`: the resulting
  decomposition of the stalk of the pushforward at `x` as the finite product of the
  summand-section colimits, with the leg characterization
  `AlgebraicGeometry.Scheme.Etale.
  toPushforwardStalk_pushforwardStalkIsoColimitPiSummand_hom_π`.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X) (p₁ : (geometricPoint x).fiber.Elements)
  {ι : Type u} (es : ι → Γ(((Over.pullback @Etale ⊤ f).obj p₁.1).left, ⊤))

/-!
### The summand system without point data

The split summands and their transition maps assemble into a functor from the summand
indices to the small étale site of `Y`. In contrast to
`AlgebraicGeometry.Scheme.Etale.summandFunctor`, no geometric point of `Y` or
character data is needed.
-/

private lemma summandMap_id (i : ι) (g : SummandIndex x p₁) :
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

private lemma summandMap_comp (i : ι) {g g' g'' : SummandIndex x p₁} (u : g'' ⟶ g')
    (t : g' ⟶ g) :
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

/-- **The summand system without point data**: the functor from the summand indices to
the small étale site of `Y` sending a stage to its split summand. In contrast to
`AlgebraicGeometry.Scheme.Etale.summandFunctor`, no lifted geometric point or
character data is needed. -/
noncomputable def summandObjFunctor (i : ι) : SummandIndex x p₁ ⥤ Y.Etale where
  obj g := summand f x p₁ es i g
  map t := summandMap f x p₁ es i t
  map_id g := summandMap_id f x p₁ es i g
  map_comp u t := summandMap_comp f x p₁ es i u t

@[simp]
lemma summandObjFunctor_obj (i : ι) (g : SummandIndex x p₁) :
    (summandObjFunctor f x p₁ es i).obj g = summand f x p₁ es i g :=
  rfl

@[simp]
lemma summandObjFunctor_map (i : ι) {g g' : SummandIndex x p₁} (t : g' ⟶ g) :
    (summandObjFunctor f x p₁ es i).map t = summandMap f x p₁ es i t :=
  rfl

/-- The transition maps of the summand system commute with the cofan injections of the
basic open summands into the fibers. -/
lemma summandMap_inj (i : ι) {g g' : SummandIndex x p₁} (t : g' ⟶ g) :
    summandMap f x p₁ es i t ≫
        (cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
          (esAt f x p₁ es g)).inj i =
      (cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g').1)
          (esAt f x p₁ es g')).inj i ≫
        (Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map t).val := by
  apply MorphismProperty.Over.Hom.ext
  have h := summandMap_left_ι f x p₁ es i t
  exact h

/-!
### The diagrams of sections over the stages
-/

variable (F : Sheaf Y.smallEtaleTopology Ab.{u + 1})

/-- The diagram of the sections of `F` over the split summands of the étale
neighbourhood stages refining the splitting stage. -/
noncomputable def summandSheafDiagram (i : ι) : (SummandIndex x p₁)ᵒᵖ ⥤ Ab.{u + 1} :=
  (summandObjFunctor f x p₁ es i).op ⋙ F.obj

lemma summandSheafDiagram_obj (i : ι) (g : SummandIndex x p₁) :
    (summandSheafDiagram f x p₁ es F i).obj (op g) =
      F.obj.obj (op (summand f x p₁ es i g)) :=
  rfl

lemma summandSheafDiagram_map (i : ι) {g g' : SummandIndex x p₁} (t : g' ⟶ g) :
    (summandSheafDiagram f x p₁ es F i).map t.op =
      F.obj.map (summandMap f x p₁ es i t).op :=
  rfl

/-- The diagram of the sections of `F` over the fibers of the étale neighbourhood
stages refining the splitting stage: the restriction of the pushforward-stalk colimit
diagram along the initial functor `stageFunctor`, see
`AlgebraicGeometry.Scheme.Etale.pullbackStageSheafDiagram_eq`. -/
noncomputable def pullbackStageSheafDiagram : (SummandIndex x p₁)ᵒᵖ ⥤ Ab.{u + 1} :=
  (stageFunctor x p₁).op ⋙ (CategoryOfElements.π (geometricPoint x).fiber).op ⋙
    (Over.pullback @Etale ⊤ f).op ⋙ F.obj

/-- The stage diagram is the restriction of the pushforward-stalk colimit diagram of
`AlgebraicGeometry.Scheme.Etale.pushforwardStalkIsoColimit` along `stageFunctor`. -/
lemma pullbackStageSheafDiagram_eq :
    pullbackStageSheafDiagram f x p₁ F =
      (stageFunctor x p₁).op ⋙ ((CategoryOfElements.π (geometricPoint x).fiber).op ⋙
        (Over.pullback @Etale ⊤ f).op ⋙ F.obj) :=
  rfl

lemma pullbackStageSheafDiagram_obj (g : SummandIndex x p₁) :
    (pullbackStageSheafDiagram f x p₁ F).obj (op g) =
      F.obj.obj (op ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)) :=
  rfl

/-!
### Colimits and exactness over the summand indices in `Ab`
-/

instance : HasColimitsOfShape (SummandIndex x p₁)ᵒᵖ Ab.{u + 1} :=
  HasFilteredColimitsOfSize.HasColimitsOfShape _

instance : HasExactColimitsOfShape (SummandIndex x p₁)ᵒᵖ Ab.{u + 1} :=
  AB5OfSize.ofShape _

instance : PreservesFiniteLimits
    (colim : ((SummandIndex x p₁)ᵒᵖ ⥤ Ab.{u + 1}) ⥤ Ab.{u + 1}) :=
  HasExactColimitsOfShape.preservesFiniteLimits

/-- The value of a finite product of the summand-section diagrams commutes with the
projections of the product of functors, naturally in the stage. -/
private lemma pi_map_piObjIso {A B : (SummandIndex x p₁)ᵒᵖ} (u : A ⟶ B) :
    (∏ᶜ fun i => summandSheafDiagram f x p₁ es F i).map u ≫
        (piObjIso (fun i => summandSheafDiagram f x p₁ es F i) B).hom =
      (piObjIso (fun i => summandSheafDiagram f x p₁ es F i) A).hom ≫
        Limits.Pi.map fun i => (summandSheafDiagram f x p₁ es F i).map u := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [Category.assoc, Category.assoc, piObjIso_hom_comp_π, Limits.Pi.map_π,
    piObjIso_hom_comp_π_assoc]
  exact (Pi.π (fun i => summandSheafDiagram f x p₁ es F i) i).naturality u

/-!
### The stage-wise product decomposition
-/

variable [Fintype ι] (hes : CompleteOrthogonalIdempotents es)

include hes in
/-- The restricted idempotents at a stage form a complete orthogonal family. -/
lemma completeOrthogonalIdempotents_esAt (g : SummandIndex x p₁) :
    CompleteOrthogonalIdempotents (esAt f x p₁ es g) :=
  hes.map ((fiberSectionsDiagram f x).map (op (stageHom x p₁ g))).hom

include hes in
/-- **The stage-wise product decomposition**: the sections of `F` over the fiber of a
stage decompose as the finite product of the sections over the basic open summands of
the restricted idempotents. -/
noncomputable def stageProdIsoApp (g : SummandIndex x p₁) :
    F.obj.obj (op ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)) ≅
      ∏ᶜ fun i => (summandSheafDiagram f x p₁ es F i).obj (op g) :=
  sheafObjProdIsoOfCompleteOrthogonalIdempotents
    ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1) (esAt f x p₁ es g) F
    (completeOrthogonalIdempotents_esAt f x p₁ es hes g)

/-- The projections of the stage-wise product decomposition are the restrictions to
the basic open summands. -/
@[reassoc]
lemma stageProdIsoApp_hom_π (g : SummandIndex x p₁) (i : ι) :
    (stageProdIsoApp f x p₁ es F hes g).hom ≫
        Pi.π (fun j => (summandSheafDiagram f x p₁ es F j).obj (op g)) i =
      F.obj.map ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
        (esAt f x p₁ es g)).inj i).op := by
  have h := sheafObjProdIsoOfIsColimit_hom_π F
    (isColimitCofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
      (esAt f x p₁ es g) (completeOrthogonalIdempotents_esAt f x p₁ es hes g)) i
  exact h

private lemma stageProdIsoApp_naturality {g g' : SummandIndex x p₁} (t : g' ⟶ g) :
    (pullbackStageSheafDiagram f x p₁ F).map t.op ≫
        (stageProdIsoApp f x p₁ es F hes g').hom =
      (stageProdIsoApp f x p₁ es F hes g).hom ≫
        Limits.Pi.map fun i => (summandSheafDiagram f x p₁ es F i).map t.op := by
  refine Pi.hom_ext _ _ fun i => ?_
  have hkey : (pullbackStageSheafDiagram f x p₁ F).map t.op ≫
      F.obj.map ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g').1)
        (esAt f x p₁ es g')).inj i).op =
      F.obj.map ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
        (esAt f x p₁ es g)).inj i).op ≫
        (summandSheafDiagram f x p₁ es F i).map t.op := by
    have h3 : F.obj.map
        ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g').1)
            (esAt f x p₁ es g')).inj i ≫
          (Over.pullback @Etale ⊤ f).map ((stageFunctor x p₁).map t).val).op =
        F.obj.map (summandMap f x p₁ es i t ≫
          (cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
            (esAt f x p₁ es g)).inj i).op :=
      congrArg (fun z => F.obj.map z.op) (summandMap_inj f x p₁ es i t).symm
    rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp] at h3
    exact h3
  rw [Category.assoc, Category.assoc, Limits.Pi.map_π,
    stageProdIsoApp_hom_π f x p₁ es F hes g' i,
    stageProdIsoApp_hom_π_assoc f x p₁ es F hes g i]
  exact hkey

include hes in
/-- **The stage-wise product decomposition, natural in the stage**: the diagram of the
sections of `F` over the fibers of the stages decomposes as the finite product of the
summand-section diagrams. -/
noncomputable def pullbackStageProdIso :
    pullbackStageSheafDiagram f x p₁ F ≅
      ∏ᶜ fun i => summandSheafDiagram f x p₁ es F i :=
  NatIso.ofComponents
    (fun A => stageProdIsoApp f x p₁ es F hes A.unop ≪≫
      (piObjIso (fun i => summandSheafDiagram f x p₁ es F i) A).symm)
    (fun {A B} u => by
      rw [← cancel_mono ((piObjIso (fun i => summandSheafDiagram f x p₁ es F i) B).hom)]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
      rw [pi_map_piObjIso f x p₁ es F u]
      simp only [Iso.inv_hom_id_assoc]
      exact stageProdIsoApp_naturality f x p₁ es F hes u.unop)

/-- The components of the stage-wise product decomposition project to the restrictions
to the basic open summands. -/
@[reassoc]
lemma pullbackStageProdIso_hom_app_π (g : SummandIndex x p₁) (i : ι) :
    (pullbackStageProdIso f x p₁ es F hes).hom.app (op g) ≫
        (Pi.π (fun j => summandSheafDiagram f x p₁ es F j) i).app (op g) =
      F.obj.map ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
        (esAt f x p₁ es g)).inj i).op := by
  simp only [pullbackStageProdIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, piObjIso_inv_comp_π, Opposite.unop_op]
  exact stageProdIsoApp_hom_π f x p₁ es F hes g i

/-!
### The filtered-colimit/finite-product interchange
-/

/-- **Filtered colimits commute with finite products of the summand diagrams**: the
colimit of the product of the summand-section diagrams is the product of their
colimits, by exactness of filtered colimits in `Ab` (AB5). -/
noncomputable def colimitPiSummandIso :
    colimit (∏ᶜ fun i => summandSheafDiagram f x p₁ es F i) ≅
      ∏ᶜ fun i => colimit (summandSheafDiagram f x p₁ es F i) :=
  PreservesProduct.iso colim fun i => summandSheafDiagram f x p₁ es F i

/-- The leg characterization of the filtered-colimit/finite-product interchange. -/
@[reassoc]
lemma ι_colimitPiSummandIso_hom_π (g : SummandIndex x p₁) (i : ι) :
    colimit.ι (∏ᶜ fun j => summandSheafDiagram f x p₁ es F j) (op g) ≫
        (colimitPiSummandIso f x p₁ es F).hom ≫
        Pi.π (fun j => colimit (summandSheafDiagram f x p₁ es F j)) i =
      (Pi.π (fun j => summandSheafDiagram f x p₁ es F j) i).app (op g) ≫
        colimit.ι (summandSheafDiagram f x p₁ es F i) (op g) := by
  have h2 : (colimitPiSummandIso f x p₁ es F).hom ≫
      Pi.π (fun j => colimit (summandSheafDiagram f x p₁ es F j)) i =
      colimMap (Pi.π (fun j => summandSheafDiagram f x p₁ es F j) i) :=
    piComparison_comp_π (G := colim)
      (f := fun j => summandSheafDiagram f x p₁ es F j) i
  rw [h2]
  exact ι_colimMap _ _

/-!
### The stalk of the pushforward as a product of summand colimits
-/

/-- The stalk of the pushforward at `x` is the colimit of the sections of `F` over the
fibers of the stages refining the splitting stage, by initiality of the stages among
the étale neighbourhoods of `x`. -/
noncomputable def pushforwardStalkIsoColimitPullbackStage :
    (geometricPoint x).sheafFiber.obj ((etalePushforward f).obj F) ≅
      colimit (pullbackStageSheafDiagram f x p₁ F) :=
  pushforwardStalkIsoColimit f x F ≪≫
    (asIso (colimit.pre ((CategoryOfElements.π (geometricPoint x).fiber).op ⋙
      (Over.pullback @Etale ⊤ f).op ⋙ F.obj) (stageFunctor x p₁).op)).symm

/-- The leg characterization of the colimit description of the stalk of the
pushforward over the stages. -/
@[reassoc]
lemma toPushforwardStalk_pushforwardStalkIsoColimitPullbackStage_hom
    (g : SummandIndex x p₁) :
    toPushforwardStalk f x F (stage x p₁ g).1 (stage x p₁ g).2 ≫
        (pushforwardStalkIsoColimitPullbackStage f x p₁ F).hom =
      colimit.ι (pullbackStageSheafDiagram f x p₁ F) (op g) := by
  have h1 : toPushforwardStalk f x F (stage x p₁ g).1 (stage x p₁ g).2 =
      colimit.ι ((CategoryOfElements.π (geometricPoint x).fiber).op ⋙
        (Over.pullback @Etale ⊤ f).op ⋙ F.obj) (op (stage x p₁ g)) := rfl
  have h2 : colimit.ι (pullbackStageSheafDiagram f x p₁ F) (op g) ≫
      colimit.pre ((CategoryOfElements.π (geometricPoint x).fiber).op ⋙
        (Over.pullback @Etale ⊤ f).op ⋙ F.obj) (stageFunctor x p₁).op =
      colimit.ι ((CategoryOfElements.π (geometricPoint x).fiber).op ⋙
        (Over.pullback @Etale ⊤ f).op ⋙ F.obj) (op (stage x p₁ g)) :=
    colimit.ι_pre _ _ _
  have h3 : (pushforwardStalkIsoColimitPullbackStage f x p₁ F).hom =
      (pushforwardStalkIsoColimit f x F).hom ≫
        inv (colimit.pre ((CategoryOfElements.π (geometricPoint x).fiber).op ⋙
          (Over.pullback @Etale ⊤ f).op ⋙ F.obj) (stageFunctor x p₁).op) := rfl
  have h4 : (pushforwardStalkIsoColimit f x F).hom =
      𝟙 ((geometricPoint x).sheafFiber.obj ((etalePushforward f).obj F)) := rfl
  rw [h3, h4, Category.id_comp, IsIso.comp_inv_eq]
  exact h1.trans h2.symm

include hes in
/-- **The stalk of the pushforward as a finite product of summand colimits**: for a
complete orthogonal family of idempotents at the splitting stage, the stalk of `f_* F`
at `x` decomposes as the finite product of the colimits of the sections of `F` over
the split summand systems. -/
noncomputable def pushforwardStalkIsoColimitPiSummand :
    (geometricPoint x).sheafFiber.obj ((etalePushforward f).obj F) ≅
      ∏ᶜ fun i => colimit (summandSheafDiagram f x p₁ es F i) :=
  pushforwardStalkIsoColimitPullbackStage f x p₁ F ≪≫
    HasColimit.isoOfNatIso (pullbackStageProdIso f x p₁ es F hes) ≪≫
    colimitPiSummandIso f x p₁ es F

/-- **The leg characterization of the product decomposition of the stalk of the
pushforward**: at a stage `g`, the composite of the canonical map to the stalk with
the `i`-th projection of the decomposition is the restriction to the `i`-th basic open
summand followed by the canonical map to the summand-section colimit. -/
theorem toPushforwardStalk_pushforwardStalkIsoColimitPiSummand_hom_π
    (g : SummandIndex x p₁) (i : ι) :
    toPushforwardStalk f x F (stage x p₁ g).1 (stage x p₁ g).2 ≫
        (pushforwardStalkIsoColimitPiSummand f x p₁ es F hes).hom ≫
        Pi.π (fun j => colimit (summandSheafDiagram f x p₁ es F j)) i =
      F.obj.map ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
          (esAt f x p₁ es g)).inj i).op ≫
        colimit.ι (summandSheafDiagram f x p₁ es F i) (op g) := by
  have h0 : (pushforwardStalkIsoColimitPiSummand f x p₁ es F hes).hom =
      (pushforwardStalkIsoColimitPullbackStage f x p₁ F).hom ≫
        (HasColimit.isoOfNatIso (pullbackStageProdIso f x p₁ es F hes)).hom ≫
        (colimitPiSummandIso f x p₁ es F).hom := rfl
  rw [h0]
  simp only [Category.assoc]
  rw [toPushforwardStalk_pushforwardStalkIsoColimitPullbackStage_hom_assoc,
    HasColimit.isoOfNatIso_ι_hom_assoc,
    ι_colimitPiSummandIso_hom_π f x p₁ es F g i,
    pullbackStageProdIso_hom_app_π_assoc f x p₁ es F hes g i]

end AlgebraicGeometry.Scheme.Etale
