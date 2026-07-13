/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.AlgebraicGeometry.Sites.DerivedPushforward
import Proetale.Mathlib.AlgebraicGeometry.Sites.GeometricPoint

/-!
# Stalks of étale pullbacks at geometric points

For a morphism of schemes `g : S' ⟶ S` and a geometric point `z : Spec Ω ⟶ S'` with `Ω`
separably closed, the stalk of the pullback `g^* G` of an abelian sheaf `G` on the small
étale site of `S` at `z` is the stalk of `G` at the composed geometric point `z ≫ g`:

- `AlgebraicGeometry.Scheme.Etale.etalePullbackSheafFiberIso`: the natural isomorphism
  `etalePullback g ⋙ (geometricPoint z).sheafFiber ≅ (geometricPoint (z ≫ g)).sheafFiber`.
- `AlgebraicGeometry.Scheme.Etale.etalePullbackStalkIso`: the objectwise version.
- `AlgebraicGeometry.Scheme.Etale.toPresheafFiber_etalePullbackSheafFiberIso_inv_app` and
  `unit_toPresheafFiber_etalePullbackSheafFiberIso_hom_app`: compatibility of the
  isomorphism with the canonical colimit legs `G(U) ⟶ G_{z ≫ g}` of the stalks, through
  the unit of the pullback-pushforward adjunction.

The construction combines `CategoryTheory.GrothendieckTopology.Point.sheafFiberComapIso`
from mathlib, applied to the base change functor `Over.pullback @Etale ⊤ g` of the small
étale sites (which is representably flat, continuous and cover preserving), with the
identification of the fiber functor of the comapped point with the fiber functor of
`geometricPoint (z ≫ g)` via the universal property of the pullback
(`AlgebraicGeometry.Scheme.Etale.geometricPointPullbackFiberIso`).

Along the way we prove general lemmas about points of sites:

- `CategoryTheory.CategoryOfElements.mapEquivalence`: a natural isomorphism of
  type-valued functors induces an equivalence of the categories of elements.
- `CategoryTheory.GrothendieckTopology.Point.presheafFiberIsoOfIso` /
  `sheafFiberIsoOfIso`: two points with isomorphic fiber functors have isomorphic
  fiber functors on (pre)sheaves, compatibly with the colimit legs.
- `CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app`:
  the leg compatibility of mathlib's `sheafFiberComapIso`, expressing its components in
  terms of the unit of the pullback-pushforward adjunction.
-/

universe w v'' u'' v' u' v u

open CategoryTheory Limits Opposite MorphismProperty

namespace CategoryTheory

namespace CategoryOfElements

variable {C : Type u} [Category.{v} C]

/-- A natural isomorphism between type-valued functors induces an equivalence between
their categories of elements. -/
@[simps functor inverse]
def mapEquivalence {F₁ F₂ : C ⥤ Type w} (α : F₁ ≅ F₂) : F₁.Elements ≌ F₂.Elements where
  functor := map α.hom
  inverse := map α.inv
  unitIso := NatIso.ofComponents
    (fun t ↦ isoMk _ _ (Iso.refl _) (by simp))
    (fun {t₁ t₂} f ↦ (π F₁).map_injective (by simp))
  counitIso := NatIso.ofComponents
    (fun t ↦ isoMk _ _ (Iso.refl _) (by simp))
    (fun {t₁ t₂} f ↦ (π F₂).map_injective (by simp))
  functor_unitIso_comp t := (π F₂).map_injective (by simp)

end CategoryOfElements

namespace GrothendieckTopology.Point

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ₁ Φ₂ : Point.{w} J) (α : Φ₁.fiber ≅ Φ₂.fiber)
  {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]

/-- The map on stalks of presheaves induced by a morphism of the fiber functors of two
points of a site. -/
noncomputable def presheafFiberMap (β : Φ₁.fiber ⟶ Φ₂.fiber) (P : Cᵒᵖ ⥤ A) :
    Φ₁.presheafFiber.obj P ⟶ Φ₂.presheafFiber.obj P :=
  Φ₁.presheafFiberDesc
    (fun X x ↦ Φ₂.toPresheafFiber X (β.app X x) P)
    (fun X Y f x ↦ by
      rw [Φ₂.toPresheafFiber_w f (β.app X x) P]
      exact congrArg (fun t ↦ Φ₂.toPresheafFiber Y t P)
        (NatTrans.naturality_apply β f x).symm)

@[reassoc (attr := simp)]
lemma toPresheafFiber_presheafFiberMap (β : Φ₁.fiber ⟶ Φ₂.fiber) (X : C)
    (x : Φ₁.fiber.obj X) (P : Cᵒᵖ ⥤ A) :
    Φ₁.toPresheafFiber X x P ≫ presheafFiberMap Φ₁ Φ₂ β P =
      Φ₂.toPresheafFiber X (β.app X x) P := by
  simp only [presheafFiberMap]
  exact Φ₁.toPresheafFiber_presheafFiberDesc _ _ X x

/-- A natural isomorphism between the fiber functors of two points of a site induces an
isomorphism between the associated fiber functors on presheaves. -/
noncomputable def presheafFiberIsoOfIso :
    Φ₁.presheafFiber (A := A) ≅ Φ₂.presheafFiber :=
  NatIso.ofComponents
    (fun P ↦
      { hom := presheafFiberMap Φ₁ Φ₂ α.hom P
        inv := presheafFiberMap Φ₂ Φ₁ α.inv P
        hom_inv_id := by
          ext X x
          simp
        inv_hom_id := by
          ext X x
          simp })
    (fun {P Q} f ↦ by
      ext X x
      simp)

lemma presheafFiberIsoOfIso_hom_app (P : Cᵒᵖ ⥤ A) :
    (presheafFiberIsoOfIso Φ₁ Φ₂ α (A := A)).hom.app P = presheafFiberMap Φ₁ Φ₂ α.hom P :=
  rfl

lemma presheafFiberIsoOfIso_inv_app (P : Cᵒᵖ ⥤ A) :
    (presheafFiberIsoOfIso Φ₁ Φ₂ α (A := A)).inv.app P = presheafFiberMap Φ₂ Φ₁ α.inv P :=
  rfl

@[reassoc (attr := simp)]
lemma toPresheafFiber_presheafFiberIsoOfIso_hom_app (X : C) (x : Φ₁.fiber.obj X)
    (P : Cᵒᵖ ⥤ A) :
    Φ₁.toPresheafFiber X x P ≫ (presheafFiberIsoOfIso Φ₁ Φ₂ α (A := A)).hom.app P =
      Φ₂.toPresheafFiber X (α.hom.app X x) P := by
  rw [presheafFiberIsoOfIso_hom_app, toPresheafFiber_presheafFiberMap]

@[reassoc (attr := simp)]
lemma toPresheafFiber_presheafFiberIsoOfIso_inv_app (X : C) (x : Φ₂.fiber.obj X)
    (P : Cᵒᵖ ⥤ A) :
    Φ₂.toPresheafFiber X x P ≫ (presheafFiberIsoOfIso Φ₁ Φ₂ α (A := A)).inv.app P =
      Φ₁.toPresheafFiber X (α.inv.app X x) P := by
  rw [presheafFiberIsoOfIso_inv_app, toPresheafFiber_presheafFiberMap]

/-- A natural isomorphism between the fiber functors of two points of a site induces an
isomorphism between the associated fiber functors on sheaves. -/
noncomputable def sheafFiberIsoOfIso :
    Φ₁.sheafFiber (A := A) ≅ Φ₂.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafFiberIsoOfIso Φ₁ Φ₂ α)

@[reassoc (attr := simp)]
lemma toPresheafFiber_sheafFiberIsoOfIso_hom_app (G : Sheaf J A) (X : C)
    (x : Φ₁.fiber.obj X) :
    Φ₁.toPresheafFiber X x G.obj ≫ (sheafFiberIsoOfIso Φ₁ Φ₂ α (A := A)).hom.app G =
      Φ₂.toPresheafFiber X (α.hom.app X x) G.obj :=
  toPresheafFiber_presheafFiberIsoOfIso_hom_app Φ₁ Φ₂ α X x G.obj

@[reassoc (attr := simp)]
lemma toPresheafFiber_sheafFiberIsoOfIso_inv_app (G : Sheaf J A) (X : C)
    (x : Φ₂.fiber.obj X) :
    Φ₂.toPresheafFiber X x G.obj ≫ (sheafFiberIsoOfIso Φ₁ Φ₂ α (A := A)).inv.app G =
      Φ₁.toPresheafFiber X (α.inv.app X x) G.obj :=
  toPresheafFiber_presheafFiberIsoOfIso_inv_app Φ₁ Φ₂ α X x G.obj

end Transport

section Skyscraper

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (Φ : Point.{w} J)
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]

/-- The components of the skyscraper sheaf functor on morphisms are the products of
copies of the morphism. -/
@[reassoc]
lemma skyscraperSheafFunctor_map_hom_app_π {M N : A} (t : M ⟶ N) (X : C)
    (x : Φ.fiber.obj X) :
    (Φ.skyscraperSheafFunctor.map t).hom.app (op X) ≫
        Pi.π (fun (_ : Φ.fiber.obj X) ↦ N) x =
      Pi.π (fun (_ : Φ.fiber.obj X) ↦ M) x ≫ t := by
  simp [skyscraperSheafFunctor, skyscraperPresheafFunctor]

variable [HasColimitsOfSize.{w, w} A]

/-- The unit of the skyscraper sheaf adjunction is given componentwise by the canonical
colimit legs into the stalk. -/
@[reassoc]
lemma unit_skyscraperSheafAdjunction_hom_app_π (G : Sheaf J A) (X : C)
    (x : Φ.fiber.obj X) :
    (Φ.skyscraperSheafAdjunction.unit.app G).hom.app (op X) ≫
        Pi.π (fun (_ : Φ.fiber.obj X) ↦ Φ.sheafFiber.obj G) x =
      Φ.toPresheafFiber X x G.obj := by
  have h1 : Φ.skyscraperSheafAdjunction.unit.app G =
      Φ.skyscraperSheafAdjunction.homEquiv G (Φ.sheafFiber.obj G)
        (𝟙 (Φ.sheafFiber.obj G)) :=
    (Adjunction.homEquiv_id _ _).symm
  rw [h1]
  have h2 : (Φ.skyscraperSheafAdjunction.homEquiv G (Φ.sheafFiber.obj G)
      (𝟙 (Φ.sheafFiber.obj G))).hom =
      Φ.skyscraperPresheafHomEquiv (P := G.obj) (𝟙 (Φ.sheafFiber.obj G)) :=
    Φ.skyscraperSheafAdjunction_homEquiv_apply_hom (𝟙 _)
  rw [h2]
  have h3 := Φ.skyscraperPresheafHomEquiv_app_π (P := G.obj)
    (𝟙 (Φ.sheafFiber.obj G)) X x
  exact h3.trans (Category.comp_id _)

end Skyscraper

section Comap

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {K : GrothendieckTopology D} (Φ : Point.{w} K) (F : C ⥤ D) [RepresentablyFlat F]
  {J : GrothendieckTopology C} (hF : CoverPreserving J K F)
  [InitiallySmall.{w} (F ⋙ Φ.fiber).Elements]
  (A : Type u'') [Category.{v''} A] [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
  [Functor.IsContinuous F J K] [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]

/-- Leg compatibility of `Point.sheafFiberComapIso`: the isomorphism between the stalk
of a sheaf `G` at the comapped point and the stalk of the pullback of `G` at the
original point sends the colimit leg at `(U, x)` to the composition of the unit of the
pullback-pushforward adjunction with the colimit leg at `(F.obj U, x)`. -/
@[reassoc]
lemma toPresheafFiber_sheafFiberComapIso_hom_app (G : Sheaf J A) (U : C)
    (x : Φ.fiber.obj (F.obj U)) :
    (Φ.comap F hF).toPresheafFiber U x G.obj ≫
        (Φ.sheafFiberComapIso F hF A).hom.app G =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op U) ≫
        Φ.toPresheafFiber (F.obj U) x ((F.sheafPullback A J K).obj G).obj := by
  -- the conjugation identity relating the units of the two skyscraper adjunctions
  have key := unit_conjugateEquiv_symm
    ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
    ((Φ.comap F hF).skyscraperSheafAdjunction)
    (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous F hF A).hom G
  have hγ : (conjugateEquiv
      ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
      ((Φ.comap F hF).skyscraperSheafAdjunction)).symm
        (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous F hF A).hom =
      (Φ.sheafFiberComapIso F hF A).hom := rfl
  rw [hγ] at key
  -- the identification of the two skyscraper functors is the identity, so `key`
  -- relates the unit of the composed adjunction to the unit of the comapped point
  have key2 : ((F.sheafAdjunctionContinuous A J K).comp
        Φ.skyscraperSheafAdjunction).unit.app G =
      (Φ.comap F hF).skyscraperSheafAdjunction.unit.app G ≫
        (Φ.comap F hF).skyscraperSheafFunctor.map
          ((Φ.sheafFiberComapIso F hF A).hom.app G) :=
    (Category.comp_id _).symm.trans key
  -- compute the composite of the colimit leg with the component of the isomorphism
  -- through the units of the two skyscraper adjunctions
  rw [← unit_skyscraperSheafAdjunction_hom_app_π (Φ.comap F hF) G U x, Category.assoc,
    ← skyscraperSheafFunctor_map_hom_app_π (Φ.comap F hF)
      (M := (Φ.comap F hF).sheafFiber.obj G)
      (N := Φ.sheafFiber.obj ((F.sheafPullback A J K).obj G))
      ((Φ.sheafFiberComapIso F hF A).hom.app G) U x, ← Category.assoc]
  have hcomp : ((Φ.comap F hF).skyscraperSheafAdjunction.unit.app G ≫
      (Φ.comap F hF).skyscraperSheafFunctor.map
        ((Φ.sheafFiberComapIso F hF A).hom.app G)).hom.app (op U) =
      ((Φ.comap F hF).skyscraperSheafAdjunction.unit.app G).hom.app (op U) ≫
        ((Φ.comap F hF).skyscraperSheafFunctor.map
          ((Φ.sheafFiberComapIso F hF A).hom.app G)).hom.app (op U) := rfl
  rw [← hcomp, ← key2, Adjunction.comp_unit_app]
  have hcomp2 : ((F.sheafAdjunctionContinuous A J K).unit.app G ≫
      (F.sheafPushforwardContinuous A J K).map
        (Φ.skyscraperSheafAdjunction.unit.app ((F.sheafPullback A J K).obj G))).hom.app
        (op U) =
      ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op U) ≫
        (Φ.skyscraperSheafAdjunction.unit.app
          ((F.sheafPullback A J K).obj G)).hom.app (op (F.obj U)) := rfl
  rw [hcomp2, Category.assoc]
  exact congrArg
    (fun t ↦ ((F.sheafAdjunctionContinuous A J K).unit.app G).hom.app (op U) ≫ t)
    (unit_skyscraperSheafAdjunction_hom_app_π Φ ((F.sheafPullback A J K).obj G)
      (F.obj U) x)

end Comap

end GrothendieckTopology.Point

end CategoryTheory

namespace AlgebraicGeometry.Scheme

section CoverPreserving

variable {S T : Scheme.{u}} (f : S ⟶ T) (P : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.RespectsIso] [P.IsStableUnderBaseChange]

/-- The base change functor along `f : S ⟶ T` preserves covers of the small
Grothendieck topologies: this is the cover preservation part of the continuity
instance established in `Proetale/Mathlib/AlgebraicGeometry/Sites/Small.lean`. -/
lemma coverPreserving_smallPullback :
    CoverPreserving (T.smallGrothendieckTopology P) (S.smallGrothendieckTopology P)
      (Over.pullback P ⊤ f) :=
  ⟨fun {U R} hR ↦ by
    rw [Functor.mem_inducedTopology_sieves_iff, ← Sieve.functorPushforward_comp]
    refine GrothendieckTopology.functorPushforward_mem_of_iso _
      (Over.pullbackCompForgetIso (P := P) (Q := ⊤) f).symm R ?_
    rw [Sieve.functorPushforward_comp]
    exact (GrothendieckTopology.coverPreserving_overPullback
      (J := Scheme.grothendieckTopology P) f).cover_preserve
      (by rwa [Functor.mem_inducedTopology_sieves_iff] at hR)⟩

end CoverPreserving

namespace Etale

variable {S' S : Scheme.{u}} (g : S' ⟶ S) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (z : Spec (CommRingCat.of Ω) ⟶ S')

instance : RepresentablyFlat (Over.pullback @Etale ⊤ g) :=
  flat_of_preservesFiniteLimits _

@[reassoc (attr := simp)]
lemma overPullback_map_left_fst {U V : S.Etale} (φ : U ⟶ V) :
    ((Over.pullback @Etale ⊤ g).map φ).left ≫ pullback.fst V.hom g =
      pullback.fst U.hom g ≫ φ.left := by
  simp [MorphismProperty.Over.pullback]

@[reassoc (attr := simp)]
lemma overPullback_map_left_snd {U V : S.Etale} (φ : U ⟶ V) :
    ((Over.pullback @Etale ⊤ g).map φ).left ≫ pullback.snd V.hom g =
      pullback.snd U.hom g := by
  simp [MorphismProperty.Over.pullback]

/-- The fiber functor of the geometric point `z` of `S'` composed with the base change
functor of the small étale sites is naturally isomorphic to the fiber functor of the
composed geometric point `z ≫ g` of `S`: a lift of `z` to `U ×_S S'` corresponds to a
lift of `z ≫ g` to `U` via the universal property of the pullback. -/
noncomputable def geometricPointPullbackFiberIso :
    Over.pullback @Etale ⊤ g ⋙ (geometricPoint z).fiber ≅
      (geometricPoint (z ≫ g)).fiber :=
  NatIso.ofComponents
    (fun U ↦
      { hom := TypeCat.ofHom fun u ↦
          geometricPoint.mkFiber (z ≫ g) (u.val ≫ pullback.fst U.hom g)
            (by
              have hu : u.val ≫ pullback.snd U.hom g = z := u.property
              rw [Category.assoc, pullback.condition, ← Category.assoc, hu])
        inv := TypeCat.ofHom fun v ↦
          geometricPoint.mkFiber z (pullback.lift v.val z (by exact v.property))
            (pullback.lift_snd _ _ _)
        hom_inv_id := by
          apply ConcreteCategory.hom_ext
          intro u
          refine Subtype.ext (pullback.hom_ext ?_ ?_)
          · exact pullback.lift_fst _ _ _
          · have hu : u.val ≫ pullback.snd U.hom g = z := u.property
            exact (pullback.lift_snd _ _ _).trans hu.symm
        inv_hom_id := by
          apply ConcreteCategory.hom_ext
          intro v
          exact Subtype.ext (pullback.lift_fst _ _ _) })
    (fun {U V} φ ↦ by
      apply ConcreteCategory.hom_ext
      intro u
      refine Subtype.ext ?_
      change (u.val ≫ ((Over.pullback @Etale ⊤ g).map φ).left) ≫ pullback.fst V.hom g =
        (u.val ≫ pullback.fst U.hom g) ≫ φ.left
      rw [Category.assoc, overPullback_map_left_fst, ← Category.assoc])

@[simp]
lemma geometricPointPullbackFiberIso_hom_app_val (U : S.Etale)
    (u : (geometricPoint z).fiber.obj ((Over.pullback @Etale ⊤ g).obj U)) :
    ((geometricPointPullbackFiberIso g z).hom.app U u).val =
      u.val ≫ pullback.fst U.hom g :=
  rfl

@[reassoc (attr := simp)]
lemma geometricPointPullbackFiberIso_inv_app_val_fst (U : S.Etale)
    (v : (geometricPoint (z ≫ g)).fiber.obj U) :
    ((geometricPointPullbackFiberIso g z).inv.app U v).val ≫ pullback.fst U.hom g =
      v.val :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma geometricPointPullbackFiberIso_inv_app_val_snd (U : S.Etale)
    (v : (geometricPoint (z ≫ g)).fiber.obj U) :
    ((geometricPointPullbackFiberIso g z).inv.app U v).val ≫ pullback.snd U.hom g =
      z :=
  pullback.lift_snd _ _ _

/-- The étale neighbourhoods of `z` of the form `U ×_S S'` with `U` an étale
neighbourhood of `z ≫ g` admit an initial small family, by transport along
`geometricPointPullbackFiberIso` from the corresponding statement for `z ≫ g`. -/
instance initiallySmall_pullback_comp_fiber_elements :
    InitiallySmall.{u}
      (Over.pullback @Etale ⊤ g ⋙ (geometricPoint z).fiber).Elements :=
  initiallySmall_of_initial_of_initiallySmall
    (CategoryOfElements.mapEquivalence (geometricPointPullbackFiberIso g z).symm).functor

/-- **Stalks of étale pullbacks at geometric points**: for a morphism of schemes
`g : S' ⟶ S` and a geometric point `z` of `S'`, the stalk of the pullback of an abelian
sheaf on the small étale site of `S` at `z` is naturally isomorphic to the stalk of the
sheaf itself at the composed geometric point `z ≫ g`. -/
noncomputable def etalePullbackSheafFiberIso :
    etalePullback g ⋙ (geometricPoint z).sheafFiber ≅
      (geometricPoint (z ≫ g)).sheafFiber :=
  -- the instances for the comparison of the comapped point, provided as local
  -- instances so that they apply at all definitionally equal spellings of the
  -- small étale sites
  haveI : RepresentablyFlat (Over.pullback @Etale ⊤ g) := inferInstance
  haveI : InitiallySmall.{u}
      (Over.pullback @Etale ⊤ g ⋙ (geometricPoint z).fiber).Elements := inferInstance
  haveI : (Over.pullback @Etale ⊤ g).IsContinuous (S.smallGrothendieckTopology @Etale)
      S'.smallEtaleTopology :=
    inferInstanceAs ((Over.pullback @Etale ⊤ g).IsContinuous
      (S.smallGrothendieckTopology @Etale) (S'.smallGrothendieckTopology @Etale))
  haveI : ((Over.pullback @Etale ⊤ g).sheafPushforwardContinuous Ab.{u + 1}
      (S.smallGrothendieckTopology @Etale) S'.smallEtaleTopology).IsRightAdjoint :=
    inferInstanceAs (((Over.pullback @Etale ⊤ g).sheafPushforwardContinuous Ab.{u + 1}
      (S.smallGrothendieckTopology @Etale)
      (S'.smallGrothendieckTopology @Etale)).IsRightAdjoint)
  (GrothendieckTopology.Point.sheafFiberComapIso (geometricPoint z)
      (Over.pullback @Etale ⊤ g) (coverPreserving_smallPullback g @Etale)
      Ab.{u + 1}).symm ≪≫
    GrothendieckTopology.Point.sheafFiberIsoOfIso
      ((geometricPoint z).comap (Over.pullback @Etale ⊤ g)
        (coverPreserving_smallPullback g @Etale))
      (geometricPoint (z ≫ g)) (geometricPointPullbackFiberIso g z)

/-- Objectwise version of `etalePullbackSheafFiberIso`: the stalk of `g^* G` at the
geometric point `z` is the stalk of `G` at `z ≫ g`. -/
noncomputable def etalePullbackStalkIso (G : Sheaf S.smallEtaleTopology Ab.{u + 1}) :
    (geometricPoint z).sheafFiber.obj ((etalePullback g).obj G) ≅
      (geometricPoint (z ≫ g)).sheafFiber.obj G :=
  (etalePullbackSheafFiberIso g z).app G

/-- Leg compatibility of `etalePullbackSheafFiberIso`, inverse direction: the map from
the stalk of `G` at `z ≫ g` to the stalk of `g^* G` at `z` sends the colimit leg at an
étale neighbourhood `(U, u)` of `z ≫ g` to the composition of the unit
`G(U) ⟶ (g^* G)(U ×_S S')` of the pullback-pushforward adjunction with the colimit leg
at the étale neighbourhood `(U ×_S S', (u, z))` of `z`. -/
@[reassoc]
lemma toPresheafFiber_etalePullbackSheafFiberIso_inv_app
    (G : Sheaf S.smallEtaleTopology Ab.{u + 1}) (U : S.Etale)
    (u : (geometricPoint (z ≫ g)).fiber.obj U) :
    (geometricPoint (z ≫ g)).toPresheafFiber U u G.obj ≫
        (etalePullbackSheafFiberIso g z).inv.app G =
      ((smallPullbackPushforwardAdj g @Etale Ab.{u + 1}).unit.app G).hom.app (op U) ≫
        (geometricPoint z).toPresheafFiber ((Over.pullback @Etale ⊤ g).obj U)
          ((geometricPointPullbackFiberIso g z).inv.app U u)
          ((etalePullback g).obj G).obj := by
  haveI : RepresentablyFlat (Over.pullback @Etale ⊤ g) := inferInstance
  haveI : InitiallySmall.{u}
      (Over.pullback @Etale ⊤ g ⋙ (geometricPoint z).fiber).Elements := inferInstance
  haveI : (Over.pullback @Etale ⊤ g).IsContinuous (S.smallGrothendieckTopology @Etale)
      S'.smallEtaleTopology :=
    inferInstanceAs ((Over.pullback @Etale ⊤ g).IsContinuous
      (S.smallGrothendieckTopology @Etale) (S'.smallGrothendieckTopology @Etale))
  haveI : ((Over.pullback @Etale ⊤ g).sheafPushforwardContinuous Ab.{u + 1}
      (S.smallGrothendieckTopology @Etale) S'.smallEtaleTopology).IsRightAdjoint :=
    inferInstanceAs (((Over.pullback @Etale ⊤ g).sheafPushforwardContinuous Ab.{u + 1}
      (S.smallGrothendieckTopology @Etale)
      (S'.smallGrothendieckTopology @Etale)).IsRightAdjoint)
  have h1 : (etalePullbackSheafFiberIso g z).inv.app G =
      (GrothendieckTopology.Point.sheafFiberIsoOfIso
        ((geometricPoint z).comap (Over.pullback @Etale ⊤ g)
          (coverPreserving_smallPullback g @Etale))
        (geometricPoint (z ≫ g)) (geometricPointPullbackFiberIso g z)).inv.app G ≫
      (GrothendieckTopology.Point.sheafFiberComapIso (geometricPoint z)
        (Over.pullback @Etale ⊤ g) (coverPreserving_smallPullback g @Etale)
        Ab.{u + 1}).hom.app G := rfl
  rw [h1, ← Category.assoc]
  have h2 := GrothendieckTopology.Point.toPresheafFiber_sheafFiberIsoOfIso_inv_app
    ((geometricPoint z).comap (Over.pullback @Etale ⊤ g)
      (coverPreserving_smallPullback g @Etale))
    (geometricPoint (z ≫ g)) (geometricPointPullbackFiberIso g z) G U u
  rw [h2]
  exact GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app
    (geometricPoint z) (Over.pullback @Etale ⊤ g) (coverPreserving_smallPullback g @Etale)
    Ab.{u + 1} G U ((geometricPointPullbackFiberIso g z).inv.app U u)

/-- Leg compatibility of `etalePullbackSheafFiberIso`, forward direction: the triangle
`G(U) ⟶ (g^* G)_z ⟶ G_{z ≫ g}` through the unit of the pullback-pushforward adjunction
and a lift `u` of `z` to `U ×_S S'` is the colimit leg of the stalk at `z ≫ g` at the
induced lift of `z ≫ g` to `U`. -/
@[reassoc]
lemma unit_toPresheafFiber_etalePullbackSheafFiberIso_hom_app
    (G : Sheaf S.smallEtaleTopology Ab.{u + 1}) (U : S.Etale)
    (u : (geometricPoint z).fiber.obj ((Over.pullback @Etale ⊤ g).obj U)) :
    ((smallPullbackPushforwardAdj g @Etale Ab.{u + 1}).unit.app G).hom.app (op U) ≫
        (geometricPoint z).toPresheafFiber ((Over.pullback @Etale ⊤ g).obj U) u
          ((etalePullback g).obj G).obj ≫
        (etalePullbackSheafFiberIso g z).hom.app G =
      (geometricPoint (z ≫ g)).toPresheafFiber U
        ((geometricPointPullbackFiberIso g z).hom.app U u) G.obj := by
  have h := toPresheafFiber_etalePullbackSheafFiberIso_inv_app g z G U
    ((geometricPointPullbackFiberIso g z).hom.app U u)
  have hu : (geometricPointPullbackFiberIso g z).inv.app U
      ((geometricPointPullbackFiberIso g z).hom.app U u) = u := by
    refine Subtype.ext (pullback.hom_ext ?_ ?_)
    · exact geometricPointPullbackFiberIso_inv_app_val_fst g z U
        ((geometricPointPullbackFiberIso g z).hom.app U u)
    · have hu2 : u.val ≫ pullback.snd U.hom g = z := u.property
      exact (geometricPointPullbackFiberIso_inv_app_val_snd g z U
        ((geometricPointPullbackFiberIso g z).hom.app U u)).trans hu2.symm
  rw [hu] at h
  calc ((smallPullbackPushforwardAdj g @Etale Ab.{u + 1}).unit.app G).hom.app (op U) ≫
      (geometricPoint z).toPresheafFiber ((Over.pullback @Etale ⊤ g).obj U) u
        ((etalePullback g).obj G).obj ≫
      (etalePullbackSheafFiberIso g z).hom.app G
      = ((geometricPoint (z ≫ g)).toPresheafFiber U
          ((geometricPointPullbackFiberIso g z).hom.app U u) G.obj ≫
          (etalePullbackSheafFiberIso g z).inv.app G) ≫
          (etalePullbackSheafFiberIso g z).hom.app G := by
        rw [h, Category.assoc]
    _ = (geometricPoint (z ≫ g)).toPresheafFiber U
          ((geometricPointPullbackFiberIso g z).hom.app U u) G.obj := by
        rw [Category.assoc, Iso.inv_hom_id_app]
        exact Category.comp_id _

end Etale

end AlgebraicGeometry.Scheme
