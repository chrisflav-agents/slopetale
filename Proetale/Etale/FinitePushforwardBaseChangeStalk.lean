/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.FinitePushforwardStalk
import Proetale.Mathlib.AlgebraicGeometry.Sites.GeometricPointBaseChange

/-!
# The base change transformation on stalks at geometric points

Let

```
Y' --g'--> Y
|f'        |f
X' --g---> X
```

be a cartesian square of schemes. This file computes the base change transformation
`etaleBaseChangeNatTrans f g f' g' : f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` of abelian sheaves on the
small étale sites on stalks at geometric points of `X'`.

The stalk of `g^* (f_* F)` at a geometric point `z` of `X'` is the stalk of `f_* F` at
`z ≫ g` (`AlgebraicGeometry.Scheme.Etale.etalePullbackSheafFiberIso`), the stalk of
`g'^* F` at a geometric point `y'` of `Y'` is the stalk of `F` at `y' ≫ g'`, and the
stalks of the pushforwards are compared to the stalks at points of the fibers by
`AlgebraicGeometry.Scheme.Etale.pushforwardStalkToStalk`. The content of this file is
that these identifications are compatible: leg by leg, the base change map on stalks is
the identity comparison.

## Main results

- `AlgebraicGeometry.Scheme.Etale.comp_lift_over`: a lift `y'` of a geometric point `z`
  of `X'` to `Y'` composes with `g'` to a lift of `z ≫ g` to `Y`.
- `AlgebraicGeometry.Scheme.Etale.unit_comp_pushforwardSquareIso_hom_app`: the key
  sections level identity, expressing the base change transformation through the unit of
  the pullback-pushforward adjunction and the canonical isomorphism
  `pushforwardSquareIso : g'_* ⋙ f_* ≅ f'_* ⋙ g_*`. It is deduced from mathlib's
  `CategoryTheory.iterated_mateEquiv_conjugateEquiv` (the base change transformation is
  the mate of `pullbackSquareIso`, which is the conjugate of `pushforwardSquareIso`) and
  `CategoryTheory.unit_mateEquiv`.
- `AlgebraicGeometry.Scheme.Etale.pushforwardStalkToStalk_etaleBaseChangeNatTrans`: the
  leg lemma. The composition of the base change map on stalks at `z` with the comparison
  map to the stalk of `g'^* F` at a lift `y'` of `z` is the comparison map from the stalk
  of `f_* F` at `z ≫ g` to the stalk of `F` at `y' ≫ g'`.
- `AlgebraicGeometry.Scheme.Etale.isIso_sheafFiber_map_etaleBaseChangeNatTrans_app` and
  `AlgebraicGeometry.Scheme.Etale.isIso_etaleBaseChangeNatTrans_app_of_forall`: the
  resulting criteria for the base change transformation to be an isomorphism, pointwise
  and globally: it suffices that the comparison maps into the finite products of the
  stalks at a finite family of lifts are isomorphisms upstairs and downstairs.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme.Etale

variable {X X' Y Y' : Scheme.{u}} (f : Y ⟶ X) (g : X' ⟶ X) (f' : Y' ⟶ X') (g' : Y' ⟶ Y)
  (hc : IsPullback g' f' f g)

section CompLift

include hc in
/-- A lift `y'` of a geometric point `z` of `X'` to `Y'` composes with `g'` to a lift of
the geometric point `z ≫ g` of `X` to `Y`. -/
lemma comp_lift_over {Ω Ω' : Scheme.{u}} {z : Ω ⟶ X'} {ε : Ω' ⟶ Ω} {y' : Ω' ⟶ Y'}
    (hy' : y' ≫ f' = ε ≫ z) : (y' ≫ g') ≫ f = ε ≫ (z ≫ g) := by
  rw [Category.assoc, hc.w, ← Category.assoc, hy', Category.assoc]

end CompLift

section SquareIso

variable (w : g' ≫ f = f' ≫ g)

/-- The sections of `pushforwardSquareIso` are given by restriction along the canonical
isomorphism `overPullbackSquareIso` of the two base changes of an étale neighbourhood. -/
lemma pushforwardSquareIso_hom_app_hom_app (G : Sheaf Y'.smallEtaleTopology Ab.{u + 1})
    (U : X.Etale) :
    ((pushforwardSquareIso f g f' g' w).hom.app G).hom.app (op U) =
      G.obj.map ((overPullbackSquareIso f g f' g' w).inv.app U).op := by
  simp [pushforwardSquareIso]

/-- The canonical isomorphism `(U ×_X Y) ×_Y Y' ≅ (U ×_X X') ×_{X'} Y'` is compatible
with the projections to `U`. -/
lemma overPullbackSquareIso_hom_app_left_fst_fst (U : X.Etale) :
    ((overPullbackSquareIso f g f' g' w).hom.app U).left ≫
        pullback.fst ((Over.pullback @Etale ⊤ g).obj U).hom f' ≫ pullback.fst U.hom g =
      pullback.fst ((Over.pullback @Etale ⊤ f).obj U).hom g' ≫ pullback.fst U.hom f := by
  simp [overPullbackSquareIso]

/-- The canonical isomorphism `(U ×_X X') ×_{X'} Y' ≅ (U ×_X Y) ×_Y Y'` is compatible
with the projections to `U`. -/
lemma overPullbackSquareIso_inv_app_left_fst_fst (U : X.Etale) :
    ((overPullbackSquareIso f g f' g' w).inv.app U).left ≫
        pullback.fst ((Over.pullback @Etale ⊤ f).obj U).hom g' ≫ pullback.fst U.hom f =
      pullback.fst ((Over.pullback @Etale ⊤ g).obj U).hom f' ≫ pullback.fst U.hom g := by
  have hcancel : ((overPullbackSquareIso f g f' g' w).inv.app U).left ≫
      ((overPullbackSquareIso f g f' g' w).hom.app U).left = 𝟙 _ := by
    rw [← MorphismProperty.Comma.comp_left,
      (overPullbackSquareIso f g f' g' w).inv_hom_id_app U]
    rfl
  rw [← overPullbackSquareIso_hom_app_left_fst_fst f g f' g' w U, ← Category.assoc, hcancel,
    Category.id_comp]

/-- **The key sections level identity**: the two ways of mapping `f_* F ⟶ g_* f'_* g'^* F`,
through the unit of the adjunction `g'^* ⊣ g'_*` and the canonical isomorphism
`pushforwardSquareIso`, respectively through the unit of `g^* ⊣ g_*` and the base change
transformation, agree.

This is a formal consequence of the fact that the base change transformation is the mate
of `pullbackSquareIso`, which is the conjugate of `pushforwardSquareIso`: taking the mate
twice in the two directions is taking the conjugate
(`CategoryTheory.iterated_mateEquiv_conjugateEquiv`). -/
theorem map_unit_comp_pushforwardSquareIso_hom_app
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    (etalePushforward f).map ((smallPullbackPushforwardAdj g' @Etale Ab.{u + 1}).unit.app F) ≫
        (pushforwardSquareIso f g f' g' w).hom.app ((etalePullback g').obj F) =
      (smallPullbackPushforwardAdj g @Etale Ab.{u + 1}).unit.app ((etalePushforward f).obj F) ≫
        (etalePushforward g).map ((etaleBaseChangeNatTrans f g f' g' w).app F) := by
  -- the iterated mate of `pullbackSquareIso` is its conjugate, i.e. `pushforwardSquareIso`
  have key := iterated_mateEquiv_conjugateEquiv
    (smallPullbackPushforwardAdj f @Etale Ab.{u + 1})
    (smallPullbackPushforwardAdj f' @Etale Ab.{u + 1})
    (smallPullbackPushforwardAdj g @Etale Ab.{u + 1})
    (smallPullbackPushforwardAdj g' @Etale Ab.{u + 1})
    (TwoSquare.mk _ _ _ _ (pullbackSquareIso f g f' g' w).hom)
  have hp : (conjugateEquiv
      ((smallPullbackPushforwardAdj f @Etale Ab.{u + 1}).comp
        (smallPullbackPushforwardAdj g' @Etale Ab.{u + 1}))
      ((smallPullbackPushforwardAdj g @Etale Ab.{u + 1}).comp
        (smallPullbackPushforwardAdj f' @Etale Ab.{u + 1})))
        (pullbackSquareIso f g f' g' w).hom = (pushforwardSquareIso f g f' g' w).hom := by
    rw [pullbackSquareIso]
    exact congrArg Iso.hom
      ((conjugateIsoEquiv
        ((smallPullbackPushforwardAdj f @Etale Ab.{u + 1}).comp
          (smallPullbackPushforwardAdj g' @Etale Ab.{u + 1}))
        ((smallPullbackPushforwardAdj g @Etale Ab.{u + 1}).comp
          (smallPullbackPushforwardAdj f' @Etale Ab.{u + 1}))).apply_symm_apply
        (pushforwardSquareIso f g f' g' w))
  rw [hp] at key
  have key' : (mateEquiv (smallPullbackPushforwardAdj g' @Etale Ab.{u + 1})
      (smallPullbackPushforwardAdj g @Etale Ab.{u + 1})
      (mateEquiv (smallPullbackPushforwardAdj f @Etale Ab.{u + 1})
        (smallPullbackPushforwardAdj f' @Etale Ab.{u + 1})
        (TwoSquare.mk _ _ _ _ (pullbackSquareIso f g f' g' w).hom))) =
      (pushforwardSquareIso f g f' g' w).hom := key
  -- the compatibility of a mate with the units of the two adjunctions
  have hu := unit_mateEquiv (smallPullbackPushforwardAdj g' @Etale Ab.{u + 1})
    (smallPullbackPushforwardAdj g @Etale Ab.{u + 1})
    (mateEquiv (smallPullbackPushforwardAdj f @Etale Ab.{u + 1})
      (smallPullbackPushforwardAdj f' @Etale Ab.{u + 1})
      (TwoSquare.mk _ _ _ _ (pullbackSquareIso f g f' g' w).hom)) F
  rw [key'] at hu
  exact hu

/-- The sections level identity `map_unit_comp_pushforwardSquareIso_hom_app`, evaluated at
an étale neighbourhood `U` of `X`: the two maps `F(U ×_X Y) ⟶ (g'^* F)((U ×_X X') ×_{X'} Y')`
agree. -/
theorem unit_comp_pushforwardSquareIso_hom_app
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) (U : X.Etale) :
    ((smallPullbackPushforwardAdj g' @Etale Ab.{u + 1}).unit.app F).hom.app
          (op ((Over.pullback @Etale ⊤ f).obj U)) ≫
        ((etalePullback g').obj F).obj.map
          ((overPullbackSquareIso f g f' g' w).inv.app U).op =
      ((smallPullbackPushforwardAdj g @Etale Ab.{u + 1}).unit.app
          ((etalePushforward f).obj F)).hom.app (op U) ≫
        ((etaleBaseChangeNatTrans f g f' g' w).app F).hom.app
          (op ((Over.pullback @Etale ⊤ g).obj U)) := by
  have h := congrArg (fun t : (etalePushforward f).obj F ⟶
      (etalePushforward g).obj ((etalePushforward f').obj ((etalePullback g').obj F)) ↦
        t.hom.app (op U)) (map_unit_comp_pushforwardSquareIso_hom_app f g f' g' w F)
  rw [← pushforwardSquareIso_hom_app_hom_app f g f' g' w ((etalePullback g').obj F) U]
  exact h

end SquareIso

section Stalk

variable {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
  (z : Spec (CommRingCat.of Ω) ⟶ X') (ε : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))

include hc

/-- The lift of an étale neighbourhood `(U, u)` of `z ≫ g` in `X` to an étale
neighbourhood of `y' ≫ g'` in `Y`, computed through the base change square: transporting
the lift of `(U ×_X X', (u, z))` to `Y'` along the canonical isomorphism
`(U ×_X X') ×_{X'} Y' ≅ (U ×_X Y) ×_Y Y'` and projecting to `U ×_X Y` gives the lift of
`(U, u)` to `Y`. -/
lemma geometricPointPullbackFiberIso_hom_app_fiber_map_pullbackFiberLift
    (y' : Spec (CommRingCat.of Ω') ⟶ Y') (hy' : y' ≫ f' = ε ≫ z) (U : X.Etale)
    (u : (geometricPoint (z ≫ g)).fiber.obj U) :
    (geometricPointPullbackFiberIso g' y').hom.app ((Over.pullback @Etale ⊤ f).obj U)
        ((geometricPoint y').fiber.map ((overPullbackSquareIso f g f' g' hc.w).inv.app U)
          (pullbackFiberLift f' z ε y' hy' ((Over.pullback @Etale ⊤ g).obj U)
            ((geometricPointPullbackFiberIso g z).inv.app U u))) =
      pullbackFiberLift f (z ≫ g) ε (y' ≫ g') (comp_lift_over f g f' g' hc hy') U u := by
  set v : (geometricPoint z).fiber.obj ((Over.pullback @Etale ⊤ g).obj U) :=
    (geometricPointPullbackFiberIso g z).inv.app U u with hv
  set p : (geometricPoint y').fiber.obj
      ((Over.pullback @Etale ⊤ f').obj ((Over.pullback @Etale ⊤ g).obj U)) :=
    pullbackFiberLift f' z ε y' hy' ((Over.pullback @Etale ⊤ g).obj U) v with hp
  set θ := (overPullbackSquareIso f g f' g' hc.w).inv.app U with hθ
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · -- the projections to `U` agree
    have h1 : ((geometricPointPullbackFiberIso g' y').hom.app
        ((Over.pullback @Etale ⊤ f).obj U)
          ((geometricPoint y').fiber.map θ p)).val =
        (p.val ≫ θ.left) ≫
          pullback.fst ((Over.pullback @Etale ⊤ f).obj U).hom g' := rfl
    rw [h1, pullbackFiberLift_val_fst, Category.assoc, Category.assoc,
      overPullbackSquareIso_inv_app_left_fst_fst f g f' g' hc.w U, ← Category.assoc,
      pullbackFiberLift_val_fst, Category.assoc,
      geometricPointPullbackFiberIso_inv_app_val_fst]
  · -- the projections to `Y` agree
    have h1 : ((geometricPointPullbackFiberIso g' y').hom.app
        ((Over.pullback @Etale ⊤ f).obj U)
          ((geometricPoint y').fiber.map θ p)).val =
        (p.val ≫ θ.left) ≫
          pullback.fst ((Over.pullback @Etale ⊤ f).obj U).hom g' := rfl
    have hw : θ.left ≫ pullback.snd ((Over.pullback @Etale ⊤ f).obj U).hom g' =
        pullback.snd ((Over.pullback @Etale ⊤ g).obj U).hom f' :=
      MorphismProperty.Over.w θ
    have hcond : pullback.fst ((Over.pullback @Etale ⊤ f).obj U).hom g' ≫
        pullback.snd U.hom f =
      pullback.snd ((Over.pullback @Etale ⊤ f).obj U).hom g' ≫ g' :=
      pullback.condition
    rw [h1, pullbackFiberLift_val_snd, Category.assoc, Category.assoc, hcond,
      ← Category.assoc θ.left, hw, ← Category.assoc, pullbackFiberLift_val_snd]

variable (F : Sheaf Y.smallEtaleTopology Ab.{u + 1})

/-- **The leg lemma**: the base change map on the stalk at a geometric point `z` of `X'`,
followed by the comparison to the stalk of `g'^* F` at a lift `y'` of `z` to `Y'` and the
identification of that stalk with the stalk of `F` at `y' ≫ g'`, is the canonical
comparison map from the stalk of `f_* F` at `z ≫ g` to the stalk of `F` at `y' ≫ g'`. -/
theorem pushforwardStalkToStalk_etaleBaseChangeNatTrans
    (y' : Spec (CommRingCat.of Ω') ⟶ Y') (hy' : y' ≫ f' = ε ≫ z) :
    (etalePullbackSheafFiberIso g z).inv.app ((etalePushforward f).obj F) ≫
        (geometricPoint z).sheafFiber.map ((etaleBaseChangeNatTrans f g f' g' hc.w).app F) ≫
        pushforwardStalkToStalk f' z ε y' hy' ((etalePullback g').obj F) ≫
        (etalePullbackSheafFiberIso g' y').hom.app F =
      pushforwardStalkToStalk f (z ≫ g) ε (y' ≫ g') (comp_lift_over f g f' g' hc hy') F := by
  refine pushforwardStalk_hom_ext f (z ≫ g) fun U u ↦ ?_
  -- the base change of `U` to `X'` and to `Y`, and the lifts of `z`, `y'`
  set V : X'.Etale := (Over.pullback @Etale ⊤ g).obj U with hV
  set W : Y.Etale := (Over.pullback @Etale ⊤ f).obj U with hW
  set v : (geometricPoint z).fiber.obj V := (geometricPointPullbackFiberIso g z).inv.app U u
    with hv
  set p : (geometricPoint y').fiber.obj ((Over.pullback @Etale ⊤ f').obj V) :=
    pullbackFiberLift f' z ε y' hy' V v with hp
  set θ := (overPullbackSquareIso f g f' g' hc.w).inv.app U with hθ
  -- the leg of the stalk of `f_* F` at `z ≫ g` at `(U, u)` maps to the leg of the stalk
  -- of `g^* f_* F` at `z` at `(V, v)`, through the unit of the adjunction `g^* ⊣ g_*`
  have h1 : toPushforwardStalk f (z ≫ g) F U u ≫
        (etalePullbackSheafFiberIso g z).inv.app ((etalePushforward f).obj F) =
      ((smallPullbackPushforwardAdj g @Etale Ab.{u + 1}).unit.app
          ((etalePushforward f).obj F)).hom.app (op U) ≫
        (geometricPoint z).toPresheafFiber V v
          ((etalePullback g).obj ((etalePushforward f).obj F)).obj :=
    toPresheafFiber_etalePullbackSheafFiberIso_inv_app g z ((etalePushforward f).obj F) U u
  -- naturality of the legs in the sheaf
  have h2 : (geometricPoint z).toPresheafFiber V v
        ((etalePullback g).obj ((etalePushforward f).obj F)).obj ≫
      (geometricPoint z).sheafFiber.map ((etaleBaseChangeNatTrans f g f' g' hc.w).app F) =
      ((etaleBaseChangeNatTrans f g f' g' hc.w).app F).hom.app (op V) ≫
        (geometricPoint z).toPresheafFiber V v
          ((etalePushforward f').obj ((etalePullback g').obj F)).obj :=
    (geometricPoint z).toPresheafFiber_naturality _ V v
  -- the comparison map to the stalk at `y'` on the leg at `(V, v)`
  have h3 : (geometricPoint z).toPresheafFiber V v
        ((etalePushforward f').obj ((etalePullback g').obj F)).obj ≫
      pushforwardStalkToStalk f' z ε y' hy' ((etalePullback g').obj F) =
      (geometricPoint y').toPresheafFiber ((Over.pullback @Etale ⊤ f').obj V) p
        ((etalePullback g').obj F).obj :=
    toPushforwardStalk_pushforwardStalkToStalk f' z ε y' hy' ((etalePullback g').obj F) V v
  -- the key sections level identity
  have h4 := unit_comp_pushforwardSquareIso_hom_app f g f' g' hc.w F U
  -- restriction along the canonical isomorphism of the two base changes
  have h5 : ((etalePullback g').obj F).obj.map θ.op ≫
      (geometricPoint y').toPresheafFiber ((Over.pullback @Etale ⊤ f').obj V) p
        ((etalePullback g').obj F).obj =
      (geometricPoint y').toPresheafFiber ((Over.pullback @Etale ⊤ g').obj W)
        ((geometricPoint y').fiber.map θ p) ((etalePullback g').obj F).obj :=
    (geometricPoint y').toPresheafFiber_w θ p ((etalePullback g').obj F).obj
  -- the leg of the stalk of `g'^* F` at `y'`, transported to the stalk of `F` at `y' ≫ g'`
  have h6 := unit_toPresheafFiber_etalePullbackSheafFiberIso_hom_app g' y' F W
    ((geometricPoint y').fiber.map θ p)
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, ← reassoc_of% h4, reassoc_of% h5, h6,
    toPushforwardStalk_pushforwardStalkToStalk]
  exact congrArg (fun t ↦ (geometricPoint (y' ≫ g')).toPresheafFiber W t F.obj)
    (geometricPointPullbackFiberIso_hom_app_fiber_map_pullbackFiberLift f g f' g' hc z ε y'
      hy' U u)

/-- **The pointwise criterion**: if the comparison maps from the stalks of the two
pushforwards into the finite products of the stalks at a finite family of lifts of `z` are
isomorphisms, then the base change transformation is an isomorphism on the stalk at `z`. -/
theorem isIso_sheafFiber_map_etaleBaseChangeNatTrans_app {ι : Type u} [Finite ι]
    (y' : ι → (Spec (CommRingCat.of Ω') ⟶ Y')) (hy' : ∀ i, y' i ≫ f' = ε ≫ z)
    (h1 : IsIso (pushforwardStalkToPiStalk f' z ε y' hy' ((etalePullback g').obj F)))
    (h2 : IsIso (pushforwardStalkToPiStalk f (z ≫ g) ε (fun i ↦ y' i ≫ g')
      (fun i ↦ comp_lift_over f g f' g' hc (hy' i)) F)) :
    IsIso ((geometricPoint z).sheafFiber.map
      ((etaleBaseChangeNatTrans f g f' g' hc.w).app F)) := by
  -- the product of the identifications of the stalks of `g'^* F` at the `y' i` with the
  -- stalks of `F` at the `y' i ≫ g'`
  set π : (∏ᶜ fun i ↦ (geometricPoint (y' i)).sheafFiber.obj ((etalePullback g').obj F)) ⟶
      ∏ᶜ fun i ↦ (geometricPoint (y' i ≫ g')).sheafFiber.obj F :=
    Limits.Pi.map fun i ↦ (etalePullbackSheafFiberIso g' (y' i)).hom.app F with hπ
  haveI : IsIso π := by
    haveI : ∀ i, IsIso ((etalePullbackSheafFiberIso g' (y' i)).hom.app F) := fun i ↦
      inferInstanceAs (IsIso (((etalePullbackSheafFiberIso g' (y' i)).app F).hom))
    exact inferInstanceAs (IsIso (Limits.Pi.map _))
  -- the leg lemma, assembled into the product
  have key : (etalePullbackSheafFiberIso g z).inv.app ((etalePushforward f).obj F) ≫
      (geometricPoint z).sheafFiber.map ((etaleBaseChangeNatTrans f g f' g' hc.w).app F) ≫
      pushforwardStalkToPiStalk f' z ε y' hy' ((etalePullback g').obj F) ≫ π =
    pushforwardStalkToPiStalk f (z ≫ g) ε (fun i ↦ y' i ≫ g')
      (fun i ↦ comp_lift_over f g f' g' hc (hy' i)) F := by
    refine Limits.Pi.hom_ext _ _ fun i ↦ ?_
    rw [Category.assoc, Category.assoc, Category.assoc, hπ, Limits.Pi.map_π,
      pushforwardStalkToPiStalk_π_assoc, pushforwardStalkToPiStalk_π]
    exact pushforwardStalkToStalk_etaleBaseChangeNatTrans f g f' g' hc z ε F (y' i) (hy' i)
  -- solve for the base change map on stalks
  have hsolve : (geometricPoint z).sheafFiber.map
      ((etaleBaseChangeNatTrans f g f' g' hc.w).app F) =
      (etalePullbackSheafFiberIso g z).hom.app ((etalePushforward f).obj F) ≫
        pushforwardStalkToPiStalk f (z ≫ g) ε (fun i ↦ y' i ≫ g')
          (fun i ↦ comp_lift_over f g f' g' hc (hy' i)) F ≫ inv π ≫
          inv (pushforwardStalkToPiStalk f' z ε y' hy' ((etalePullback g').obj F)) := by
    rw [← key]
    simp
  rw [hsolve]
  infer_instance

end Stalk

/-- **The global criterion**: if for every point `p` of `X'` there is a finite family of
lifts of the canonical geometric point at `p` to `Y'` such that the comparison maps into
the finite products of the stalks are isomorphisms upstairs and downstairs, then the base
change transformation is an isomorphism at `F`. -/
theorem isIso_etaleBaseChangeNatTrans_app_of_forall
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    (h : ∀ p : X', ∃ (ι : Type u) (_ : Finite ι)
        (y' : ι → (Spec (CommRingCat.of
          (AlgebraicClosure (SeparableClosure (X'.residueField p)))) ⟶ Y'))
        (hy' : ∀ i, y' i ≫ f' =
          Spec.map (CommRingCat.ofHom (algebraMap (SeparableClosure (X'.residueField p))
            (AlgebraicClosure (SeparableClosure (X'.residueField p))))) ≫
              X'.sepClosurePoint p),
        IsIso (pushforwardStalkToPiStalk f' (X'.sepClosurePoint p)
            (Spec.map (CommRingCat.ofHom (algebraMap (SeparableClosure (X'.residueField p))
              (AlgebraicClosure (SeparableClosure (X'.residueField p)))))) y' hy'
            ((etalePullback g').obj F)) ∧
          IsIso (pushforwardStalkToPiStalk f (X'.sepClosurePoint p ≫ g)
            (Spec.map (CommRingCat.ofHom (algebraMap (SeparableClosure (X'.residueField p))
              (AlgebraicClosure (SeparableClosure (X'.residueField p))))))
            (fun i ↦ y' i ≫ g') (fun i ↦ comp_lift_over f g f' g' hc (hy' i)) F)) :
    IsIso ((etaleBaseChangeNatTrans f g f' g' hc.w).app F) := by
  rw [isIso_iff_sheafFiber_geometricPoint' ((etaleBaseChangeNatTrans f g f' g' hc.w).app F)]
  intro p
  obtain ⟨ι, hι, y', hy', h1, h2⟩ := h p
  exact isIso_sheafFiber_map_etaleBaseChangeNatTrans_app f g f' g' hc _ _ F y' hy' h1 h2

end AlgebraicGeometry.Scheme.Etale
