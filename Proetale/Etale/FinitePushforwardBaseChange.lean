/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.FinitePushforwardBaseChangeStalk
import Proetale.Etale.FinitePushforwardExact
import Proetale.Etale.FinitePushforwardLifts

/-!
# Proper base change for finite morphisms

Let

```
Y' --g'--> Y
|          |
f'         f
↓          ↓
X' --g---> X
```

be a cartesian square of schemes with `f` **finite**. This file works towards blueprint
`lemma:pbc-finite`: the base change transformation is an isomorphism, both on abelian
sheaves and, in the derived form, on all of the bounded below derived category (no
torsion hypothesis is needed for finite morphisms).

The identification of the two index sets appearing in the stalk formulae for `f` and
for `f'` is the universal property of the cartesian square: the lifts of a geometric
point `z` of `X'` to `Y'` correspond bijectively, via `- ≫ g'`, to the lifts of `z ≫ g`
to `Y`.

## Main results

- `AlgebraicGeometry.Scheme.Etale.liftEquivCompLift`: the lifts of a geometric point of
  `X'` to `Y'` are the lifts of the induced geometric point of `X` to `Y`.
- `AlgebraicGeometry.Scheme.Etale.isIso_etaleBaseChangeNatTrans_app_of_isFinite`: the
  sheaf-level base change transformation is an isomorphism.
- `AlgebraicGeometry.Scheme.Etale.isIso_derivedBaseChangeNatTrans_app_of_isFinite`:
  **proper base change for finite morphisms** on the bounded below derived category.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme.Etale

attribute [local instance] finite_maximalSpectrum_fiberSections

variable {X X' Y Y' : Scheme.{u}} (f : Y ⟶ X) (g : X' ⟶ X) (f' : Y' ⟶ X') (g' : Y' ⟶ Y)
  (hc : IsPullback g' f' f g)

section Lifts

variable {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
  (z : Spec (CommRingCat.of Ω) ⟶ X')
  (ε : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))

include hc

/-- **The lifts of a geometric point along a base change**: for a cartesian square, the
lifts of a geometric point `z` of `X'` to `Y'` correspond bijectively, via composition
with `g'`, to the lifts of the geometric point `z ≫ g` of `X` to `Y`. This is the
universal property of the cartesian square. -/
noncomputable def liftEquivCompLift :
    {y' : Spec (CommRingCat.of Ω') ⟶ Y' // y' ≫ f' = ε ≫ z} ≃
      {y : Spec (CommRingCat.of Ω') ⟶ Y // y ≫ f = ε ≫ (z ≫ g)} where
  toFun y' := ⟨y'.1 ≫ g', comp_lift_over f g f' g' hc y'.2⟩
  invFun y := ⟨hc.lift y.1 (ε ≫ z) (by rw [y.2, Category.assoc]), hc.lift_snd _ _ _⟩
  left_inv y' := by
    refine Subtype.ext (hc.hom_ext ?_ ?_)
    · exact hc.lift_fst _ _ _
    · exact (hc.lift_snd _ _ _).trans y'.2.symm
  right_inv y := Subtype.ext (hc.lift_fst _ _ _)

omit [IsSepClosed Ω] [IsSepClosed Ω'] in
@[simp]
lemma liftEquivCompLift_apply_coe
    (y' : {y' : Spec (CommRingCat.of Ω') ⟶ Y' // y' ≫ f' = ε ≫ z}) :
    (liftEquivCompLift f g f' g' hc z ε y').1 = y'.1 ≫ g' :=
  rfl

end Lifts

section BaseChange

include hc

/-- **The base change transformation for a finite morphism is an isomorphism** (the
sheaf-level half of blueprint `lemma:pbc-finite`): for a cartesian square with `f`
finite and every abelian sheaf `F` on the small étale site of `Y`, the canonical map
`g^* (f_* F) ⟶ f'_* (g'^* F)` is an isomorphism.

On the stalk at a geometric point `z` of `X'`, both sides are the product of the stalks
of `F` over the lifts of `z ≫ g` to `Y` — on the left by the stalk formula for `f`, on
the right by the stalk formula for `f'` composed with the identification of the stalks
of `g'^* F` at the lifts of `z` to `Y'`. The two index sets agree because composing
with `g'` identifies the lifts of `z` to `Y'` with the lifts of `z ≫ g` to `Y`. -/
theorem isIso_etaleBaseChangeNatTrans_app_of_isFinite [IsFinite f]
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    IsIso ((etaleBaseChangeNatTrans f g f' g' hc.w).app F) := by
  haveI : IsFinite f' := MorphismProperty.of_isPullback hc inferInstance
  refine isIso_etaleBaseChangeNatTrans_app_of_forall f g f' g' hc F fun p ↦ ?_
  set Ω := SeparableClosure (X'.residueField p) with hΩ
  set z : Spec (CommRingCat.of Ω) ⟶ X' := X'.sepClosurePoint p with hz
  set ψ : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω) with hψ
  -- the family of *all* lifts of `z` to `Y'`, indexed by the maximal ideals of the
  -- fiber sections of `f'` at `z`
  set e := liftEquivMaximalSpectrum f' z with he
  refine ⟨MaximalSpectrum (fiberSections f' z), inferInstance, fun m ↦ (e.symm m).1,
    fun m ↦ (e.symm m).2, ?_, ?_⟩
  · refine isIso_pushforwardStalkToPiStalk_of_bijective f' z ψ _ _ ?_ _
    have hid : (fun m ↦ maximalSpectrumOfLift f' z ψ (e.symm m).1 (e.symm m).2) = id :=
      funext fun m ↦ e.apply_symm_apply m
    rw [hid]
    exact Function.bijective_id
  · refine isIso_pushforwardStalkToPiStalk_of_bijective f (z ≫ g) ψ _ _ ?_ F
    -- the maximal ideal attached to the composed lift is the image of `m` under the
    -- composition of three bijections
    have hcomp : (fun m ↦ maximalSpectrumOfLift f (z ≫ g) ψ ((e.symm m).1 ≫ g')
          (comp_lift_over f g f' g' hc (e.symm m).2)) =
        ⇑(e.symm.trans ((liftEquivCompLift f g f' g' hc z
          (Spec.map (CommRingCat.ofHom ψ))).trans
            (liftEquivMaximalSpectrum f (z ≫ g)))) :=
      rfl
    rw [hcomp]
    exact Equiv.bijective _

section Derived

variable [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf Y.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X'.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf Y'.smallEtaleTopology Ab.{u + 1})]

/-- **Proper base change for finite morphisms** (blueprint `lemma:pbc-finite`): for a
cartesian square of schemes with `f` finite, the derived base change transformation
`Rf_* ⋙ g^* ⟶ g'^* ⋙ Rf'_*` is an isomorphism on *every* object of the bounded below
derived category of abelian sheaves on the small étale site of `Y` — no torsion
hypothesis is needed.

Both pushforwards are exact
(`AlgebraicGeometry.Scheme.Etale.preservesFiniteColimits_etalePushforward`), so the
derived base change transformation is the underived one applied degreewise, and the
latter is an isomorphism by
`AlgebraicGeometry.Scheme.Etale.isIso_etaleBaseChangeNatTrans_app_of_isFinite`. -/
theorem isIso_derivedBaseChangeNatTrans_app_of_isFinite [IsFinite f]
    (K : DerivedCategoryPlus (Sheaf Y.smallEtaleTopology Ab.{u + 1})) :
    IsIso ((derivedBaseChangeNatTrans f g f' g' hc.w).app K) := by
  haveI : IsFinite f' := MorphismProperty.of_isPullback hc inferInstance
  exact isIso_derivedBaseChangeNatTrans_app_of_preservesFiniteColimits f g f' g' hc.w
    (fun F ↦ isIso_etaleBaseChangeNatTrans_app_of_isFinite f g f' g' hc F) K

/-- **Proper base change for finite morphisms**, natural-transformation form: the
derived base change transformation is an isomorphism of functors. -/
theorem isIso_derivedBaseChangeNatTrans_of_isFinite [IsFinite f] :
    IsIso (derivedBaseChangeNatTrans f g f' g' hc.w) := by
  haveI (K : DerivedCategoryPlus (Sheaf Y.smallEtaleTopology Ab.{u + 1})) :
      IsIso ((derivedBaseChangeNatTrans f g f' g' hc.w).app K) :=
    isIso_derivedBaseChangeNatTrans_app_of_isFinite f g f' g' hc K
  exact NatIso.isIso_of_isIso_app _

end Derived

end BaseChange

end AlgebraicGeometry.Scheme.Etale
