/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.WithTerminal.Cone
import Mathlib.CategoryTheory.WithTerminal.Lemmas
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Ind and pro-properties

Given a morphism property `P`, we define a morphism property `ind P` that is satisfied for
`f : X ⟶ Y` if `Y` is a filtered colimit of `Yᵢ` and `fᵢ : X ⟶ Yᵢ` satisfy `P`.

We show that `ind P` inherits stability properties from `P`.

## TODOs:

- Show `ind P` is stable under composition if `P` spreads out (Christian).
-/

universe s t w' w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

instance (X : C) [HasFilteredColimits C] : ReflectsFilteredColimits (Under.forget X) := by
  constructor
  intro J _ _
  exact reflectsColimitsOfShape_of_reflectsIsomorphisms

open Opposite

namespace ObjectProperty

lemma ind_of_univLE (P : ObjectProperty C) [UnivLE.{w', w}] :
    ind.{w'} P ≤ ind.{w} P := by
  intro X ⟨J, _, _, pres, H⟩
  haveI : EssentiallySmall.{w} J :=
    @essentiallySmall_of_small_of_locallySmall J _ (UnivLE.small J) inferInstance
  exact of_essentiallySmall_index pres H

@[gcongr]
lemma ind_mono {P Q : ObjectProperty C} (h : P ≤ Q) :
    ind.{w} P ≤ ind.{w} Q := by
  intro X ⟨J, _, _, pres, H⟩
  exact ⟨J, inferInstance, inferInstance, pres, fun i ↦ h _ (H i)⟩

end ObjectProperty

namespace MorphismProperty

instance [P.ContainsIdentities] : (ind.{w} P).ContainsIdentities where
  id_mem X := le_ind _ _ (P.id_mem X)

lemma ind_of_univLE [UnivLE.{w', w}] : ind.{w'} P ≤ ind.{w} P := by
  intro X Y f hf
  rw [MorphismProperty.ind_iff_ind_underMk] at hf ⊢
  exact ObjectProperty.ind_of_univLE P.underObj _ hf

@[gcongr]
lemma underObj_mono {P Q : MorphismProperty C} (h : P ≤ Q) (X : C) :
    P.underObj (X := X) ≤ Q.underObj (X := X) :=
  fun _ ↦ h _

@[gcongr]
lemma ind_mono {P Q : MorphismProperty C} (h : P ≤ Q) : ind.{w} P ≤ ind.{w} Q := by
  intro X Y f hf
  rw [MorphismProperty.ind_iff_ind_underMk] at hf ⊢
  apply ObjectProperty.ind_mono _ _ hf
  gcongr

lemma ind_coconeι {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c)
    (j : J) (H : ∀ {i : J} (f : j ⟶ i), P (D.map f)) :
    ind.{w} P (c.ι.app j) := by
  refine ⟨Under j, inferInstance, inferInstance, Under.post D ⋙ CategoryTheory.Under.forget _,
      ?_, ?_, ?_, fun k ↦ ⟨?_, ?_⟩⟩
  · exact
      { app i := D.map i.hom
        naturality := by
          intro X Y f
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
          show D.map Y.hom = D.map X.hom ≫ ((Under.post D).map f).right
          change D.map Y.hom = D.map X.hom ≫ D.map f.right
          rw [← D.map_comp]; congr 1
          have := StructuredArrow.w f
          simp only [Functor.id_map] at this
          exact this.symm }
  · exact ((CategoryTheory.Under.forget _).mapCocone (c.underPost j)).ι
  · exact isColimitOfPreserves (CategoryTheory.Under.forget _) (hc.underPost j)
  · apply H
  · have := c.ι.naturality k.hom
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    exact this

variable {P}

/--
Let `P` be a property of morphisms. `P.Pro` is satisfied for `f : X ⟶ Y`
if there exists a family of natural maps `tᵢ : Xᵢ ⟶ Y` and `sᵢ : X ⟶ Xᵢ` indexed by `J`
such that
- `J` is cofiltered
- `X = lim Xᵢ` via `{sᵢ}ᵢ`
- `tᵢ` satisfies `P` for all `i`
- `f = sᵢ ≫ tᵢ` for all `i`.
-/
def pro (P : MorphismProperty C) : MorphismProperty C :=
  fun X Y f ↦ ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCofiltered J)
    (D : J ⥤ C) (t : D ⟶ (Functor.const J).obj Y) (s : (Functor.const J).obj X ⟶ D)
    (_ : IsLimit (Cone.mk _ s)), ∀ j, P (t.app j) ∧ s.app j ≫ t.app j = f

lemma pro_eq_unop_ind_op : pro.{w} P = (ind.{w} P.op).unop := by
  ext X Y f
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_, fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.op, NatTrans.op t,
      NatTrans.op s, isColimitOfUnop hs, fun j ↦ ⟨(hst j.1).1, by simp [← (hst j.1).2]⟩⟩
  · exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.leftOp, NatTrans.leftOp t,
      NatTrans.leftOp s, isLimitOfCoconeRightOpOfCone D.leftOp hs, fun j ↦ ⟨(hst _).1,
      op_injective (hst _).2⟩⟩

lemma ind_eq_unop_pro_op : ind.{w} P = (pro.{w} P.op).unop := by
  ext X Y f
  refine ⟨fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_, fun ⟨J, _, _, D, t, s, hs, hst⟩ ↦ ?_⟩
  · -- ind P f → (pro P.op).unop f = pro P.op f.op
    -- Use D.op, NatTrans.op t, NatTrans.op s, hs.op
    exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.op, NatTrans.op t,
      NatTrans.op s, hs.op, fun j ↦ ⟨(hst j.unop).1, by simp [← (hst j.unop).2]⟩⟩
  · -- (pro P.op).unop f → ind P f
    -- D : J ⥤ Cᵒᵖ, t : D ⟶ const(op X), s : const(op Y) ⟶ D, hs : IsLimit (Cone.mk _ s)
    -- Use D.leftOp, NatTrans.leftOp t, NatTrans.leftOp s, isColimitCoconeLeftOpOfCone D hs
    exact ⟨Jᵒᵖ, inferInstance, inferInstance, D.leftOp, NatTrans.leftOp t,
      NatTrans.leftOp s, isColimitCoconeLeftOpOfCone D hs, fun j ↦ ⟨(hst j.unop).1,
      Quiver.Hom.op_inj (hst j.unop).2⟩⟩

@[gcongr]
lemma unop_mono {P Q : MorphismProperty Cᵒᵖ} (h : P ≤ Q) : P.unop ≤ Q.unop :=
  fun _ _ _ hf ↦ h _ hf

@[gcongr]
lemma op_mono {P Q : MorphismProperty C} (h : P ≤ Q) : P.op ≤ Q.op :=
  fun _ _ _ hf ↦ h _ hf

variable (P) in
lemma le_pro : P ≤ pro.{w} P := by
  rw [pro_eq_unop_ind_op]
  conv_lhs => rw [← unop_op P]
  exact unop_mono P.op.le_ind

instance [P.ContainsIdentities] : (pro.{w} P).ContainsIdentities where
  id_mem X := le_pro _ _ (P.id_mem X)

-- Attempted proof: for `f : X ⟶ Y` in `Cᵒᵖ` (i.e. `f.unop : Y.unop ⟶ X.unop` in `C`),
-- the LHS asks `IsFinitelyPresentable (Under.mk f.unop)` in `Under Y.unop` (over `C`),
-- while the RHS asks `IsFinitelyPresentable (Under.mk f)` in `Under X` (over `Cᵒᵖ`).
-- These two coyoneda-preservation conditions involve different slice categories, so the
-- equality does not unfold definitionally.  The natural bridge is
-- `CategoryTheory.Under.opEquivOpOver : Under (op X) ≌ (Over X)ᵒᵖ`,
-- which sends `Under.mk f ↦ op (Over.mk f.unop)`, turning the RHS into
-- `IsFinitelyPresentable (op (Over.mk f.unop))` inside `(Over X.unop)ᵒᵖ`.  This is the
-- *finitely co-presentable* condition on `Over.mk f.unop`, which is in general distinct
-- from finite presentability of `Under.mk f.unop` in `Under Y.unop`.  Closing this gap
-- requires either a strengthened hypothesis (e.g. a self-dual ambient category) or a
-- restatement of the lemma using `Over` on one side.
lemma op_isFinitelyPresentable :
    (isFinitelyPresentable.{w} C).op = isFinitelyPresentable.{w} Cᵒᵖ := by
  -- The statement reduces to: for every `f : X ⟶ Y` in `Cᵒᵖ`,
  -- `IsFinitelyPresentable (Under.mk f.unop)` (in `Under Y.unop` over `C`) is equivalent to
  -- `IsFinitelyPresentable (Under.mk f)` (in `Under X` over `Cᵒᵖ`).  After unfolding the
  -- definitions, both reduce to `IsCardinalAccessible` of a coyoneda functor; the natural
  -- transport across `Under.opEquivOpOver` exchanges fp with co-fp.
  ext X Y f
  -- See the comment above; this is the residual mathematical gap.
  sorry

lemma pro_pro [LocallySmall.{w} C] (H : P ≤ isFinitelyPresentable.{w} C) :
    pro.{w} (pro.{w} P) = pro.{w} P := by
  rw [pro_eq_unop_ind_op, pro_eq_unop_ind_op, op_unop, ind_ind]
  rw [← op_isFinitelyPresentable]
  exact P.op_mono H

lemma pro_of_univLE [UnivLE.{w', w}] :
    pro.{w'} P ≤ pro.{w} P := by
  grw [pro_eq_unop_ind_op, pro_eq_unop_ind_op]
  exact unop_mono (ind_of_univLE P.op)

@[gcongr]
lemma pro_mono {P Q : MorphismProperty C} (h : P ≤ Q) : pro.{w} P ≤ pro.{w} Q := by
  grw [pro_eq_unop_ind_op, pro_eq_unop_ind_op]
  gcongr

lemma pro_coneπ {J : Type w} [SmallCategory J] [IsCofiltered J]
    {D : J ⥤ C} {c : Cone D} (hc : IsLimit c)
    (j : J) (H : ∀ {i : J} (f : i ⟶ j), P (D.map f)) :
    pro.{w} P (c.π.app j) := by
  rw [pro_eq_unop_ind_op]
  exact ind_coconeι P.op hc.op _ (fun _ ↦ H _)

-- NOTE: The previous prover agent attempted a full proof here; their attempt currently
-- fails to compile (errors around lines previously at 297, 326, 382 in the working tree).
-- Reverted to the bare `sorry` so the file compiles while the assigned `op_isFinitelyPresentable`
-- work proceeds.  See git history / `task_results` for the partial attempt.
instance [HasPullbacks C] {X Y : C} (f : X ⟶ Y) [P.IsStableUnderBaseChangeAlong f] :
    (pro.{w} P).IsStableUnderBaseChangeAlong f :=
  sorry

end CategoryTheory.MorphismProperty
