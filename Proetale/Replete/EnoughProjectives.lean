/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Proetale.Replete.Basic
import Proetale.Replete.WeaklyContractible

/-!
# `EnoughProjectives` implies `IsReplete`

We show that if a category has enough projective objects, sequential limits preserve
epimorphisms, i.e. the category is replete in the sense of `IsReplete`. This is
`prop:wc-replete` in the blueprint.
-/

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category C]

namespace IsReplete

variable (F : ℕᵒᵖ ⥤ C) (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op))
variable {P : C} [Projective P] {n₀ : ℕ} (f : P ⟶ F.obj ⟨n₀⟩)

include hF in
/-- A compatible family `P ⟶ F.obj ⟨k⟩` for all `k`, equal to `f` at `k = n₀`. Below `n₀`,
the family is given by composition with the transition maps; above `n₀`, by iterated
projective lifts. -/
private noncomputable def liftApp : (k : ℕ) → P ⟶ F.obj ⟨k⟩
  | 0 => f ≫ F.map (homOfLE (Nat.zero_le n₀)).op
  | k + 1 =>
      if h : k + 1 ≤ n₀ then
        f ≫ F.map (homOfLE h).op
      else
        haveI : Epi (F.map (homOfLE k.le_succ).op) := hF k
        Projective.factorThru (liftApp k) (F.map (homOfLE k.le_succ).op)

include hF in
private lemma liftApp_naturality (k : ℕ) :
    liftApp F hF f (k + 1) ≫ F.map (homOfLE k.le_succ).op = liftApp F hF f k := by
  rw [liftApp]
  split_ifs with h
  · -- Case `k + 1 ≤ n₀`: both `liftApp (k+1)` and `liftApp k` are composites of `f` with
    -- transition maps; equality follows from functoriality and proof irrelevance.
    have hk : k ≤ n₀ := k.le_succ.trans h
    rw [Category.assoc, ← F.map_comp, ← op_comp]
    cases k with
    | zero =>
      change f ≫ F.map _ = f ≫ F.map (homOfLE (Nat.zero_le n₀)).op
      congr 2
    | succ j =>
      rw [liftApp, dif_pos hk]
      congr 2
  · haveI : Epi (F.map (homOfLE k.le_succ).op) := hF k
    exact Projective.factorThru_comp _ _

include hF in
private lemma liftApp_at_n₀ : liftApp F hF f n₀ = f := by
  cases n₀ with
  | zero =>
    change f ≫ F.map (homOfLE (Nat.zero_le 0)).op = f
    rw [Subsingleton.elim (homOfLE (Nat.zero_le 0)) (𝟙 (0 : ℕ)), op_id, F.map_id,
      Category.comp_id]
  | succ n =>
    rw [liftApp, dif_pos (le_refl _)]
    rw [Subsingleton.elim (homOfLE (le_refl (n + 1))) (𝟙 (n + 1 : ℕ)), op_id, F.map_id,
      Category.comp_id]

include hF in
/-- The cone on `F` with apex `P` defined by `liftApp`. Its `n₀`-th projection is `f`. -/
private noncomputable def coneFromLift : Cone F where
  pt := P
  π :=
    NatTrans.ofOpSequence (fun k => liftApp F hF f k)
      (fun k => by
        dsimp
        rw [Category.id_comp]
        rw [Subsingleton.elim (homOfLE (k.le_add_right 1)) (homOfLE k.le_succ)]
        exact (liftApp_naturality F hF f k).symm)

end IsReplete

open IsReplete in
/-- If `C` has enough projectives, then sequential inverse limits preserve epimorphisms, i.e.
`C` is replete. This is the geometric content of `prop:wc-replete`. -/
instance IsReplete.of_enoughProjectives [EnoughProjectives C] : IsReplete C where
  epi_pi_app_of_forall_epi_map F hF c hc n₀ := by
    rw [EnoughProjectives.epi_iff_forall_projective]
    intro P _ f
    refine ⟨hc.lift (coneFromLift F hF f), ?_⟩
    exact (hc.fac (coneFromLift F hF f) ⟨n₀⟩).trans (liftApp_at_n₀ F hF f)

end CategoryTheory
