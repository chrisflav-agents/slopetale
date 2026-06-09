/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Ind

/-!
# Cofiltered limits of weakly étale morphisms

This file contains the result that a cofiltered limit of weakly étale morphisms is weakly étale.
This is Stacks 092Q-adjacent.

## Main results

* `AlgebraicGeometry.WeaklyEtale.of_pro`: If `f : X ⟶ Y` is in `pro P` for some morphism
  property `P ≤ @WeaklyEtale`, then `f` is weakly étale.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

/-- If `f` is a cofiltered limit of morphisms satisfying a property `P ≤ @WeaklyEtale`,
then `f` itself is weakly étale.

Mathematical content (Stacks 092Q-adjacent): a cofiltered limit of weakly étale morphisms is
weakly étale. The proof goes via the two ingredients of `WeaklyEtale`:

1. **Flatness**: For each `x ∈ X`, the stalk `O_{X,x}` is the filtered colimit
   `colim_i O_{X_i, π_i(x)}` (Stacks 02XX/0F2W for cofiltered limits with affine transitions).
   Each `O_{Y, f(x)} → O_{X_i, π_i(x)}` is flat by the weakly étale assumption on `t_i`.
   Filtered colimits of flat modules are flat, so the colimit map is flat.

2. **Diagonal flatness**: A similar stalk-colimit argument applies to the diagonal
   `Δ_f : X ⟶ X ×_Y X`. The diagonal of a cofiltered limit fits into compatible diagonals
   `Δ_{t_i} : X_i ⟶ X_i ×_Y X_i`, each flat by the weakly étale assumption.

The actual formalization requires the stalk-colimit description for cofiltered limits of
schemes, which is not yet in Mathlib. This is the genuine mathematical gap. -/
lemma WeaklyEtale.of_pro {P : MorphismProperty Scheme.{u}}
    (hP : P ≤ @WeaklyEtale) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : MorphismProperty.pro.{u} P f) : WeaklyEtale f := by
  -- Strategy outline (Stacks 092Q):
  -- (1) From `hf : pro P f`, extract `(J, D, t, s, hs, hts)` with `J` cofiltered, `D : J ⥤ Scheme`,
  --     `t : D ⟶ const Y`, `s : const X ⟶ D` exhibiting `X` as `lim D` (so each `s.app j` is the
  --     projection), and `t.app j ∘ s.app j = f`.
  -- (2) For each `j`, `t.app j` is weakly étale (from `hP`).
  -- (3) Decompose `WeaklyEtale` as `Flat ⊓ diagonal Flat` (via `weaklyEtale_eq_flat_inf_diagonal_flat`).
  -- (4) Flat is stalk-local. For a cofiltered limit `X = lim X_i` of schemes (with affine transitions),
  --     stalks of `X` are filtered colimits of stalks of `X_i`. A filtered colimit of flat modules
  --     over a fixed ring is flat. Apply with the modules being the stalks `O_{X_i, π_i(x)}` viewed
  --     as `O_{Y, f(x)}`-modules.
  -- (5) The diagonal `Δ_f` fits as a cofiltered limit of `Δ_{t_i}`'s; apply the same argument.
  --
  -- The bottleneck is the stalk-colimit lemma for cofiltered limits of schemes, which is the
  -- genuine mathematical content not yet in Mathlib. The Lean formalization of Stacks 092Q
  -- requires new infrastructure (stalk of cofiltered limit = colimit of stalks).
  sorry

end AlgebraicGeometry
