/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WeaklyEtale

/-!
# Weak dimension of a commutative ring

Since mathlib does not have `Tor`, we only define some special cases in low dimensions.
-/

/-- A ring `R` is absolutely flat if every ideal of `R` is pure, i.e. `R ⧸ I` is flat. -/
class Ring.AbsolutelyFlat (R : Type*) [CommRing R] where
  flat (I : Ideal R) : Module.Flat R (R ⧸ I)

/-- A ring `R` is of weak dimension `≤ 1` if any finitely generated ideal is flat. -/
class Ring.WeakDimensionLEOne (R : Type*) [CommRing R] where
  flat_of_fg (I : Ideal R) : I.FG → Module.Flat R I

namespace Ring.WeakDimensionLEOne

variable (R : Type*) [CommRing R]

/-- If `R` is of weak dimension `≤ 1` if any submodule of a flat module is flat. -/
lemma flat_submodule [Ring.WeakDimensionLEOne R] {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Module.Flat R M] :
    Module.Flat R N := by
  -- Strategy: First prove all ideals are flat, then use this to prove submodules of flat modules are flat
  have all_ideals_flat : ∀ (I : Ideal R), Module.Flat R I := by
    intro I
    classical
    rw [Module.Flat.iff_rTensor_injectiveₛ]
    intro P _ _ J
    -- Strategy: I is the direct limit of its FG submodules (which are FG ideals since Ideal R = Submodule R R)
    -- Use Submodule.FG.rTensor.directLimit: DirectLimit (K ⊗ P) ≃ I ⊗ P
    -- Show rTensor I J.subtype is injective by factoring through this isomorphism
    -- and applying Module.DirectLimit.lift_injective
    sorry
  -- Now use that all ideals are flat to prove submodules of flat modules are flat
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ J
  -- Need: rTensor N J.subtype is injective
  -- Strategy: Use the fact that all ideals are flat
  -- For any x in ker(rTensor N J.subtype), we need to show x = 0
  sorry

end Ring.WeakDimensionLEOne
