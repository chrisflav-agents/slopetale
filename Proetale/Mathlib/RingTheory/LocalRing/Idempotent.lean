/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Idempotents in a local ring

A local ring has only the trivial idempotents `0` and `1`.
-/

namespace IsIdempotentElem

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- The only idempotents of a local ring are `0` and `1`. -/
theorem eq_zero_or_one_of_isLocalRing {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hadd : e + (1 - e) = 1 := by ring
  have hmul : e * (1 - e) = 0 := by
    have : e * (1 - e) = e - e * e := by ring
    rw [this, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hadd with hu | hu
  · exact .inr (sub_eq_zero.mp (hu.mul_right_eq_zero.mp hmul)).symm
  · exact .inl (hu.mul_right_eq_zero.mp (mul_comm e (1 - e) ▸ hmul))

/-- In a local ring, an element is idempotent if and only if it is `0` or `1`. -/
theorem iff_eq_zero_or_one_of_isLocalRing {e : R} : IsIdempotentElem e ↔ e = 0 ∨ e = 1 :=
  ⟨eq_zero_or_one_of_isLocalRing, by rintro (rfl | rfl) <;> simp [IsIdempotentElem]⟩

end IsIdempotentElem
