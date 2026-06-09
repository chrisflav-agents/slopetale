/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.Basic

/-!
# Sections of algebra homomorphisms out of a product

Let `σ : C × E →ₐ[R] A` be an algebra homomorphism. The element `σ (1, 0)` is
an idempotent in `A`, and dually for `σ (0, 1)`. When `σ (1, 0) = 1`
(equivalently `σ (0, 1) = 0`), the function `c ↦ σ (c, 0)` is a unital
algebra homomorphism `C →ₐ[R] A`; symmetrically for `E`.

There is no unital `AlgHom.inl : C →ₐ[R] C × E`: the natural inclusion
`c ↦ (c, 0)` fails to send `1` to `1` (it would need `(1, 0) = (1, 1)`). The
section constructions below capture the situation in which post-composition
with such an inclusion still lands in a unital algebra homomorphism. In a
local target ring, the idempotent `σ (1, 0)` is forced to be `0` or `1`, so
one of the two sections is always available.

## Main definitions

- `AlgHom.compFstSection`: from `σ : C × E →ₐ[R] A` with `σ (1, 0) = 1`,
  produce the algebra hom `C →ₐ[R] A, c ↦ σ (c, 0)`.
- `AlgHom.compSndSection`: dual, requiring `σ (0, 1) = 1`.

## Main lemmas

- `AlgHom.isIdempotentElem_apply_inl` / `_inr`: idempotency of `σ (1, 0)` and
  `σ (0, 1)`.
- `AlgHom.apply_inl_add_apply_inr`: `σ (1, 0) + σ (0, 1) = 1`.
- `AlgHom.apply_inl_eq_zero_or_one` (over a local ring): the idempotent
  `σ (1, 0)` is `0` or `1`.
-/

universe u v w₁ w₂

namespace AlgHom

section Semiring

variable {R : Type u} {A : Type v} {C : Type w₁} {E : Type w₂}
variable [CommSemiring R] [Semiring A] [Semiring C] [Semiring E]
variable [Algebra R A] [Algebra R C] [Algebra R E]
variable (σ : C × E →ₐ[R] A)

/-- For `σ : C × E →ₐ[R] A`, the image `σ (1, 0)` is an idempotent of `A`. -/
theorem isIdempotentElem_apply_inl : IsIdempotentElem (σ (1, 0)) := by
  show σ (1, 0) * σ (1, 0) = σ (1, 0)
  rw [← map_mul]
  congr 1
  ext <;> simp

/-- For `σ : C × E →ₐ[R] A`, the image `σ (0, 1)` is an idempotent of `A`. -/
theorem isIdempotentElem_apply_inr : IsIdempotentElem (σ (0, 1)) := by
  show σ (0, 1) * σ (0, 1) = σ (0, 1)
  rw [← map_mul]
  congr 1
  ext <;> simp

/-- The idempotents `σ (1, 0)` and `σ (0, 1)` sum to `1` in `A`. -/
theorem apply_inl_add_apply_inr : σ (1, 0) + σ (0, 1) = 1 := by
  rw [← map_add]
  have h : ((1, 0) + (0, 1) : C × E) = 1 := by ext <;> simp
  rw [h, map_one]

/-- The idempotents `σ (1, 0)` and `σ (0, 1)` are orthogonal. -/
theorem apply_inl_mul_apply_inr : σ (1, 0) * σ (0, 1) = 0 := by
  rw [← map_mul]
  have h : ((1, 0) * (0, 1) : C × E) = 0 := by ext <;> simp
  rw [h, map_zero]

/-- The idempotents `σ (0, 1)` and `σ (1, 0)` are orthogonal. -/
theorem apply_inr_mul_apply_inl : σ (0, 1) * σ (1, 0) = 0 := by
  rw [← map_mul]
  have h : ((0, 1) * (1, 0) : C × E) = 0 := by ext <;> simp
  rw [h, map_zero]

end Semiring

section Ring

variable {R : Type u} {A : Type v} {C : Type w₁} {E : Type w₂}
variable [CommSemiring R] [Ring A] [Semiring C] [Semiring E]
variable [Algebra R A] [Algebra R C] [Algebra R E]
variable (σ : C × E →ₐ[R] A)

/-- If `σ (1, 0) = 1`, then `σ (0, 1) = 0`. -/
theorem apply_inr_eq_zero_of_apply_inl_eq_one (h : σ (1, 0) = 1) : σ (0, 1) = 0 := by
  have eq := apply_inl_add_apply_inr σ
  rw [h] at eq
  -- eq : 1 + σ (0, 1) = 1
  have : (1 : A) + σ (0, 1) = 1 + 0 := by rw [add_zero]; exact eq
  exact add_left_cancel this

/-- If `σ (0, 1) = 1`, then `σ (1, 0) = 0`. -/
theorem apply_inl_eq_zero_of_apply_inr_eq_one (h : σ (0, 1) = 1) : σ (1, 0) = 0 := by
  have eq := apply_inl_add_apply_inr σ
  rw [h] at eq
  -- eq : σ (1, 0) + 1 = 1
  have : σ (1, 0) + (1 : A) = 0 + 1 := by rw [zero_add]; exact eq
  exact add_right_cancel this

/-- If `σ (1, 0) = 0`, then `σ (0, 1) = 1`. -/
theorem apply_inr_eq_one_of_apply_inl_eq_zero (h : σ (1, 0) = 0) : σ (0, 1) = 1 := by
  have eq := apply_inl_add_apply_inr σ
  rw [h, zero_add] at eq
  exact eq

/-- If `σ (0, 1) = 0`, then `σ (1, 0) = 1`. -/
theorem apply_inl_eq_one_of_apply_inr_eq_zero (h : σ (0, 1) = 0) : σ (1, 0) = 1 := by
  have eq := apply_inl_add_apply_inr σ
  rw [h, add_zero] at eq
  exact eq

end Ring

section CompFst

variable {R : Type u} {A : Type v} {C : Type w₁} {E : Type w₂}
variable [CommSemiring R] [Ring A] [Semiring C] [Semiring E]
variable [Algebra R A] [Algebra R C] [Algebra R E]
variable (σ : C × E →ₐ[R] A) (h : σ (1, 0) = 1)

/-- The algebra homomorphism `C →ₐ[R] A`, `c ↦ σ (c, 0)`, available when
`σ (1, 0) = 1`. -/
def compFstSection : C →ₐ[R] A where
  toFun c := σ (c, 0)
  map_one' := h
  map_mul' x y := by
    show σ (x * y, 0) = σ (x, 0) * σ (y, 0)
    rw [← map_mul]
    congr 1
    ext <;> simp
  map_zero' := by
    show σ ((0, 0) : C × E) = 0
    have : ((0, 0) : C × E) = 0 := rfl
    rw [this, map_zero]
  map_add' x y := by
    show σ (x + y, 0) = σ (x, 0) + σ (y, 0)
    rw [← map_add]
    congr 1
    ext <;> simp
  commutes' r := by
    show σ (algebraMap R C r, 0) = algebraMap R A r
    -- `(algebraMap R C r, 0) = algebraMap R (C × E) r * (1, 0)`.
    have key : ((algebraMap R C r, (0 : E)) : C × E) =
        algebraMap R (C × E) r * (1, 0) := by
      ext <;> simp
    rw [key, map_mul, σ.commutes, h, mul_one]

@[simp]
theorem compFstSection_apply (c : C) : compFstSection σ h c = σ (c, 0) := rfl

end CompFst

section CompSnd

variable {R : Type u} {A : Type v} {C : Type w₁} {E : Type w₂}
variable [CommSemiring R] [Ring A] [Semiring C] [Semiring E]
variable [Algebra R A] [Algebra R C] [Algebra R E]
variable (σ : C × E →ₐ[R] A) (h : σ (0, 1) = 1)

/-- The algebra homomorphism `E →ₐ[R] A`, `e ↦ σ (0, e)`, available when
`σ (0, 1) = 1`. -/
def compSndSection : E →ₐ[R] A where
  toFun e := σ (0, e)
  map_one' := h
  map_mul' x y := by
    show σ (0, x * y) = σ (0, x) * σ (0, y)
    rw [← map_mul]
    congr 1
    ext <;> simp
  map_zero' := by
    show σ ((0, 0) : C × E) = 0
    have : ((0, 0) : C × E) = 0 := rfl
    rw [this, map_zero]
  map_add' x y := by
    show σ (0, x + y) = σ (0, x) + σ (0, y)
    rw [← map_add]
    congr 1
    ext <;> simp
  commutes' r := by
    show σ (0, algebraMap R E r) = algebraMap R A r
    have key : (((0 : C), algebraMap R E r) : C × E) =
        algebraMap R (C × E) r * (0, 1) := by
      ext <;> simp
    rw [key, map_mul, σ.commutes, h, mul_one]

@[simp]
theorem compSndSection_apply (e : E) : compSndSection σ h e = σ (0, e) := rfl

end CompSnd

section LocalRing

variable {R : Type u} {A : Type v} {C : Type w₁} {E : Type w₂}
variable [CommRing R] [CommRing A] [IsLocalRing A] [Ring C] [Ring E]
variable [Algebra R A] [Algebra R C] [Algebra R E]

/-- In a local target ring, an idempotent `e` is either `0` or `1`. -/
private theorem IsIdempotentElem.eq_zero_or_one_of_isLocalRing
    {e : A} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  -- `e * (1 - e) = e - e * e = 0`.
  have key : e * (1 - e) = 0 := by
    have heq : e * e = e := he
    have : e * (1 - e) = e - e * e := by ring
    rw [this, heq, sub_self]
  -- In a local ring, either `e` or `1 - e` is a unit.
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · -- `e` is a unit ⇒ `1 - e = 0` ⇒ `e = 1`.
    right
    obtain ⟨u, hu⟩ := hu
    have h0 : (u : A) * (1 - e) = 0 := by rw [hu]; exact key
    have h1 : (1 - e : A) = 0 := by
      have hcalc : (↑u⁻¹ : A) * ((↑u : A) * (1 - e)) = (↑u⁻¹ : A) * 0 := by rw [h0]
      rw [mul_zero, ← mul_assoc] at hcalc
      have huu : (↑u⁻¹ : A) * (↑u : A) = 1 := u.inv_mul
      rw [huu, one_mul] at hcalc
      exact hcalc
    -- `1 - e = 0` ⇒ `e = 1`.
    have : e = 1 := by
      have := sub_eq_zero.mp h1
      exact this.symm
    exact this
  · -- `1 - e` is a unit ⇒ `e = 0`.
    left
    obtain ⟨u, hu⟩ := hu
    have h0 : e * (u : A) = 0 := by rw [hu]; exact key
    have hcalc : (e * (↑u : A)) * (↑u⁻¹ : A) = 0 * (↑u⁻¹ : A) := by rw [h0]
    rw [zero_mul, mul_assoc] at hcalc
    have huu : (↑u : A) * (↑u⁻¹ : A) = 1 := u.val_inv
    rw [huu, mul_one] at hcalc
    exact hcalc

/-- In a local ring target, the idempotent `σ (1, 0)` is forced to be `0` or `1`. -/
theorem apply_inl_eq_zero_or_one (σ : C × E →ₐ[R] A) :
    σ (1, 0) = 0 ∨ σ (1, 0) = 1 :=
  IsIdempotentElem.eq_zero_or_one_of_isLocalRing (isIdempotentElem_apply_inl σ)

/-- In a local ring target, the idempotent `σ (0, 1)` is forced to be `0` or `1`. -/
theorem apply_inr_eq_zero_or_one (σ : C × E →ₐ[R] A) :
    σ (0, 1) = 0 ∨ σ (0, 1) = 1 :=
  IsIdempotentElem.eq_zero_or_one_of_isLocalRing (isIdempotentElem_apply_inr σ)

/-- Over a local ring target, every algebra homomorphism out of a binary product factors
through one of the two projections. The `Sum` recipient mirrors the factor through
either `C` (left disjunct, with `σ (1, 0) = 1`) or `E` (right disjunct, with `σ (0, 1) = 1`). -/
theorem exists_section_of_isLocalRing (σ : C × E →ₐ[R] A) :
    (∃ h : σ (1, 0) = 1, ∀ c e, σ (c, e) = compFstSection σ h c) ∨
    (∃ h : σ (0, 1) = 1, ∀ c e, σ (c, e) = compSndSection σ h e) := by
  rcases apply_inl_eq_zero_or_one σ with h0 | h1
  · -- σ (1, 0) = 0, so σ (0, 1) = 1; the map factors through E.
    right
    have h1' : σ (0, 1) = 1 := apply_inr_eq_one_of_apply_inl_eq_zero σ h0
    refine ⟨h1', fun c e => ?_⟩
    show σ (c, e) = σ (0, e)
    have hdecomp : ((c, e) : C × E) = (c, 0) + (0, e) := by ext <;> simp
    rw [hdecomp, map_add]
    have hc0 : σ (c, 0) = 0 := by
      have : ((c, (0 : E)) : C × E) = (c, 1) * (1, 0) := by ext <;> simp
      rw [this, map_mul, h0, mul_zero]
    rw [hc0, zero_add]
  · -- σ (1, 0) = 1, so the map factors through C.
    left
    refine ⟨h1, fun c e => ?_⟩
    show σ (c, e) = σ (c, 0)
    have h0' : σ (0, 1) = 0 := apply_inr_eq_zero_of_apply_inl_eq_one σ h1
    have hdecomp : ((c, e) : C × E) = (c, 0) + (0, e) := by ext <;> simp
    rw [hdecomp, map_add]
    have he0 : σ (0, e) = 0 := by
      have : (((0 : C), e) : C × E) = (1, e) * (0, 1) := by ext <;> simp
      rw [this, map_mul, h0', mul_zero]
    rw [he0, add_zero]

end LocalRing

end AlgHom
