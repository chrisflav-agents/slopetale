/-
Copyright (c) 2026 The Proetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Quotient
import Proetale.Mathlib.RingTheory.Etale.HenselianPairLift

/-!
# Hensel-lifting orthogonal idempotents for étale algebras over henselian local rings

This file extracts a Mathlib-PR-quality helper from
`Proetale/Mathlib/RingTheory/Etale/StrictlyHenselian.lean`'s
`exists_idempotent_lift_isolating_at_maximal`. The substantive
mathematical content is the **Stacks 0DXB Hensel-idempotent-lift
fragment**: for `A` henselian local and `B` étale over `A`, the
orthogonal idempotents of the residue decomposition
`B / m·B ≃ ∏ k_i` lift to **true** orthogonal idempotents in `B`.

## Main result

* `Algebra.Etale.exists_completeOrthogonalIdempotents_lift_of_henselian`:
  the existence of a complete orthogonal idempotent system in `B` lifting
  the canonical orthogonal idempotents of the étale-residue product
  decomposition `(IsLocalRing.ResidueField A) ⊗_A B ≃ ∏ k_i`.
-/

open IsLocalRing

namespace Algebra.Etale

universe u

/-- An idempotent that lies in the Jacobson radical of `R` (the intersection of all
maximal ideals, or equivalently `Ideal.jacobson (⊥ : Ideal R)`) is zero.

Reason: if `e ∈ jac R`, then `1 - e` is a unit; combined with the idempotent relation
`e * (1 - e) = e - e^2 = 0` and cancellation by `(1 - e)`, we get `e = 0`. -/
private lemma _isIdempotentElem_eq_zero_of_mem_jacobson_bot
    {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e)
    (hmem : e ∈ Ideal.jacobson (⊥ : Ideal R)) : e = 0 := by
  rw [Ideal.mem_jacobson_bot] at hmem
  have hu : IsUnit (1 - e) := by
    have := hmem (-1)
    rwa [mul_neg_one, neg_add_eq_sub] at this
  have h_prod : e * (1 - e) = 0 := by
    have hee : e * e = e := he
    rw [mul_sub, mul_one, hee, sub_self]
  obtain ⟨u, hu_eq⟩ := hu
  have hinv : (1 - e) * ((u⁻¹ : Rˣ) : R) = 1 := Units.mul_inv_of_eq hu_eq
  calc e = e * ((1 - e) * ((u⁻¹ : Rˣ) : R)) := by rw [hinv, mul_one]
    _ = e * (1 - e) * ((u⁻¹ : Rˣ) : R) := by ring
    _ = 0 := by rw [h_prod, zero_mul]

/-- **Stacks 0DXB fragment** (Hensel-lifting orthogonal idempotents).

For `A` a henselian local ring and `B` étale over `A`, the orthogonal
idempotents `{Pi.single i 1}_i` of the residue decomposition
`(IsLocalRing.ResidueField A) ⊗_A B ≃ ∀ i, k_i` (from
`Algebra.Etale.iff_exists_algEquiv_prod`) lift to a **true** complete
orthogonal idempotent system in `B`.

The existential bundles the residue decomposition together with the
lifted idempotents, so the consumer can destructure both at once.

The proof goes via Hensel-lifting the polynomial `X² - X` at each
naive lift of `Pi.single i 1`: since `m·B ⊆ Ring.jacobson B` (a
consequence of `A` henselian + `B` étale), the derivative `2·e₀ - 1`
is a unit modulo `m·B` and hence a unit in `B`, so Hensel's lemma
produces the unique idempotent lift `eLift i`. Uniqueness then forces
pairwise orthogonality (`eLift i · eLift j` is a root of `X² - X`
projecting to `0`) and completeness (`Σ_i eLift i` is a root of
`X² - X` projecting to `1`).

Note on the existential's `Fintype` binder: the directive proposing this
helper used `Finite I`, but `CompleteOrthogonalIdempotents` elaborates
its `∑ i, e i` via `Fintype I`. Bundling `Fintype I` directly avoids a
redundant `Fintype.ofFinite` step at every consumer. The two are
equivalent on a non-empty finite index set. -/
theorem exists_completeOrthogonalIdempotents_lift_of_henselian
    (A B : Type u) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B] :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I) (kI : I → Type u)
      (_ : ∀ i, Field (kI i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField A) (kI i))
      (eqv : TensorProduct A (IsLocalRing.ResidueField A) B ≃ₐ[IsLocalRing.ResidueField A]
              ∀ i, kI i)
      (eLift : I → B),
      CompleteOrthogonalIdempotents eLift ∧
      (∀ i,
        eqv ((Algebra.TensorProduct.includeRight : B →ₐ[A] _) (eLift i)) =
          Pi.single i 1) := by
  classical
  -- Step 1 (residue decomposition). The base change `k ⊗_A B` is étale over the
  -- residue field `k := ResidueField A` (via `Algebra.Etale.baseChange`), so the
  -- étale-over-field structure theorem applies and produces a finite index
  -- family `(kI : I → Type u)` of finite separable extensions of `k` together
  -- with an algebra equivalence `eqv : k ⊗_A B ≃ₐ[k] ∀ i, kI i`.
  obtain ⟨I, hIfin, kI, hKfield, hKalg, eqv, _hsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod
      (K := IsLocalRing.ResidueField A)
      (A := TensorProduct A (IsLocalRing.ResidueField A) B)).mp inferInstance
  haveI := hIfin
  haveI : Fintype I := Fintype.ofFinite I
  haveI : DecidableEq I := Classical.decEq I
  refine ⟨I, inferInstance, inferInstance, kI, hKfield, hKalg, eqv, ?_⟩
  -- ===== Setup for the Hensel-lifting argument =====
  -- Notation: `m` is A's maximal ideal, `mB` its extension to `B`.
  set m : Ideal A := IsLocalRing.maximalIdeal A with hm_def
  set mB : Ideal B := m.map (algebraMap A B) with hmB_def
  -- The canonical map `inj : B →ₐ[A] k ⊗_A B`, `b ↦ 1 ⊗ b`, is surjective
  -- because `algebraMap A k = Ideal.Quotient.mk m` is surjective.
  have hinj_surj : Function.Surjective
      (Algebra.TensorProduct.includeRight : B →ₐ[A] _) :=
    Algebra.TensorProduct.includeRight_surjective B
      (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal A))
  -- For each index `i`, pick a naive preimage `e₀ i ∈ B` of the idempotent
  -- `eqv.symm (Pi.single i 1) ∈ k ⊗_A B`.
  -- The `(b : ∀ i, kI i)` annotation forces unification to use the `hKfield`
  -- instance from the existential, avoiding a `Field` typeclass mismatch.
  have hlift_data : ∀ i : I, ∃ b : B,
      (Algebra.TensorProduct.includeRight : B →ₐ[A] _) b =
        eqv.symm ((Pi.single i 1 : ∀ j, kI j)) := by
    intro i
    exact hinj_surj _
  choose e₀ he₀ using hlift_data
  -- ===== Step 2 (residue isomorphism `B/mB ≃+* (A/m) ⊗_A B`). =====
  -- Compose `quotIdealMapEquivTensorQuot B m : B/mB ≃ₐ[B] B ⊗_A (A/m)`
  -- with `Algebra.TensorProduct.comm : B ⊗_A (A/m) ≃ₐ[A] (A/m) ⊗_A B`.
  -- The composite ring iso sends `mk b ↦ 1 ⊗ b = includeRight b`.
  let isoBQ : (B ⧸ mB) ≃+* TensorProduct A (IsLocalRing.ResidueField A) B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        (A := A) B m).toRingEquiv.trans
      (Algebra.TensorProduct.comm A B (IsLocalRing.ResidueField A)).toRingEquiv
  have isoBQ_mk : ∀ b : B, isoBQ (Ideal.Quotient.mk mB b) =
      (Algebra.TensorProduct.includeRight : B →ₐ[A] _) b := fun b => by
    show (Algebra.TensorProduct.comm A B (IsLocalRing.ResidueField A))
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot
          (A := A) B m) (Ideal.Quotient.mk mB b)) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    rfl
  -- ===== Step 3 (residue idempotents `ē_i := mk (e₀ i)` are idempotent in B/mB). =====
  have h_pi_single_idem : ∀ i : I, (Pi.single i (1 : kI i)) *
      (Pi.single i (1 : kI i)) = (Pi.single i (1 : kI i)) := by
    intro i; ext j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  have h_pi_single_mul_zero : ∀ {i j : I}, i ≠ j →
      (Pi.single i (1 : kI i)) * (Pi.single j (1 : kI j)) = 0 := by
    intro i j hij; ext k
    by_cases hik : i = k
    · subst hik; simp [hij]
    · simp [hik]
  have h_pi_single_sum : ∑ i : I, (Pi.single i (1 : kI i)) = 1 := by
    apply Finset.univ_sum_single (fun i : I => (1 : kI i))
  have h_e₀_idem : ∀ i, IsIdempotentElem (Ideal.Quotient.mk mB (e₀ i)) := by
    intro i
    rw [IsIdempotentElem]
    apply isoBQ.injective
    rw [map_mul]
    simp only [isoBQ_mk, he₀]
    rw [← map_mul, h_pi_single_idem]
  -- ===== Step 4 (per-index Hensel lift via `lift_idempotent_henselianPair`). =====
  choose eLift heLift_idem heLift_mk_eq using fun i =>
    Algebra.Etale.lift_idempotent_henselianPair A B
      (Ideal.Quotient.mk mB (e₀ i)) (h_e₀_idem i)
  -- The lift's defining property pushed through `isoBQ` and `includeRight`.
  have eLift_includeRight : ∀ i,
      (Algebra.TensorProduct.includeRight : B →ₐ[A] _) (eLift i) =
        eqv.symm ((Pi.single i 1 : ∀ j, kI j)) := by
    intro i
    have h := isoBQ_mk (eLift i)
    rw [heLift_mk_eq, isoBQ_mk, he₀] at h
    exact h.symm
  -- ===== Step 5 (orthogonality + completeness via Jacobson-idempotent trick). =====
  have h_jacobson : mB ≤ Ideal.jacobson (⊥ : Ideal B) :=
    Algebra.Etale.maximalIdeal_map_le_jacobson_bot A B
  -- For `i ≠ j`, `eLift i * eLift j ∈ mB`; combined with idempotency → 0.
  have h_ortho : ∀ {i j : I}, i ≠ j → eLift i * eLift j = 0 := by
    intro i j hij
    have h_idem : IsIdempotentElem (eLift i * eLift j) :=
      (heLift_idem i).mul (heLift_idem j)
    apply _isIdempotentElem_eq_zero_of_mem_jacobson_bot h_idem
    apply h_jacobson
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, heLift_mk_eq, heLift_mk_eq]
    apply isoBQ.injective
    rw [map_zero, map_mul]
    simp only [isoBQ_mk, he₀]
    rw [← map_mul, h_pi_single_mul_zero hij, map_zero]
  -- `1 - ∑ eLift i ∈ mB` (image in `(A/m) ⊗ B` equals 0), and is idempotent.
  have h_orthIdem : OrthogonalIdempotents eLift :=
    ⟨heLift_idem, fun _ _ hij => h_ortho hij⟩
  have h_sum_idem : IsIdempotentElem (∑ i : I, eLift i) :=
    h_orthIdem.isIdempotentElem_sum
  -- Image of ∑ eLift i in B/mB ≃ (A/m) ⊗ B equals eqv.symm 1 = 1 (in tensor).
  have h_sum_isoBQ : isoBQ (Ideal.Quotient.mk mB (∑ i : I, eLift i)) = 1 := by
    calc isoBQ (Ideal.Quotient.mk mB (∑ i : I, eLift i))
        = ∑ i : I, isoBQ (Ideal.Quotient.mk mB (eLift i)) := by
          rw [map_sum, map_sum]
      _ = ∑ i : I, eqv.symm (Pi.single i (1 : kI i)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [isoBQ_mk]
          exact eLift_includeRight i
      _ = eqv.symm (∑ i : I, Pi.single i (1 : kI i)) := by rw [map_sum]
      _ = eqv.symm 1 := by rw [h_pi_single_sum]
      _ = 1 := map_one _
  have h_mk_sum_eq_one : Ideal.Quotient.mk mB (∑ i : I, eLift i) = 1 := by
    apply isoBQ.injective
    rw [h_sum_isoBQ, map_one]
  have h_one_sub_in_mB : (1 - ∑ i : I, eLift i) ∈ mB := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
      h_mk_sum_eq_one, sub_self]
  have h_complete : ∑ i : I, eLift i = 1 := by
    have h_one_sub_idem : IsIdempotentElem (1 - ∑ i : I, eLift i) :=
      h_sum_idem.one_sub
    have h_zero : 1 - ∑ i : I, eLift i = 0 :=
      _isIdempotentElem_eq_zero_of_mem_jacobson_bot h_one_sub_idem
        (h_jacobson h_one_sub_in_mB)
    linear_combination -h_zero
  refine ⟨eLift, ⟨⟨heLift_idem, fun i j hij => h_ortho hij⟩, h_complete⟩, ?_⟩
  intro i
  rw [eLift_includeRight, AlgEquiv.apply_symm_apply]

end Algebra.Etale
