/-
Copyright (c) 2026 The Proetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Algebra.Pi

/-!
# Localization of a finite product of fields at a single-coordinate element

This file contains the Mathlib-PR-quality helper
`Localization.Away_pi_field_supportedAt`: for a finite product of fields
`∏ i, k i`, localizing away from an element `r` whose support is the singleton
`{i₀}` (i.e. `r i₀ ≠ 0` and `r i = 0` for `i ≠ i₀`) collapses to the single
factor `k i₀`.

This is folklore; the result is needed as the residue-identification ingredient
in `Proetale/Mathlib/RingTheory/Etale/StrictlyHenselian.lean` (§5 Gap A close,
`surjective_standardEtalePair_lift_of_etale`).

## Main result

* `Localization.Away_pi_field_supportedAt`: the canonical `S`-algebra
  isomorphism `Localization.Away r ≃ₐ[S] k i₀` for `r` supported at `i₀`.
-/

open scoped Classical

namespace Localization

variable {S : Type*} [CommRing S]
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (k : I → Type*) [∀ i, Field (k i)] [∀ i, Algebra S (k i)]

/-- For a finite family of fields `k i` (each an `S`-algebra) and an element
`r : ∀ i, k i` supported only at the index `i₀` (so `r i₀ ≠ 0` and `r i = 0`
for `i ≠ i₀`), the localization `(∀ i, k i)[r⁻¹]` is `S`-algebra isomorphic
to the single factor `k i₀`. -/
theorem Away_pi_field_supportedAt
    (i₀ : I) (r : ∀ i, k i) (hr_i₀ : r i₀ ≠ 0)
    (hr_other : ∀ i, i ≠ i₀ → r i = 0) :
    Nonempty (Localization.Away r ≃ₐ[S] k i₀) := by
  -- Step 1: the i₀-projection as an S-algebra hom.
  let π : (∀ i, k i) →ₐ[S] k i₀ := Pi.evalAlgHom S k i₀
  -- Step 2: π r = r i₀ is a nonzero element of the field k i₀, hence a unit.
  have hπr : π r = r i₀ := Pi.evalAlgHom_apply S k i₀ r
  have hunit_πr : IsUnit (π r) := by
    rw [hπr]
    exact (Ne.isUnit hr_i₀)
  -- Step 3: extend π to lift : Localization.Away r →ₐ[S] k i₀.
  have hunit_all :
      ∀ y : Submonoid.powers r, IsUnit (π (y : ∀ i, k i)) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    exact hunit_πr.pow n
  let extn : Localization.Away r →ₐ[S] k i₀ :=
    IsLocalization.liftAlgHom (M := Submonoid.powers r) hunit_all
  -- Step 4a: surjectivity of lift.
  -- The S-algebra map π is already surjective: for any y, Pi.single i₀ y
  -- has i₀-component y. So lift is surjective too.
  have hπ_surj : Function.Surjective π := by
    intro y
    refine ⟨Pi.single i₀ y, ?_⟩
    show Pi.single i₀ y i₀ = y
    exact Pi.single_eq_same i₀ y
  have hlift_surj : Function.Surjective extn := by
    intro y
    obtain ⟨x, hx⟩ := hπ_surj y
    refine ⟨algebraMap _ _ x, ?_⟩
    show extn (algebraMap (∀ i, k i) (Localization.Away r) x) = y
    -- lift ∘ algebraMap = π by the universal property
    have : extn.toRingHom.comp (algebraMap (∀ i, k i) (Localization.Away r))
        = π.toRingHom := by
      ext z
      simp [extn, IsLocalization.lift_eq]
    have hcomp := RingHom.congr_fun this x
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] at hcomp
    rw [hcomp]
    exact hx
  -- Step 4b: injectivity of lift.
  -- Key step: if lift q = 0, write q = mk' x ⟨r^n⟩; then π x = x i₀ = 0,
  -- so the coordinates of r * x are all zero (r i₀ * 0 at i₀, 0 * x i at i ≠ i₀),
  -- hence r * x = 0 in ∀ i, k i; then q = 0 in the localization by
  -- IsLocalization.mk'_eq_zero_iff with witness r.
  have hlift_inj : Function.Injective extn := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    -- Surjectivity of mk' over the powers submonoid.
    obtain ⟨⟨x, s⟩, hxs⟩ :=
      IsLocalization.mk'_surjective (M := Submonoid.powers r) (S := Localization.Away r) q
    rw [← hxs] at hq
    -- Multiply by extn (algebraMap _ _ s) to clear the denominator.
    -- extn (mk' x s) * extn (algebraMap _ _ s) = extn (algebraMap _ _ x) = π x.
    have hmul : extn (IsLocalization.mk' (Localization.Away r) x s) *
        extn (algebraMap (∀ i, k i) (Localization.Away r) (s : ∀ i, k i)) =
        π x := by
      rw [← map_mul, IsLocalization.mk'_spec (Localization.Away r) x s]
      show extn (algebraMap (∀ i, k i) (Localization.Away r) x) = π x
      simp [extn, IsLocalization.lift_eq]
    have hsπ : extn (algebraMap (∀ i, k i) (Localization.Away r) (s : ∀ i, k i)) =
        π (s : ∀ i, k i) := by
      simp [extn, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    rw [hsπ] at hmul
    rw [hq, zero_mul] at hmul
    -- Now π x = 0.
    have hπx : π x = 0 := hmul.symm
    -- π x = x i₀ = 0
    have hx_i₀ : x i₀ = 0 := by
      have : π x = x i₀ := Pi.evalAlgHom_apply S k i₀ x
      rw [this] at hπx
      exact hπx
    -- Show r * x = 0 in ∀ i, k i.
    have hrx_zero : r * x = 0 := by
      funext i
      by_cases h : i = i₀
      · show r i * x i = 0
        rw [h, hx_i₀, mul_zero]
      · show r i * x i = 0
        rw [hr_other i h, zero_mul]
    -- Use mk'_eq_zero_iff with witness r ∈ powers r.
    rw [← hxs]
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨r, ⟨1, by simp⟩⟩, ?_⟩
    show r * x = 0
    exact hrx_zero
  -- Step 5: assemble the AlgEquiv.
  exact ⟨AlgEquiv.ofBijective extn ⟨hlift_inj, hlift_surj⟩⟩

end Localization
