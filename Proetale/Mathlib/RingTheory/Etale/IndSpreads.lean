/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Étale descent along the canonical map `R → Aₘ`

This file states the étale-descent result Stacks 00U6 specialized to `Aₘ = colim Aₛ`,
the filtered colimit of standard-open localizations of a commutative ring `R` at the
multiplicative system `R ∖ m` (`m` a prime ideal of `R`).

## Main statement

`Algebra.Etale.exists_descent_along_localizationAtPrime` :
Given a prime ideal `m` of `R` and an étale `R_m`-algebra `B`, there exists `f ∉ m`
such that `B` arises (as an `R_m`-algebra) by base change from an étale
`Localization.Away f`-algebra `B'`. Formally:
`∃ f ∉ m, ∃ B', Algebra.Etale (Localization.Away f) B' ∧ B ≃ Aₘ ⊗_{A_f} B'`.

## Implementation notes

The proof (TODO) follows Stacks 00U6 in two steps:

1. **FP descent** (the "spreading" step): given `B` finitely presented over
   `Localization.AtPrime m`, lift each polynomial relation's coefficients from
   `Localization.AtPrime m` to `Localization.Away f` for some `f ∉ m` (via
   `IsLocalization.mk'_surjective` + product of denominators). Construct
   `B' = MvPolynomial _ (Localization.Away f) / (lifted relations)`. The product of
   denominators is not in `m` because `m` is prime
   (`Ideal.IsPrime.prod_mem_iff`). Verify the base-change iso
   `B ≃ₐ[A_m] A_m ⊗_{A_f} B'` via the universal property of presentations.

2. **Étaleness** (the "localizing" step): the base-changed algebra `B = A_m ⊗_{A_f} B'`
   is étale over `A_m`. By `Algebra.FormallyEtale.localization_map` applied in
   reverse, `B'` is formally étale at the localization-at-prime above `m`. Since
   `Localization.Away f` is itself finitely presented over `R`, the algebra `B'` is
   finitely presented over `R`, and `Algebra.exists_etale_of_isEtaleAt` (Mathlib)
   applied to the appropriate prime of `B'` yields a further localization
   `Localization.Away (f·g)` over which `B'` is étale. Re-package the conclusion to
   match the desired existential.

Both steps require substantial polynomial / tensor-product manipulation; the full proof
is estimated at 300-500 LOC and is left for future work. The body below is
a `sorry`-placeholder for the central descent statement, used by
`Proetale.Algebra.WStrictLocalization` to give `exists_descent_at_localization` a
clean structural shape.
-/

universe u

open TensorProduct

namespace Algebra.Etale

/-- **Annihilator extraction from a vanishing localization** for a finitely
generated module.

If `M` is a finitely generated `R`-module, `T ⊆ R` is a submonoid, and the
localized module `T⁻¹ M` is subsingleton (i.e. `0`), then there exists a single
element `t ∈ T` whose action annihilates all of `M`.

This is the "uniform" version of `LocalizedModule.subsingleton_iff` for FG
modules. -/
lemma _root_.Module.exists_mem_smul_eq_zero_of_finite_of_subsingleton_localization
    {R : Type*} [CommRing R] {M : Type*} [AddCommMonoid M] [Module R M]
    [Module.Finite R M] (T : Submonoid R)
    [Subsingleton (LocalizedModule T M)] :
    ∃ t : R, t ∈ T ∧ ∀ m : M, t • m = 0 := by
  classical
  -- Pick a finite generating set `s`.
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  -- For each generator `x ∈ s`, `T⁻¹ M = 0` gives `tₓ ∈ T` with `tₓ • x = 0`.
  have hzero : ∀ m : M, ∃ r ∈ T, r • m = 0 :=
    (LocalizedModule.subsingleton_iff (S := T) (R := R) (M := M)).mp inferInstance
  choose t ht ht' using fun x : s ↦ hzero (x : M)
  -- Take the product `∏ x, t x` over the generators.
  refine ⟨s.attach.prod t, T.prod_mem (fun x _ ↦ ht x), fun m ↦ ?_⟩
  -- Every `m ∈ M` is in the span of `s`, so reduce to checking on generators.
  have hm : m ∈ Submodule.span R (s : Set M) := by rw [hs]; exact Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx =>
    have hdvd : t ⟨x, hx⟩ ∣ s.attach.prod t :=
      Finset.dvd_prod_of_mem _ (Finset.mem_attach _ _)
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, mul_comm, mul_smul, ht', smul_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

/-- **Étale descent along `R → R_m`** (Stacks 00U6, specialized to étale).

Given a prime ideal `m` of a commutative ring `R` and an étale algebra `B` over
`Localization.AtPrime m`, there exist `f ∈ R ∖ m` and an étale
`Localization.Away f`-algebra `B'` such that `B` is isomorphic (as an
`Localization.AtPrime m`-algebra) to the base change `Localization.AtPrime m ⊗_{Localization.Away f} B'`.

This is the central étale-descent lemma needed to formalize the blueprint argument
`lemma:retractions-strictly-henselian` for `WStrictLocalization` (Stacks 00U6
applied to the filtered colimit `Localization.AtPrime m = colim_{f ∉ m} Localization.Away f`). -/
lemma exists_descent_along_localizationAtPrime
    {R : Type u} [CommRing R] (m : Ideal R) [m.IsPrime]
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime m) B]
    [Algebra.Etale (Localization.AtPrime m) B] :
    ∃ (f : R) (_hf : f ∉ m) (B' : Type u) (_ : CommRing B')
      (_ : Algebra (Localization.Away f) B')
      (_ : Algebra.Etale (Localization.Away f) B')
      (_ : Algebra (Localization.Away f) (Localization.AtPrime m))
      (_ : Algebra (Localization.Away f) B)
      (_ : IsScalarTower (Localization.Away f) (Localization.AtPrime m) B),
      Nonempty (B ≃ₐ[Localization.AtPrime m]
        TensorProduct (Localization.Away f) (Localization.AtPrime m) B') := by
  classical
  -- ==================================================================
  -- Step 1: B is FP over A_m (from `Algebra.Etale.finitePresentation`).
  -- ==================================================================
  have _hFP : Algebra.FinitePresentation (Localization.AtPrime m) B :=
    Algebra.Etale.finitePresentation
  -- ==================================================================
  -- Step 2: Extract a concrete finite presentation `P` of B over A_m.
  -- ==================================================================
  obtain ⟨n, k, ⟨P⟩⟩ :=
    Algebra.Presentation.exists_presentation_fin (Localization.AtPrime m) B
  -- `P : Algebra.Presentation A_m B (Fin n) (Fin k)`
  -- `P.relation i : MvPolynomial (Fin n) A_m` for each `i : Fin k`.
  -- ==================================================================
  -- Step 3: Collect all coefficients of all relations into a finite set.
  -- ==================================================================
  let coeffs : Finset (Localization.AtPrime m) :=
    (Finset.univ : Finset (Fin k)).biUnion fun i => (P.relation i).coeffs
  -- ==================================================================
  -- Step 4: For each coefficient `c ∈ coeffs`, choose a representation
  -- `c = mk' a s` with numerator `a : R` and denominator `s ∉ m`.
  -- ==================================================================
  have hsurj : ∀ c : Localization.AtPrime m, ∃ as : R × m.primeCompl,
      IsLocalization.mk' (Localization.AtPrime m) as.1 as.2 = c := by
    intro c
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.mk'_surjective m.primeCompl c
    exact ⟨(a, s), h⟩
  choose den hden using hsurj
  -- `den c : R × m.primeCompl`, `hden c : IsLocalization.mk' Am (den c).1 (den c).2 = c`.
  -- ==================================================================
  -- Step 5: Define `f` as the product of all denominators over `coeffs`,
  -- and show `f ∉ m` using primality.
  -- ==================================================================
  let f : R := ∏ c ∈ coeffs, ((den c).2 : R)
  have hf : f ∉ m := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨c, _, hc⟩
    exact (den c).2.2 hc
  -- ==================================================================
  -- Step 6: Set up the algebra map `Localization.Away f → Localization.AtPrime m`.
  -- Since `f ∉ m`, `f` is a unit in `Localization.AtPrime m`, so by the universal
  -- property of `Localization.Away f` we get the required ring hom.
  -- ==================================================================
  have hf_unit : IsUnit (algebraMap R (Localization.AtPrime m) f) :=
    IsLocalization.map_units (Localization.AtPrime m) (⟨f, hf⟩ : m.primeCompl)
  letI algAfAm : Algebra (Localization.Away f) (Localization.AtPrime m) :=
    (IsLocalization.Away.lift f hf_unit).toAlgebra
  have algMap_AfAm : ∀ a : R,
      algebraMap (Localization.Away f) (Localization.AtPrime m)
        (algebraMap R (Localization.Away f) a) = algebraMap R (Localization.AtPrime m) a := by
    intro a
    change IsLocalization.Away.lift f hf_unit _ = _
    rw [IsLocalization.Away.lift_eq]
  -- IsScalarTower R A_f A_m: the composition R → A_f → A_m equals R → A_m.
  haveI istR_Af_Am : IsScalarTower R (Localization.Away f) (Localization.AtPrime m) :=
    IsScalarTower.of_algebraMap_eq fun x => (algMap_AfAm x).symm
  -- Algebra (A_f) B via A_f → A_m → B.
  letI algAfB : Algebra (Localization.Away f) B :=
    ((algebraMap (Localization.AtPrime m) B).comp
      (algebraMap (Localization.Away f) (Localization.AtPrime m))).toAlgebra
  haveI istAf_Am_B : IsScalarTower (Localization.Away f) (Localization.AtPrime m) B :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- ==================================================================
  -- Step 7: Show that each coefficient `c ∈ P.coeffs` is in the image of
  -- `algebraMap A_f A_m`. The denominator `(den c).2 ∣ f`, so it is a unit
  -- in A_f. Since `(den c).2 ∣ f`, write `f = (den c).2 * g` and use
  -- `IsLocalization.mk' (Localization.Away f) ((den c).1 * g) ⟨f, _⟩`.
  -- ==================================================================
  have hcoeffs_in_image : ∀ i : Fin k, ∀ c ∈ (P.relation i).coeffs,
      c ∈ Set.range (algebraMap (Localization.Away f) (Localization.AtPrime m)) := by
    intro i c hci
    have hc_mem : c ∈ coeffs := by
      simp only [coeffs, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, hci⟩
    have hdvd : ((den c).2 : R) ∣ f :=
      Finset.dvd_prod_of_mem _ hc_mem
    -- algebraMap R A_f (den c).2 is a unit in A_f.
    have h2u : IsUnit (algebraMap R (Localization.Away f) ((den c).2 : R)) :=
      IsLocalization.Away.isUnit_of_dvd f hdvd
    -- Define y := (den c).1 * ((den c).2)⁻¹ in A_f.
    refine ⟨algebraMap R (Localization.Away f) (den c).1 *
              ((h2u.unit)⁻¹ : (Localization.Away f)ˣ).val, ?_⟩
    -- Verify image equals c using IsLocalization.eq_mk'_iff_mul_eq.
    have key : algebraMap (Localization.Away f) (Localization.AtPrime m)
          (algebraMap R (Localization.Away f) (den c).1 *
            ((h2u.unit)⁻¹ : (Localization.Away f)ˣ).val) *
        algebraMap R (Localization.AtPrime m) (den c).2 =
        algebraMap R (Localization.AtPrime m) (den c).1 := by
      rw [map_mul, mul_assoc, ← algMap_AfAm ((den c).2 : R)]
      have hu_inv : ((h2u.unit)⁻¹ : (Localization.Away f)ˣ).val *
          algebraMap R (Localization.Away f) (den c).2 = 1 :=
        h2u.val_inv_mul
      rw [← map_mul, hu_inv, map_one, mul_one, algMap_AfAm]
    exact (IsLocalization.eq_mk'_iff_mul_eq.mpr key).trans (hden c)
  -- ==================================================================
  -- Step 8: P satisfies `HasCoeffs (Localization.Away f)`.
  -- ==================================================================
  haveI hasCoeffs : P.HasCoeffs (Localization.Away f) := by
    refine ⟨?_⟩
    intro c hc
    simp only [Algebra.Presentation.coeffs, Set.mem_iUnion] at hc
    obtain ⟨i, hci⟩ := hc
    exact hcoeffs_in_image i c hci
  -- ==================================================================
  -- Step 9: Set `B' := P.ModelOfHasCoeffs (Localization.Away f)` and use
  -- `tensorModelOfHasCoeffsEquiv` to get the iso `A_m ⊗[A_f] B' ≃ₐ[A_m] B`.
  -- ==================================================================
  let B' : Type u := P.ModelOfHasCoeffs (Localization.Away f)
  let eq_iso : Localization.AtPrime m ⊗[Localization.Away f] B' ≃ₐ[Localization.AtPrime m] B :=
    P.tensorModelOfHasCoeffsEquiv (Localization.Away f)
  -- ==================================================================
  -- Step 10: Étaleness. `B'` is FP over `A_f` (automatic from
  -- `Algebra.Presentation.HasCoeffs`). However `B'` is **not** in general
  -- étale over `A_f` — only at the primes of `B'` lying above the image
  -- of `m` in `A_f`. We must therefore localize further on the base.
  --
  -- Strategy (Stacks 00U6, étaleness step, corrected from the original
  -- "g₀-not-in-Q" route which is only valid locally at one prime):
  --
  --   (a) Let `T ⊆ B'` denote the image of `R \ m` under
  --       `R → A_f → B'`. The composite localization
  --       `B = A_m ⊗_{A_f} B' = T^{-1} B'` (since `A_m = (R\m)^{-1} R`,
  --       and tensor-product-with-localization is localization).
  --   (b) `B` is étale over `A_m`, so
  --       `Ω[B/A_m] = T^{-1} Ω[B'/A_f] = 0` and
  --       `H^1_cot(A_m, B) = T^{-1} H^1_cot(A_f, B') = 0`.
  --   (c) `Ω[B'/A_f]` is FG over `B'` (FP ⇒ EssFiniteType ⇒
  --       `KaehlerDifferential.finite`). By
  --       `LocalizedModule.subsingleton_iff` applied to finitely many
  --       generators, ∃ `t₁ ∈ T` with `t₁ · Ω[B'/A_f] = 0`.
  --   (d) Localize at `t₁`: in `B'_{t₁} = B'[1/t₁]`,
  --       `Ω[B'_{t₁}/A_f] = 0` is now Projective, so
  --       `H^1_cot(A_f, B'_{t₁})` is FG. Apply the same argument:
  --       ∃ `t₂ ∈ T` with `t₂ · H^1_cot(A_f, B'_{t₁}) = 0`.
  --   (e) Set `s := t₁ * t₂ ∈ T`. Then `s = image-in-B'` of some
  --       `r ∈ R \ m` (since `T` is the image of `m.primeCompl`, a
  --       multiplicative system). In `B'_s = B'[1/s]`:
  --       `Ω = 0` and `H^1_cot = 0`, so `FormallyEtale A_f (B'_s)`,
  --       and FP base-changes to FP, hence `Etale A_f (B'_s)`.
  --   (f) Repackage with new base `A_{f * r}` and new model `B'_s`:
  --       - `A_{f * r} = Loc.Away (f * r) over R = Loc.Away r over A_f`.
  --       - `B'_s = A_{f*r} ⊗_{A_f} B'` (base-change identification).
  --       - `Etale A_{f*r} B'_s` via `FormallyEtale.localization_base`
  --         + base-change FP.
  --       - Descent iso:
  --         `A_m ⊗_{A_{f*r}} B'_s = A_m ⊗_{A_{f*r}} (A_{f*r} ⊗_{A_f} B')
  --                              = A_m ⊗_{A_f} B' ≃ B`.
  --
  -- Verified Mathlib infrastructure (no sorry in any of these):
  --   * `Algebra.basicOpen_subset_etaleLocus_iff_etale`
  --   * `Algebra.FormallyEtale.localization_base`
  --   * `KaehlerDifferential.finite`
  --   * `LocalizedModule.subsingleton_iff`
  --   * `IsLocalization.Away.mul'` / `IsLocalization.Away.of_associated`
  --
  -- The remaining sorry below stands for the full execution of (a)–(f).
  -- The blocker is purely technical (composition of localization /
  -- tensor identifications + handling the H^1_cot finiteness via the
  -- two-stage localization). The strategy is now mathematically sound;
  -- previous attempts via `exists_etale_of_isEtaleAt` directly fail in
  -- step (e) because `g₀ ∈ B'` (an arbitrary element) need not lift to
  -- `R`, breaking the descent iso.
  -- ==================================================================
  refine ⟨f, hf, B', inferInstance, inferInstance, ?_, algAfAm, algAfB, istAf_Am_B,
    ⟨eq_iso.symm⟩⟩
  -- Goal: `Algebra.Etale (Localization.Away f) B'`.
  -- NOTE: This goal is **not** provable as-stated for the current `f, B'`
  -- (we only have étaleness after further localization). The lemma
  -- statement allows existential choice of `(f, B')`, so the actual fix
  -- is to undo the above `refine` and produce a new witness
  -- `(f * r, Loc.Away (image r in B'), …)` instead. The remaining work
  -- is to carry out steps (a)–(f) above.
  sorry

end Algebra.Etale
