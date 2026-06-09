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

/-- **Étale base-change along `R → R[1/f]`** (lightweight helper for
the étale-localization step of `exists_descent_along_localizationAtPrime`).

If `B` is an étale `R`-algebra, then for any `f : R`, the base change
`Localization.Away f ⊗[R] B` is étale over `Localization.Away f`. This
is the specialization of `Algebra.Etale.baseChange` to the canonical map
`R → Localization.Away f` and is the most lightweight sub-claim of step
(a) in the strategy for `exists_descent_along_localizationAtPrime`. -/
private lemma baseChange_localization_away
    {R : Type u} [CommRing R] (B : Type u) [CommRing B] [Algebra R B]
    [Algebra.Etale R B] (f : R) :
    Algebra.Etale (Localization.Away f)
      (TensorProduct R (Localization.Away f) B) :=
  Algebra.Etale.baseChange R B (Localization.Away f)

/-- **`B[1/f]` is étale over `R` from a basic-open containment of the étale locus**.

If `B` is a finitely-presented `R`-algebra and the basic open `D(f) ⊆ Spec B`
is contained in the étale locus of `B/R`, then `Localization.Away f` is étale
over `R`. This is a thin wrapper around
`Algebra.basicOpen_subset_etaleLocus_iff_etale` providing the `mp` direction
in named form, matching the calling convention of step (e) of the strategy
for `exists_descent_along_localizationAtPrime`. -/
private lemma of_basicOpen_subset_etaleLocus
    {R : Type u} [CommRing R] {B : Type u} [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] {f : B}
    (hf : ↑(PrimeSpectrum.basicOpen f) ⊆ Algebra.etaleLocus R B) :
    Algebra.Etale R (Localization.Away f) :=
  Algebra.basicOpen_subset_etaleLocus_iff_etale.mp hf

/-- **From-T-vanishing-to-r-annihilator helper for sub-step (c).**

Given a finite `B'`-module `M`, an `R`-algebra structure on `B'`, a prime ideal
`m ⊆ R`, and the hypothesis that the localization of `M` at the image of
`m.primeCompl ⊆ R` (under `algebraMap R B'`) is zero, there exists
`r ∈ m.primeCompl` whose image in `B'` annihilates all of `M`.

This isolates the "from-T-vanishing-to-r-annihilator" content of the
two-stage localization in the étaleness step of
`exists_descent_along_localizationAtPrime`, factoring it out as a reusable
Mathlib-level lemma. -/
private lemma exists_annihilator_in_R_complement_of_finite_localized
    {R : Type u} [CommRing R] (m : Ideal R) [m.IsPrime]
    {B' : Type u} [CommRing B'] [Algebra R B']
    (M : Type u) [AddCommGroup M] [Module B' M] [Module.Finite B' M]
    [Subsingleton
      (LocalizedModule (m.primeCompl.map (algebraMap R B')) M)] :
    ∃ r ∈ m.primeCompl, ∀ x : M, (algebraMap R B' r) • x = 0 := by
  obtain ⟨t, htT, ht⟩ :=
    Module.exists_mem_smul_eq_zero_of_finite_of_subsingleton_localization
      (R := B') (M := M) (m.primeCompl.map (algebraMap R B'))
  obtain ⟨r, hr_mem, hr_eq⟩ := Submonoid.mem_map.mp htT
  refine ⟨r, hr_mem, fun x => ?_⟩
  rw [hr_eq]
  exact ht x

/-- **Find `r ∈ m.primeCompl` with `D(algMap R B' r) ⊆ etaleLocus`**.

Given a presentation `B'` over `Localization.Away f` and an étale algebra `B`
over `Localization.AtPrime m` with an `A_m`-iso between `B` and `A_m ⊗ B'`,
there exists `r ∈ m.primeCompl` such that the basic open `D(algMap R B' r)`
in `Spec B'` is contained in the étale locus of `B'` over `Loc.Away f`.

This is the heart of step (b) of the strategy for
`exists_descent_along_localizationAtPrime`: the annihilator chain argument
applied to `Ω[B'/A_f]` and `H¹Cot(A_f, B'[1/s₁])`. -/
private lemma exists_basicOpen_subset_etaleLocus_of_descent
    {R : Type u} [CommRing R] (m : Ideal R) [m.IsPrime]
    {f : R} (hf : f ∉ m)
    {B' : Type u} [CommRing B'] [Algebra (Localization.Away f) B']
    [Algebra.FinitePresentation (Localization.Away f) B']
    [Algebra R B'] [IsScalarTower R (Localization.Away f) B']
    [Algebra (Localization.Away f) (Localization.AtPrime m)]
    [IsScalarTower R (Localization.Away f) (Localization.AtPrime m)]
    {B : Type u} [CommRing B] [Algebra (Localization.AtPrime m) B]
    [Algebra.Etale (Localization.AtPrime m) B]
    (eq_iso : (Localization.AtPrime m) ⊗[Localization.Away f] B'
      ≃ₐ[Localization.AtPrime m] B) :
    ∃ r ∈ m.primeCompl,
      ↑(PrimeSpectrum.basicOpen (algebraMap R B' r)) ⊆
        Algebra.etaleLocus (Localization.Away f) B' := by
  -- Step (a): A_m as a localization of A_f at the image of m.primeCompl.
  have hpc_pow : Submonoid.powers f ≤ m.primeCompl := Submonoid.powers_le.mpr hf
  haveI hAmLocAf : IsLocalization
      (m.primeCompl.map (algebraMap R (Localization.Away f)))
      (Localization.AtPrime m) :=
    IsLocalization.isLocalization_of_submonoid_le
      (Localization.Away f) (Localization.AtPrime m)
      (Submonoid.powers f) m.primeCompl hpc_pow
  -- Step (b): FormallyEtale chain A_f → A_m → B.
  haveI hFEAfAm : Algebra.FormallyEtale (Localization.Away f) (Localization.AtPrime m) :=
    Algebra.FormallyEtale.of_isLocalization
      (m.primeCompl.map (algebraMap R (Localization.Away f)))
  -- Transport FormallyEtale across eq_iso (over A_m), then compose with A_f → A_m.
  haveI hFEAmTens : Algebra.FormallyEtale (Localization.AtPrime m)
      ((Localization.AtPrime m) ⊗[Localization.Away f] B') :=
    Algebra.FormallyEtale.of_equiv eq_iso.symm
  haveI hFEAfTens : Algebra.FormallyEtale (Localization.Away f)
      ((Localization.AtPrime m) ⊗[Localization.Away f] B') :=
    Algebra.FormallyEtale.comp (Localization.Away f) (Localization.AtPrime m)
      ((Localization.AtPrime m) ⊗[Localization.Away f] B')
  -- Hence Ω[(A_m ⊗ B')/A_f] is subsingleton.
  haveI hOmTensSub : Subsingleton (Ω[((Localization.AtPrime m) ⊗[Localization.Away f] B')⁄
      (Localization.Away f)]) :=
    hFEAfTens.subsingleton_kaehlerDifferential
  -- Step (c): IsLocalization on the tensor product via tensorRight,
  -- and IsLocalizedModule for the Kähler map.
  letI algB'Tens : Algebra B'
      ((Localization.AtPrime m) ⊗[Localization.Away f] B') :=
    Algebra.TensorProduct.rightAlgebra
  haveI hTensLoc : IsLocalization
      (Algebra.algebraMapSubmonoid B'
        (m.primeCompl.map (algebraMap R (Localization.Away f))))
      ((Localization.AtPrime m) ⊗[Localization.Away f] B') :=
    IsLocalization.tensorRight (A := Localization.AtPrime m)
      (m.primeCompl.map (algebraMap R (Localization.Away f)))
  -- The submonoid simplifies to `m.primeCompl.map (algMap R B')`.
  have hsub_eq : Algebra.algebraMapSubmonoid B'
      (m.primeCompl.map (algebraMap R (Localization.Away f))) =
        m.primeCompl.map (algebraMap R B') := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, (IsScalarTower.algebraMap_apply R (Localization.Away f) B' r)⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨algebraMap R (Localization.Away f) r, ⟨r, hr, rfl⟩,
        (IsScalarTower.algebraMap_apply R (Localization.Away f) B' r).symm⟩
  haveI hOmFin : Module.Finite B' (Ω[B'⁄(Localization.Away f)]) :=
    KaehlerDifferential.finite (Localization.Away f) B'
  -- Subsingleton (LocalizedModule (algMapSub B' M) Ω[B'/A_f]) via the iso.
  haveI hOmSub : Subsingleton (LocalizedModule
      (Algebra.algebraMapSubmonoid B'
        (m.primeCompl.map (algebraMap R (Localization.Away f))))
      (Ω[B'⁄(Localization.Away f)])) :=
    (IsLocalizedModule.iso
        (Algebra.algebraMapSubmonoid B'
          (m.primeCompl.map (algebraMap R (Localization.Away f))))
        (KaehlerDifferential.map (Localization.Away f) (Localization.Away f) B'
          ((Localization.AtPrime m) ⊗[Localization.Away f] B'))).toEquiv.subsingleton_congr.mpr
      hOmTensSub
  -- Rewrite the submonoid.
  rw [hsub_eq] at hOmSub
  -- Apply annihilator extraction to get r₁ ∈ m.primeCompl with
  -- (algMap R B' r₁) · Ω[B'/A_f] = 0.
  obtain ⟨r₁, hr₁_mem, hr₁_ann⟩ := exists_annihilator_in_R_complement_of_finite_localized
    (R := R) m (B' := B') (Ω[B'⁄(Localization.Away f)])
  -- ===========================================================
  -- Step (d): Localize at s₁ := algMap R B' r₁ to get B'_1, then
  -- find r₂ ∈ m.primeCompl annihilating H¹Cot(A_f, B'_1).
  -- ===========================================================
  set s₁ : B' := algebraMap R B' r₁ with hs₁
  let B'_1 : Type u := Localization.Away s₁
  -- B'_1 is FP over Loc.Away f (composition of FPs).
  haveI hFPB'1 : Algebra.FinitePresentation (Localization.Away f) B'_1 :=
    Algebra.FinitePresentation.trans (Localization.Away f) B' B'_1
  -- Ω[B'_1/A_f] is subsingleton (s₁ annihilates Ω[B'/A_f] localizes to 0).
  haveI hOmLocS1Sub : Subsingleton
      (LocalizedModule (Submonoid.powers s₁) (Ω[B'⁄(Localization.Away f)])) := by
    rw [LocalizedModule.subsingleton_iff]
    intro x
    exact ⟨s₁, Submonoid.mem_powers s₁, hr₁_ann x⟩
  haveI hOmB'1Sub : Subsingleton (Ω[B'_1⁄(Localization.Away f)]) :=
    (IsLocalizedModule.iso (Submonoid.powers s₁)
      (KaehlerDifferential.map (Localization.Away f) (Localization.Away f) B'
        B'_1)).symm.toEquiv.subsingleton_congr.mpr hOmLocS1Sub
  -- Ω = 0 ⇒ free via subsingleton, hence projective, hence H¹Cot finite over B'_1.
  haveI hH1Fin : Module.Finite B'_1 (Algebra.H1Cotangent (Localization.Away f) B'_1) :=
    inferInstance
  -- Establish `Algebra B'_1 (A_m ⊗ B')` and the IsScalarTower via `IsLocalization.Away.lift`.
  have h_s1_in_M : s₁ ∈ Algebra.algebraMapSubmonoid B'
      (m.primeCompl.map (algebraMap R (Localization.Away f))) := by
    rw [hsub_eq]; exact ⟨r₁, hr₁_mem, rfl⟩
  have h_s1_unit : IsUnit (algebraMap B'
      ((Localization.AtPrime m) ⊗[Localization.Away f] B') s₁) :=
    IsLocalization.map_units _ ⟨s₁, h_s1_in_M⟩
  letI algB'_1Tens : Algebra B'_1
      ((Localization.AtPrime m) ⊗[Localization.Away f] B') :=
    (IsLocalization.Away.lift s₁ h_s1_unit
      (S := B'_1)
      (P := (Localization.AtPrime m) ⊗[Localization.Away f] B')).toAlgebra
  haveI istB'_to_B'_1 : IsScalarTower B' B'_1
      ((Localization.AtPrime m) ⊗[Localization.Away f] B') := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show algebraMap B' _ x =
      (IsLocalization.Away.lift s₁ h_s1_unit (S := B'_1)) (algebraMap B' B'_1 x)
    rw [IsLocalization.Away.lift_eq]
  haveI istAfB'_1Tens : IsScalarTower (Localization.Away f) B'_1
      ((Localization.AtPrime m) ⊗[Localization.Away f] B') := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [IsScalarTower.algebraMap_apply (Localization.Away f) B' B'_1,
        ← IsScalarTower.algebraMap_apply B' B'_1
          ((Localization.AtPrime m) ⊗[Localization.Away f] B'),
        ← IsScalarTower.algebraMap_apply (Localization.Away f) B'
          ((Localization.AtPrime m) ⊗[Localization.Away f] B')]
  -- IsLocalization (m.primeCompl.map (algMap R B'_1)) (A_m ⊗ B') via submonoid_le.
  have hPwS1Le : Submonoid.powers s₁ ≤ Algebra.algebraMapSubmonoid B'
      (m.primeCompl.map (algebraMap R (Localization.Away f))) := by
    rw [Submonoid.powers_le]; exact h_s1_in_M
  haveI hImgLoc : IsLocalization
      (Submonoid.map (algebraMap B' B'_1) (Algebra.algebraMapSubmonoid B'
        (m.primeCompl.map (algebraMap R (Localization.Away f)))))
      ((Localization.AtPrime m) ⊗[Localization.Away f] B') :=
    IsLocalization.isLocalization_of_submonoid_le
      B'_1 ((Localization.AtPrime m) ⊗[Localization.Away f] B')
      (Submonoid.powers s₁)
      (Algebra.algebraMapSubmonoid B' (m.primeCompl.map (algebraMap R (Localization.Away f))))
      hPwS1Le
  -- Identify the submonoid image with m.primeCompl.map (algMap R B'_1).
  have hImgEq : Submonoid.map (algebraMap B' B'_1) (Algebra.algebraMapSubmonoid B'
      (m.primeCompl.map (algebraMap R (Localization.Away f)))) =
        m.primeCompl.map (algebraMap R B'_1) := by
    rw [hsub_eq]
    ext y
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, (IsScalarTower.algebraMap_apply R B' B'_1 r).symm⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨algebraMap R B' r, ⟨r, hr, rfl⟩, (IsScalarTower.algebraMap_apply R B' B'_1 r)⟩
  rw [hImgEq] at hImgLoc
  -- Subsingleton H¹Cot(A_f, A_m ⊗ B') (from FormallyEtale).
  haveI hH1AmTensSub : Subsingleton (Algebra.H1Cotangent (Localization.Away f)
      ((Localization.AtPrime m) ⊗[Localization.Away f] B')) :=
    hFEAfTens.subsingleton_h1Cotangent
  -- Subsingleton (LocalizedModule (m.primeCompl.map (algMap R B'_1)) (H¹Cot(_, B'_1))).
  haveI hH1B'1LocSub : Subsingleton (LocalizedModule (m.primeCompl.map (algebraMap R B'_1))
      (Algebra.H1Cotangent (Localization.Away f) B'_1)) :=
    (IsLocalizedModule.iso (m.primeCompl.map (algebraMap R B'_1))
      (Algebra.H1Cotangent.map (Localization.Away f) (Localization.Away f) B'_1
        ((Localization.AtPrime m) ⊗[Localization.Away f] B'))).toEquiv.subsingleton_congr.mpr
      hH1AmTensSub
  -- Apply annihilator extraction to get r₂.
  obtain ⟨r₂, hr₂_mem, hr₂_ann⟩ := exists_annihilator_in_R_complement_of_finite_localized
    (R := R) m (B' := B'_1) (Algebra.H1Cotangent (Localization.Away f) B'_1)
  -- ===========================================================
  -- Step (e): Set r := r₁ * r₂. Show D(algMap R B' r) ⊆ etaleLocus.
  -- ===========================================================
  refine ⟨r₁ * r₂, m.primeCompl.mul_mem hr₁_mem hr₂_mem, ?_⟩
  rw [Algebra.basicOpen_subset_etaleLocus_iff, Algebra.formallyEtale_iff]
  set s : B' := algebraMap R B' (r₁ * r₂) with hs
  refine ⟨?_, ?_⟩
  · -- Subsingleton Ω[(Loc.Away s)/(Loc.Away f)].
    have hSAnn : ∀ x : Ω[B'⁄(Localization.Away f)], s • x = 0 := by
      intro x
      have heq : s = s₁ * algebraMap R B' r₂ := by simp [s, hs₁, map_mul]
      rw [heq, mul_smul, hr₁_ann]
    have hLocSub : Subsingleton
        (LocalizedModule (Submonoid.powers s) (Ω[B'⁄(Localization.Away f)])) := by
      rw [LocalizedModule.subsingleton_iff]
      intro x
      exact ⟨s, Submonoid.mem_powers s, hSAnn x⟩
    exact (IsLocalizedModule.iso (Submonoid.powers s)
      (KaehlerDifferential.map (Localization.Away f) (Localization.Away f) B'
        (Localization.Away s))).symm.toEquiv.subsingleton_congr.mpr hLocSub
  · -- Subsingleton H¹Cot(Loc.Away f, Loc.Away s).
    -- Strategy: view `Loc.Away s` as a localization of `B'_1` at powers of
    -- `algMap R B'_1 r₂`, then apply `H1Cotangent.isLocalizedModule` to identify
    -- `H¹Cot(_, Loc.Away s)` with a localization of `H¹Cot(_, B'_1)` at the
    -- same powers, which vanishes by `hr₂_ann`.
    --
    -- Building the `IsLocalization (powers (algMap B' B'_1 t)) (Loc.Away s)`
    -- instance over `B'_1` goes through the auxiliary type
    -- `X := Localization.Away (algMap B' B'_1 t)`: `X` already carries that
    -- instance canonically, and `Loc.Away s ≃ₐ[B'_1] X` because both are
    -- localizations of `B'` at `powers s = powers (s₁ * t)`.
    set t : B' := algebraMap R B' r₂ with ht
    have hs_eq : s = s₁ * t := by
      show algebraMap R B' (r₁ * r₂) = algebraMap R B' r₁ * algebraMap R B' r₂
      exact map_mul _ _ _
    -- Algebra `B'_1 → Loc.Away s` via lifting the `s₁`-unit witness.
    have hs₁_dvd : s₁ ∣ s := ⟨t, hs_eq⟩
    have hs₁_unit_locs : IsUnit (algebraMap B' (Localization.Away s) s₁) :=
      IsLocalization.Away.isUnit_of_dvd s hs₁_dvd
    letI algB'_1Locs : Algebra B'_1 (Localization.Away s) :=
      (IsLocalization.Away.lift s₁ hs₁_unit_locs
        (S := B'_1) (P := Localization.Away s)).toAlgebra
    haveI istB'_to_B'_1_Locs : IsScalarTower B' B'_1 (Localization.Away s) := by
      refine IsScalarTower.of_algebraMap_eq fun x => ?_
      show algebraMap B' _ x =
        (IsLocalization.Away.lift s₁ hs₁_unit_locs (S := B'_1)) (algebraMap B' B'_1 x)
      rw [IsLocalization.Away.lift_eq]
    haveI istAfLocs : IsScalarTower (Localization.Away f) B'_1 (Localization.Away s) := by
      refine IsScalarTower.of_algebraMap_eq fun x => ?_
      rw [IsScalarTower.algebraMap_apply (Localization.Away f) B' B'_1,
          ← IsScalarTower.algebraMap_apply B' B'_1 (Localization.Away s),
          ← IsScalarTower.algebraMap_apply (Localization.Away f) B' (Localization.Away s)]
    -- Auxiliary X = Loc.Away (algMap B' B'_1 t). Canonical instances:
    --  * `IsLocalization.Away (algMap B' B'_1 t) X` over `B'_1`
    --  * `IsLocalization.Away (s₁ * t) X` over `B'` (via the mathlib instance).
    let X : Type u := Localization.Away (algebraMap B' B'_1 t)
    -- Transport the second to `IsLocalization (powers s) X` over `B'` via `hs_eq`.
    haveI hXLocPowS : IsLocalization (Submonoid.powers s) X := by
      rw [show (Submonoid.powers s : Submonoid B') = Submonoid.powers (s₁ * t) by
            rw [hs_eq]]
      infer_instance
    -- B'-algebra equiv between `Loc.Away s` and `X` (both at `powers s`).
    let φ_B' : Localization.Away s ≃ₐ[B'] X :=
      IsLocalization.algEquiv (Submonoid.powers s) _ _
    -- Promote to a B'_1-algebra equiv. The commutes' property reduces, via
    -- uniqueness of localization homs at `powers s₁`, to the B' commutes
    -- already given by `φ_B'`.
    let φ : Localization.Away s ≃ₐ[B'_1] X :=
      { φ_B'.toRingEquiv with
        commutes' := fun b => by
          have key : (φ_B'.toRingEquiv : Localization.Away s →+* X).comp
              (algebraMap B'_1 (Localization.Away s)) = algebraMap B'_1 X := by
            apply IsLocalization.ringHom_ext (M := Submonoid.powers s₁)
            ext x
            show φ_B' (algebraMap B'_1 (Localization.Away s) (algebraMap B' B'_1 x)) =
                algebraMap B'_1 X (algebraMap B' B'_1 x)
            rw [← IsScalarTower.algebraMap_apply B' B'_1 (Localization.Away s),
                ← IsScalarTower.algebraMap_apply B' B'_1 X]
            exact φ_B'.commutes x
          exact RingHom.congr_fun key b }
    -- Transfer the `IsLocalization` instance from X to Loc.Away s over B'_1.
    haveI hLocs_locsAt_t : IsLocalization
        (Submonoid.powers (algebraMap B' B'_1 t)) (Localization.Away s) :=
      IsLocalization.isLocalization_of_algEquiv
        (Submonoid.powers (algebraMap B' B'_1 t)) φ.symm
    -- The LocalizedModule of `H¹Cot(_, B'_1)` at `powers (algMap B' B'_1 t)`
    -- is subsingleton, because `algMap B' B'_1 t = algMap R B'_1 r₂` annihilates
    -- `H¹Cot(_, B'_1)` by `hr₂_ann`.
    have hLocSub : Subsingleton (LocalizedModule
        (Submonoid.powers (algebraMap B' B'_1 t))
        (Algebra.H1Cotangent (Localization.Away f) B'_1)) := by
      rw [LocalizedModule.subsingleton_iff]
      intro x
      refine ⟨algebraMap B' B'_1 t, Submonoid.mem_powers _, ?_⟩
      rw [show algebraMap B' B'_1 t = algebraMap R B'_1 r₂ from
        (IsScalarTower.algebraMap_apply R B' B'_1 r₂).symm]
      exact hr₂_ann x
    -- Conclude via `H1Cotangent.isLocalizedModule` on `B'_1 → Loc.Away s`.
    exact (IsLocalizedModule.iso (Submonoid.powers (algebraMap B' B'_1 t))
      (Algebra.H1Cotangent.map (Localization.Away f) (Localization.Away f) B'_1
        (Localization.Away s))).toEquiv.subsingleton_congr.mp hLocSub

/-- **Étale descent along `R → R_m`** (Stacks 00U6, specialized to étale).

Given a prime ideal `m` of a commutative ring `R` and an étale algebra `B` over
`Localization.AtPrime m`, there exist `f ∈ R ∖ m` and an étale
`Localization.Away f`-algebra `B'` such that `B` is isomorphic (as an
`Localization.AtPrime m`-algebra) to the base change `Localization.AtPrime m ⊗_{Localization.Away f} B'`.

The existential also exposes the canonical `IsScalarTower R (Localization.Away f)
(Localization.AtPrime m)` instance witnessing that the produced
`Localization.Away f → Localization.AtPrime m` map factors `R → Localization.AtPrime m`.

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
      (_ : IsScalarTower R (Localization.Away f) (Localization.AtPrime m))
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
  -- ==================================================================
  -- Step 10–16 (round 25 refactor — keep `f`, replace `B'` by `B' [1/s]`).
  -- The original `(f, B')` witness is not étale: `B'` is étale over `A_f`
  -- only after a further localization. We do NOT need to enlarge `f` to
  -- `f * r`; instead we replace the model `B'` by `Localization.Away s`
  -- where `s = algebraMap R B' r` for some `r ∈ R \ m`. The basic open
  -- `D(s) ⊆ Spec B'` will be shown to lie inside the étale locus
  -- `etaleLocus (A_f) B'`, hence `Loc.Away s` is étale over `A_f`
  -- (`basicOpen_subset_etaleLocus_iff_etale`). The descent iso
  -- `B ≃ₐ[A_m] A_m ⊗_{A_f} (Loc.Away s)` follows because `image r` is a
  -- unit in `B` (since `r ∉ m` and `A_m → B` makes `r` a unit), so
  -- `A_m ⊗_{A_f} (Loc.Away s) ≃ Loc(B, image s) ≃ B`.
  -- ==================================================================
  -- Step 10: identify `B` as the localization of `B'` at the image of
  -- `m.primeCompl` (via `R → A_f → B'`). This is the consequence of
  -- `eq_iso : A_m ⊗_{A_f} B' ≃ₐ[A_m] B` combined with the fact that
  -- `A_m` is a localization of `R` at `m.primeCompl` (which sends `f`
  -- to a unit, hence factors through `A_f`).
  let T : Submonoid B' := (m.primeCompl).map (algebraMap R B')
  -- Step 11: produce `r ∈ R \ m` such that the basic open
  -- `D(algebraMap R B' r) ⊆ Spec B'` is contained in the étale locus
  -- of `B'` over `A_f`.
  --
  -- Mathematical justification (per strategy (a)–(f) above): the étale
  -- locus is the complement of `Module.support B' Ω[B'/A_f]` intersected
  -- with the complement of `Module.support B' H¹Cot(A_f, B')`
  -- (Mathlib's `Algebra.etaleLocus_eq_compl_support`). Both `Ω[B'/A_f]`
  -- and `H¹Cot(A_f, B')` localize to `0` along `T = image (m.primeCompl)`
  -- because the base change is `B`, which is étale over `A_m`. Both
  -- modules are finitely generated over `B'` (Ω by `KaehlerDifferential.finite`;
  -- H¹Cot by `instFiniteH1Cotangent...` after the Ω-vanishing step makes
  -- Ω projective). Applying `exists_annihilator_in_R_complement_of_finite_localized`
  -- to each yields `r₁, r₂ ∈ R \ m`. The product `r := r₁ * r₂` then
  -- satisfies `algebraMap R B' r ∈ Module.annihilator B' Ω ∩
  -- Module.annihilator B' H¹Cot`, so `D(s) ⊆ etaleLocus`. The full
  -- assembly of this annihilator chain is left as a scoped sorry; the
  -- structural refactor of the outer `refine` is the round-25 content.
  -- Available instances for the annihilator chain (future agents):
  --   `Algebra.FinitePresentation (Localization.Away f) B'` — automatic from
  --     `ModelOfHasCoeffs` (already used to instantiate `inferInstance` above).
  --   `Algebra.EssFiniteType (Localization.Away f) B'` — derived from FP.
  --   `Module.Finite B' (KaehlerDifferential (Localization.Away f) B')` —
  --     via `KaehlerDifferential.finite`.
  --   `IsLocalization (Algebra.algebraMapSubmonoid B' (Algebra.algebraMapSubmonoid (Localization.Away f) m.primeCompl)) B`
  --     — transferred from `IsLocalization.tensorRight` (which gives the
  --     instance on `TensorProduct (Localization.Away f) (Localization.AtPrime m) B'`)
  --     across `eq_iso` via `IsLocalization.isLocalization_iff_of_ringEquiv`.
  obtain ⟨r, hr_mem, hbo⟩ : ∃ r ∈ m.primeCompl,
      ↑(PrimeSpectrum.basicOpen (algebraMap R B' r)) ⊆
        Algebra.etaleLocus (Localization.Away f) B' := by
    -- TODO (round 26+): expand into the annihilator chain via
    -- `exists_annihilator_in_R_complement_of_finite_localized`.
    -- Concrete plan:
    --  (i)  Establish `IsLocalization T B` (T := image of `m.primeCompl` in
    --       `B'`), transferring along `eq_iso` from
    --       `IsLocalization.tensorRight`.
    --  (ii) Use `KaehlerDifferential.isLocalizedModule_map A_f B' B T` to
    --       get `Subsingleton (LocalizedModule T Ω[B'/A_f])` from the
    --       étaleness of `B/A_m` (which kills `Ω[B/A_m]`, and via the
    --       exact-sequence `Ω[B/A_f] → Ω[B/A_m] → 0` and `Ω[A_m/A_f] = 0`
    --       gives `Ω[B/A_f] = 0`).
    --  (iii) Apply `exists_annihilator_in_R_complement_of_finite_localized`
    --        with `M := Ω[B'/A_f]` to extract `r₁ ∈ m.primeCompl`.
    --  (iv)  Localize at `algebraMap R B' r₁` to get `B'₁ := Loc.Away (...)`.
    --        Now `Ω[B'₁/A_f] = 0` (localization kills annihilated FG module),
    --        hence projective, hence `H¹Cot(A_f, B'₁)` is FG
    --        (`instFiniteH1CotangentOfFinitePresentationOfProjectiveKaehlerDifferential`).
    --  (v)   Re-apply `exists_annihilator_in_R_complement_of_finite_localized`
    --        with `M := H¹Cot(A_f, B'₁)` to extract `r₂ ∈ m.primeCompl`.
    --  (vi)  Set `r := r₁ * r₂`. Then `algebraMap R B' r ∈ Ann Ω ∩ Ann H¹Cot`,
    --        so by `etaleLocus_eq_compl_support`, `D(s) ⊆ etaleLocus`.
    -- The technical content involves transferring an `IsLocalization`
    -- across an `AlgEquiv` and threading the cotangent localization
    -- lemma. Both steps are routine but space-consuming.
    -- The instance `[Algebra R B']` is inferred from B' being a quotient of
    -- `MvPolynomial _ (Loc.Away f)` which is an R-algebra; similarly for
    -- the scalar tower.
    exact exists_basicOpen_subset_etaleLocus_of_descent m hf eq_iso
  -- Step 12: define `s := algebraMap R B' r` and the new model
  -- `B'' := Localization.Away s`.
  let s : B' := algebraMap R B' r
  let B'' : Type u := Localization.Away s
  -- Step 13: derive `Algebra.Etale (Loc.Away f) B''` from the
  -- basic-open containment via `basicOpen_subset_etaleLocus_iff_etale`.
  haveI h_etale : Algebra.Etale (Localization.Away f) B'' :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mp hbo
  -- Step 14: the algebra instance `Algebra (Loc.Away f) B''` is given by
  -- `OreLocalization.instAlgebra` (since `B'' = Loc.Away s` is built as an
  -- ore-localization of `B'`, and `B'` is an `Loc.Away f`-algebra).
  -- Step 15: build the descent iso
  --   `eq_iso' : B ≃ₐ[A_m] A_m ⊗_{A_f} B''`.
  -- Decomposition:
  --   `A_m ⊗_{A_f} B''  =  A_m ⊗_{A_f} Loc.Away s`
  --                    ≃ `Loc.Away (1 ⊗ s) (A_m ⊗_{A_f} B')`  (base change of localization)
  --                    ≃ `Loc.Away (image r in B) B`           (eq_iso)
  --                    ≃ `B`                                   (image r is a unit in B).
  -- The unit witness for `algebraMap R B r`: `r ∉ m`, so
  -- `algebraMap R A_m r` is a unit; composing with `A_m → B` keeps it
  -- a unit.
  letI algRB : Algebra R B :=
    ((algebraMap (Localization.AtPrime m) B).comp
      (algebraMap R (Localization.AtPrime m))).toAlgebra
  haveI istRAmB : IsScalarTower R (Localization.AtPrime m) B :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hr_unit_in_B : IsUnit (algebraMap R B r) := by
    have hAm_unit : IsUnit (algebraMap R (Localization.AtPrime m) r) :=
      IsLocalization.map_units (Localization.AtPrime m) (⟨r, hr_mem⟩ : m.primeCompl)
    have hcomp : algebraMap R B r =
        (algebraMap (Localization.AtPrime m) B) (algebraMap R (Localization.AtPrime m) r) :=
      IsScalarTower.algebraMap_apply R (Localization.AtPrime m) B r
    rw [hcomp]
    exact hAm_unit.map _
  -- Build `eq_iso'` (descent iso for the new model). The
  -- construction proceeds by (1) using `Algebra.TensorProduct.lift` to
  -- send `Loc.Away s` to `B` (mapping `s` to its image, which is a
  -- unit), then (2) composing with `eq_iso.symm` and showing the result
  -- is bijective. Step 11's `hbo`/`h_etale` already supply the étaleness;
  -- the iso is a structural identification.
  --
  -- Until the full TensorProduct.lift + IsLocalization argument is
  -- carried out, we expose the iso as a scoped sorry. This is the only
  -- remaining structural obligation; the étale conclusion above is
  -- discharged.
  -- Round 26 — close L486 by explicit construction.
  -- (i) Algebra hom `B' → B` (`Loc.Away f`-linear) via `eq_iso ∘ includeRight`.
  -- (ii) `toB s = algebraMap R B r`, hence a unit.
  -- (iii) Lift to `B'' = Loc.Away s → B` via `IsLocalization.liftAlgHom`.
  -- (iv) Build `backward` via `AlgHom.liftEquiv`.
  -- (v) Build `forward = tmap ∘ eq_iso.symm`, where
  --     `tmap = TensorProduct.map id (algebraMap B' B'')`.
  -- (vi) Bundle via `AlgEquiv.ofAlgHom`, mutual inverses via
  --      `Algebra.TensorProduct.ext` + `IsLocalization.algHom_ext`.
  haveI istR_Af_B' : IsScalarTower R (Localization.Away f) B' := inferInstance
  let toB : B' →ₐ[Localization.Away f] B :=
    (eq_iso.toAlgHom.restrictScalars (Localization.Away f)).comp
      Algebra.TensorProduct.includeRight
  have htower : ∀ x : R,
      algebraMap (Localization.Away f) B (algebraMap R (Localization.Away f) x) =
        algebraMap R B x := fun x => by
    rw [IsScalarTower.algebraMap_apply (Localization.Away f) (Localization.AtPrime m) B,
        ← IsScalarTower.algebraMap_apply R (Localization.Away f) (Localization.AtPrime m),
        ← IsScalarTower.algebraMap_apply R (Localization.AtPrime m) B]
  have hs_eq : toB s = algebraMap R B r := by
    show toB (algebraMap R B' r) = _
    rw [IsScalarTower.algebraMap_apply R (Localization.Away f) B', AlgHom.commutes]
    exact htower r
  have hs_unit_y : ∀ y : Submonoid.powers s, IsUnit (toB y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow, hs_eq]
    exact hr_unit_in_B.pow n
  let toB'' : B'' →ₐ[Localization.Away f] B :=
    IsLocalization.liftAlgHom (S := B'') (A := Localization.Away f) hs_unit_y
  have htoB''_algMap : ∀ b' : B',
      toB'' (algebraMap B' B'' b') = toB b' := fun b' => by
    show IsLocalization.liftAlgHom hs_unit_y (algebraMap B' B'' b') = _
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    rfl
  let backward : TensorProduct (Localization.Away f) (Localization.AtPrime m) B''
      →ₐ[Localization.AtPrime m] B :=
    AlgHom.liftEquiv (Localization.Away f) (Localization.AtPrime m) B'' B toB''
  let tmap : TensorProduct (Localization.Away f) (Localization.AtPrime m) B'
      →ₐ[Localization.AtPrime m]
      TensorProduct (Localization.Away f) (Localization.AtPrime m) B'' :=
    Algebra.TensorProduct.map
      (AlgHom.id (Localization.AtPrime m) (Localization.AtPrime m))
      (IsScalarTower.toAlgHom (Localization.Away f) B' B'')
  let forward : B →ₐ[Localization.AtPrime m]
      TensorProduct (Localization.Away f) (Localization.AtPrime m) B'' :=
    tmap.comp eq_iso.symm.toAlgHom
  have h_bt : backward.comp tmap =
      (eq_iso.toAlgHom : _ →ₐ[Localization.AtPrime m] B) := by
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    refine AlgHom.ext fun b' => ?_
    show backward (tmap (1 ⊗ₜ b')) = eq_iso (1 ⊗ₜ b')
    show backward ((1 : Localization.AtPrime m) ⊗ₜ algebraMap B' B'' b') = _
    show (1 : Localization.AtPrime m) • toB'' (algebraMap B' B'' b') = _
    rw [one_smul, htoB''_algMap]
    rfl
  have eq_iso' : Nonempty (B ≃ₐ[Localization.AtPrime m]
      TensorProduct (Localization.Away f) (Localization.AtPrime m) B'') := by
    refine ⟨AlgEquiv.ofAlgHom forward backward ?_ ?_⟩
    · refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
      refine IsLocalization.algHom_ext (R := Localization.Away f) (Submonoid.powers s) ?_
      refine AlgHom.ext fun b' => ?_
      show forward (backward ((1 : Localization.AtPrime m) ⊗ₜ algebraMap B' B'' b')) =
          (1 : Localization.AtPrime m) ⊗ₜ algebraMap B' B'' b'
      show forward ((1 : Localization.AtPrime m) • toB'' (algebraMap B' B'' b')) = _
      rw [one_smul, htoB''_algMap]
      show tmap (eq_iso.symm (toB b')) = _
      show tmap (eq_iso.symm (eq_iso (1 ⊗ₜ b'))) = _
      rw [AlgEquiv.symm_apply_apply]
      rfl
    · show backward.comp (tmap.comp eq_iso.symm.toAlgHom) = AlgHom.id _ _
      rw [← AlgHom.comp_assoc, h_bt]
      exact AlgEquiv.comp_symm eq_iso
  refine ⟨f, hf, B'', inferInstance, inferInstance, h_etale, algAfAm, istR_Af_Am,
    algAfB, istAf_Am_B, eq_iso'⟩

end Algebra.Etale
