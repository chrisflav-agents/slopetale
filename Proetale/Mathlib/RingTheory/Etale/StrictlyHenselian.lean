/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Proetale.Mathlib.RingTheory.Etale.HenselianIdempotentLift
import Proetale.Mathlib.RingTheory.Henselian
import Proetale.Mathlib.RingTheory.Localization.AtIdempotent

/-!
# Étale algebras over strictly Henselian local rings

This file develops the two key structural results about étale algebras over a strictly
Henselian local ring `A` (Stacks `04GG` / `04GH`).

## Main statements

- `Algebra.Etale.strictlyHenselian_good_retraction` (Stacks `04GH`): if `A` is strictly
  Henselian, `A → B` is étale, and `n ⊂ B` is a maximal ideal lying over the maximal
  ideal `m` of `A`, then there exists an `A`-algebra retraction `s : B →ₐ[A] A` with
  `n = m.comap s.toRingHom` (equivalently, `n = s⁻¹(m)`).
- `Algebra.Etale.bijective_localRingHom_of_strictlyHenselian` (Stacks `04GG`): under the
  same hypotheses, the canonical local ring homomorphism `Localization.AtPrime m → B_n`
  is bijective. Equivalently, `A → B_n` is an isomorphism.

The blueprint reference is `local-structure.tex`,
`thm:strictly-henselian-good-retraction` (L657) and
`thm:etale-over-strictly-henselian-localization-isom` (L676).

## Implementation notes

The good-retraction proof is decomposed into two private helpers:

- `stage1_raw_retraction`: produces a raw retraction `r : B →ₐ[A] A`, plus the auxiliary
  facts that there are only finitely many primes of `B` over `m` and that each such
  prime is maximal. All three outputs come from the étale-over-field decomposition
  `B/mB ≃ ∏ k_i` (`Algebra.Etale.iff_exists_algEquiv_prod`) plus Hensel lifting against
  `IsSepClosed (ResidueField A)`. Currently a structural typed sorry — this is the only
  residual `sorry` in the 04GH proof.
- `stage2_make_residue_compatible`: given an étale algebra `B` with maximal `n` over `m`,
  invokes stage 1 to recover finiteness/maximality of primes over `m`, applies prime
  avoidance to find `b ∉ n` with `b` in every other such prime, localizes to `B_b`
  (still étale over `A`, and now with `n B_b` as the unique prime over `m`), invokes
  stage 1 again on `(B_b, n B_b)` to obtain a raw retraction `r_b : B_b →ₐ[A] A`, and
  composes `B → B_b → A`. Residue compatibility is forced by uniqueness of the prime
  of `B_b` over `m`.

The bijectivity result `bijective_localRingHom_of_strictlyHenselian` is reduced (iter-016)
to a single internal typed sorry: the surjectivity of `algebraMap A (Loc n)`. The
diagram-chase reduction (the iso `A ≃ Loc m` via `IsLocalization.atUnits`, the
diagram identity `localRingHom ∘ algebraMap A Lm = algebraMap A Ln`, and the
section-injectivity of `algebraMap A Ln`) is fully formalized. The remaining gap
is the étale cancellation step: in `Loc n`, the kernel `I := ker(s) ⊆ n` is
annihilated (`I.Ln = 0`), equivalently the section `s_loc : Loc n → A` is injective.
This is the algebraic content of "a section of an étale morphism is an open
immersion" — not yet in Mathlib at the algebraic API level.
-/

universe u

open IsLocalRing Ideal

namespace Algebra.Etale

variable {A : Type u} [CommRing A] [IsStrictlyHenselianLocalRing A]

/-- **Prime avoidance (Finset form).** Given a prime `q` and finitely many ideals
`f i` (`i ∈ s`), none of which is contained in `q`, there exists `g ∈ ⋂ s.inf f`
with `g ∉ q`.

Re-derived locally to avoid `private` visibility issues with the version in
`Proetale.Algebra.WStrictLocalization`. -/
private lemma exists_mem_finset_inf_notMem_of_isPrime
    {R : Type*} [CommRing R] {ι : Type*} {s : Finset ι} {f : ι → Ideal R}
    {q : Ideal R} [q.IsPrime] (hnotle : ∀ i ∈ s, ¬ f i ≤ q) :
    ∃ g : R, g ∉ q ∧ ∀ i ∈ s, g ∈ f i := by
  have hnot_le : ¬ (s.inf f ≤ q) := fun h => by
    obtain ⟨i, his, hi⟩ := (Ideal.IsPrime.inf_le' ‹q.IsPrime›).mp h
    exact hnotle i his hi
  have hnot_subset : ¬ ((s.inf f : Ideal R) : Set R) ⊆ (q : Set R) := hnot_le
  rw [Set.not_subset] at hnot_subset
  obtain ⟨g, hg_inf, hg_q⟩ := hnot_subset
  refine ⟨g, hg_q, ?_⟩
  rwa [SetLike.mem_coe, Submodule.mem_finsetInf] at hg_inf

/-- **Phase 1 helper for Stage 1: residue-class section.**

Given an étale `A`-algebra `B` with a maximal ideal `n` lying over the maximal ideal
`m = maximalIdeal A`, and assuming `A` is strictly Henselian (so `k = A/m` is
separably closed), there exists an `A`-algebra homomorphism `B →ₐ[A] k`.

Informal proof (Stacks 04GH, Steps 3a–3c):

* The fibre `Bk := k ⊗_A B = B/mB` is étale over `k`, and by
  `Algebra.Etale.iff_exists_algEquiv_prod` it splits as a finite product
  `Bk ≃ₐ[k] ∏_{i ∈ I} kI i` with each `kI i` a finite separable extension of `k`.
* Each `kI i` is a finite separable extension of the sep-closed field `k`, hence
  `kI i ≃ₐ[k] k` (via `IsSepClosed`).
* The unique prime `n` of `B` over `m` (after pull-back to `Bk`) selects an index
  `i₀ : I`; the composite `B → B/mB ≃ ∏ kI i → kI i₀ ≃ k` is the desired map.

Left as a typed sorry — the index extraction via
`PrimeSpectrum.primesOverOrderIsoFiber` plus the `IsSepClosed`-driven trivialization
of each `kI i` is the technical work tracked in iter-029+. Closing this helper plus
`exists_section_of_residueField_section` closes the Phase 1 stage-1 sorry. -/
private lemma exists_residueField_algHom_of_etale_max
    {A B : Type u} [CommRing A] [IsStrictlyHenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (_h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    Nonempty (B →ₐ[A] IsLocalRing.ResidueField A) := by
  classical
  -- Step 1. Set up `k := ResidueField A` and the fibre `Bk := k ⊗[A] B`.
  -- `Bk` is étale over `k` via `Algebra.Etale.baseChange`.
  haveI : Algebra.Etale (IsLocalRing.ResidueField A)
      (TensorProduct A (IsLocalRing.ResidueField A) B) :=
    Algebra.Etale.baseChange A B (IsLocalRing.ResidueField A)
  -- Step 2. Decompose `Bk ≃ ∀ i, kI i` as a finite product of finite-separable
  -- extensions of `k`.
  obtain ⟨I, hIfin, kI, hKfield, hKalg, e, hKsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := IsLocalRing.ResidueField A)
      (A := TensorProduct A (IsLocalRing.ResidueField A) B)).mp inferInstance
  letI : Finite I := hIfin
  letI : ∀ i, Field (kI i) := hKfield
  letI : ∀ i, Algebra (IsLocalRing.ResidueField A) (kI i) := hKalg
  -- Step 3. Show `I` is nonempty. Via `TensorProduct.quotTensorEquivQuotSMul`,
  -- `Bk ≃ₗ[A] B ⧸ (m • ⊤)`. The submodule `m • ⊤` lies inside `n` (because `n` lies
  -- over `m`), and `n ≠ ⊤`, so `Nontrivial (B ⧸ m • ⊤)`. Transferring through the
  -- equiv gives `Nontrivial Bk`, and via `e` so is `∀ i, kI i`, forcing `Nonempty I`.
  haveI hBkNon : Nontrivial (TensorProduct A (IsLocalRing.ResidueField A) B) := by
    have hmB_le :
        (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A B) ≤
          Submodule.restrictScalars A n := by
      refine Submodule.smul_le.mpr fun x hx b _ => ?_
      rw [Algebra.smul_def, Submodule.restrictScalars_mem]
      refine n.mul_mem_right _ ?_
      have hxn : x ∈ n.comap (algebraMap A B) := _h.symm ▸ hx
      exact hxn
    have hmB_ne_top :
        (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A B) ≠ ⊤ := by
      intro hmB
      apply ‹n.IsMaximal›.ne_top
      apply Submodule.restrictScalars_injective A
      rw [Submodule.restrictScalars_top]
      exact top_le_iff.mp (hmB ▸ hmB_le)
    haveI : Nontrivial
        (B ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A B)) :=
      Submodule.Quotient.nontrivial_iff.mpr hmB_ne_top
    exact
      (TensorProduct.quotTensorEquivQuotSMul B
        (IsLocalRing.maximalIdeal A)).toEquiv.nontrivial
  haveI hPiNon : Nontrivial (∀ i, kI i) :=
    e.symm.toRingHom.domain_nontrivial
  haveI hInonempty : Nonempty I := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have hsub : Subsingleton (∀ i, kI i) := (Pi.uniqueOfIsEmpty kI).instSubsingleton
    exact not_subsingleton _ hsub
  -- Step 4. Pick any `i₀ : I`. Since `IsSepClosed k` and `kI i₀` is separable
  -- over `k`, `algebraMap k (kI i₀)` is bijective, giving `k ≃ₐ[k] kI i₀`.
  let i₀ : I := Classical.arbitrary I
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField A) (kI i₀) := (hKsep i₀).2
  haveI : Module.Finite (IsLocalRing.ResidueField A) (kI i₀) := (hKsep i₀).1
  have hsurj : Function.Surjective (algebraMap (IsLocalRing.ResidueField A) (kI i₀)) :=
    IsSepClosed.algebraMap_surjective (IsLocalRing.ResidueField A) (kI i₀)
  have hinj : Function.Injective (algebraMap (IsLocalRing.ResidueField A) (kI i₀)) :=
    FaithfulSMul.algebraMap_injective (IsLocalRing.ResidueField A) (kI i₀)
  let ψ : IsLocalRing.ResidueField A ≃ₐ[IsLocalRing.ResidueField A] kI i₀ :=
    AlgEquiv.ofBijective
      (Algebra.ofId (IsLocalRing.ResidueField A) (kI i₀)) ⟨hinj, hsurj⟩
  -- Step 5. Compose `B →ₐ[A] Bk →ₐ[k] ∀ i, kI i →ₐ[k] kI i₀ ≃ₐ[k] k`.
  let toBk : B →ₐ[A] TensorProduct A (IsLocalRing.ResidueField A) B :=
    Algebra.TensorProduct.includeRight
  let toPi : TensorProduct A (IsLocalRing.ResidueField A) B
      →ₐ[IsLocalRing.ResidueField A] (∀ i, kI i) := e.toAlgHom
  let evalI₀ : (∀ i, kI i) →ₐ[IsLocalRing.ResidueField A] kI i₀ :=
    Pi.evalAlgHom (IsLocalRing.ResidueField A) kI i₀
  exact ⟨((ψ.symm.toAlgHom.comp (evalI₀.comp toPi)).restrictScalars A).comp toBk⟩

/-- **Helper A for Phase 2: standard-étale Hensel section-lift.**

Given a Henselian local ring `A` and a standard étale pair `P : StandardEtalePair A`,
any `A`-algebra map `g : P.Ring →ₐ[A] ResidueField A` lifts to an `A`-algebra
section `σ : P.Ring →ₐ[A] A` whose reduction modulo `maximalIdeal A` equals `g`.

The proof: `g P.X` is an element `x_bar` of the residue field with
`P.HasMap x_bar` (via `P.hasMap_X.map g`). Lift it to `a₀ : A`. The polynomial
identities `P.f.eval a₀ ∈ maximalIdeal A` and `IsUnit (P.f.derivative.eval a₀)`
hold by transport. Apply `HenselianLocalRing.is_henselian` to obtain a root
`α` of `P.f` with `α ≡ a₀ mod m`. Build `P.HasMap α` (the `IsUnit (aeval α P.g)`
clause follows because the residue `aeval (residue α) P.g = aeval x_bar P.g` is
a unit, so `aeval α P.g ∉ m`). Finally `σ := P.lift α` and the residue
compatibility follows from `P.hom_ext` checked on `P.X`. -/
private lemma exists_section_of_standardEtalePair
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    (P : StandardEtalePair A)
    (g : P.Ring →ₐ[A] IsLocalRing.ResidueField A) :
    ∃ σ : P.Ring →ₐ[A] A,
      (IsLocalRing.residue A).comp σ.toRingHom = g.toRingHom := by
  -- Step 1. `g P.X` has `P.HasMap`.
  have hxbar : P.HasMap (g P.X) := P.hasMap_X.map g
  -- Step 2. Lift `g P.X` to `a₀ : A` with `residue A a₀ = g P.X`.
  obtain ⟨a₀, ha₀⟩ : ∃ a, IsLocalRing.residue A a = g P.X :=
    Ideal.Quotient.mk_surjective _
  -- Step 3. Polynomial-aeval through `residue A` (for any `a : A`).
  have aeval_res : ∀ (a : A) (p : Polynomial A),
      Polynomial.aeval (IsLocalRing.residue A a) p =
        IsLocalRing.residue A (Polynomial.eval a p) := by
    intro a p
    rw [Polynomial.aeval_def]
    exact Polynomial.eval₂_at_apply (IsLocalRing.residue A) a
  -- Step 4. `P.f.eval a₀ ∈ maximalIdeal A`.
  have hfa₀_mem : Polynomial.eval a₀ P.f ∈ IsLocalRing.maximalIdeal A := by
    have h := hxbar.1
    rw [← ha₀, aeval_res] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  -- Step 5. `IsUnit (P.f.derivative.eval a₀)`.
  have hd_a₀_unit : IsUnit (Polynomial.eval a₀ P.f.derivative) := by
    have h := hxbar.isUnit_derivative_f
    rw [← ha₀, aeval_res] at h
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    have hz : IsLocalRing.residue A (Polynomial.eval a₀ P.f.derivative) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hz] at h
    exact not_isUnit_zero h
  -- Step 6. Henselian lift.
  obtain ⟨α, hα_root, hα_diff⟩ :=
    HenselianLocalRing.is_henselian P.f P.monic_f a₀ hfa₀_mem hd_a₀_unit
  -- Step 7. `residue A α = g P.X`.
  have hres_α : IsLocalRing.residue A α = g P.X := by
    rw [← ha₀]
    have hz : IsLocalRing.residue A (α - a₀) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hα_diff
    rwa [map_sub, sub_eq_zero] at hz
  -- Step 8. `P.HasMap α`.
  have hαMap : P.HasMap α := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.coe_aeval_eq_eval]; exact hα_root
    · rw [← IsLocalRing.notMem_maximalIdeal]
      intro hmem
      have hgxbar_unit : IsUnit (Polynomial.aeval (g P.X) P.g) := hxbar.2
      have hg_xbar_zero : Polynomial.aeval (g P.X) P.g = 0 := by
        rw [← hres_α, aeval_res α P.g]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
          rw [Polynomial.coe_aeval_eq_eval] at hmem; exact hmem)
      rw [hg_xbar_zero] at hgxbar_unit
      exact not_isUnit_zero hgxbar_unit
  -- Step 9. Build `σ := P.lift α` and verify residue compatibility.
  refine ⟨P.lift α hαMap, ?_⟩
  have h_alg : (Algebra.ofId A (IsLocalRing.ResidueField A)).comp (P.lift α hαMap) = g := by
    apply P.hom_ext
    show (Algebra.ofId A (IsLocalRing.ResidueField A)) ((P.lift α hαMap) P.X) = g P.X
    rw [P.lift_X α hαMap]
    show algebraMap A (IsLocalRing.ResidueField A) α = g P.X
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact hres_α
  ext x
  exact AlgHom.congr_fun h_alg x

/-- **Helper B.2 (assembly): build a `StandardEtalePair A` from a monic polynomial.**

The standard étale pair `(f, f.derivative)` with the trivial Bezout
identity `f.derivative * 1 + f * 0 = f.derivative ^ 1`. -/
private noncomputable def standardEtalePairOfMonic
    {A : Type u} [CommRing A] (f : Polynomial A) (hf : f.Monic) :
    StandardEtalePair A where
  f := f
  monic_f := hf
  g := f.derivative
  cond := ⟨1, 0, 1, by simp⟩

/-- **Helper B.1: lift of a separable primitive element.**

Given an étale `A`-algebra `B/A` and a maximal ideal `n ⊂ B` lying over the
maximal ideal of `A`, there exist `β ∈ B` and a monic polynomial `f ∈ A[X]` such
that:

* `f(β) ∈ n`,
* `f'(β) ∉ n`.

The classical proof (Stacks 00U7, Step 1+2):

* The fibre `B/mB` is étale over `k = A/m` and decomposes as `∏ k_i` of
  finite-separable extensions (`Algebra.Etale.iff_exists_algEquiv_prod`).
* The factor at `n` is `B/n`, finite-separable over `k`. By the primitive
  element theorem, pick `ᾱ ∈ B/n` with separable monic minimal polynomial
  `f̄ ∈ k[X]`.
* Lift `ᾱ` to `β ∈ B` via `Ideal.Quotient.mk_surjective` and lift `f̄` to
  monic `f ∈ A[X]` (using monic-lifting along the residue map). Then
  `f(β) ≡ f̄(ᾱ) = 0 (mod n)`, and `f'(β) ≡ f̄'(ᾱ) ≠ 0 (mod n)` by
  separability.

Left as a typed sorry — the formalization requires identifying `B/n` with the
appropriate factor of `B/mB` plus monic-lifting along `A[X] → k[X]`. -/
private lemma exists_lift_separablePrimitiveElement_of_etale_at_maxIdeal
    {A B : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    ∃ (β : B) (f : Polynomial A), f.Monic ∧
      Polynomial.eval β (f.map (algebraMap A B)) ∈ n ∧
      Polynomial.eval β (f.derivative.map (algebraMap A B)) ∉ n := by
  classical
  -- ============================================================
  -- Step 1. Setup. `m := maximalIdeal A`, `k := A/m`, `L := B/n`.
  -- ============================================================
  haveI hn_over : n.LiesOver (IsLocalRing.maximalIdeal A) := ⟨h.symm⟩
  letI hm_max : (IsLocalRing.maximalIdeal A).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal A
  letI hkF : Field (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) :=
    Ideal.Quotient.field _
  letI hLF : Field (B ⧸ n) := Ideal.Quotient.field n
  letI hAlg : Algebra (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n) :=
    Ideal.Quotient.algebraOfLiesOver _ _
  -- ============================================================
  -- Step 2. Finiteness and separability of `(B/n) / (A/m)`.
  --
  -- These follow from the étale-over-field decomposition `k ⊗_A B ≃ ∏ k_i`
  -- (each `k_i` finite separable over `k`) plus identification of `B/n` with
  -- the n-factor of `k ⊗ B`. Implementing the identification step is the
  -- residual gap; we record both facts as typed sub-sorries here.
  -- ============================================================
  -- (a) Set up scaffolding: route through `n.ResidueField` to get separability.
  --     We have `Algebra.FormallyUnramified A (Loc n)` + `EssFiniteType A (Loc n)`
  --     + `IsLocalHom (algebraMap A (Loc n))`, giving by Mathlib's
  --     `Algebra.instIsSeparableResidueFieldOfFormallyUnramified`:
  --       `Algebra.IsSeparable (ResidueField A) (ResidueField (Loc n))`.
  --     Since `n.ResidueField = ResidueField (Loc n)` definitionally, this is
  --     `IsSeparable (ResidueField A) n.ResidueField`.
  haveI : Algebra.EssFiniteType A B := inferInstance
  haveI : Algebra.EssFiniteType B (Localization.AtPrime n) :=
    Algebra.EssFiniteType.of_isLocalization (Localization.AtPrime n) n.primeCompl
  haveI : Algebra.EssFiniteType A (Localization.AtPrime n) :=
    Algebra.EssFiniteType.comp A B (Localization.AtPrime n)
  haveI : Algebra.FormallyUnramified A B := inferInstance
  haveI : Algebra.FormallyUnramified B (Localization.AtPrime n) :=
    Algebra.FormallyUnramified.of_isLocalization n.primeCompl
  haveI : Algebra.FormallyUnramified A (Localization.AtPrime n) :=
    Algebra.FormallyUnramified.comp A B (Localization.AtPrime n)
  haveI : IsLocalHom (algebraMap A (Localization.AtPrime n)) := by
    -- Use the TFAE characterization: `IsLocalHom f` iff
    -- `f⁻¹ (maximalIdeal _) = maximalIdeal _` for local-to-local maps.
    have htfae := (IsLocalRing.local_hom_TFAE
        (algebraMap A (Localization.AtPrime n))).out 0 4
    rw [htfae]
    show Ideal.comap (algebraMap A (Localization.AtPrime n))
        (IsLocalRing.maximalIdeal (Localization.AtPrime n)) =
        IsLocalRing.maximalIdeal A
    rw [show (algebraMap A (Localization.AtPrime n) : A →+* _) =
          (algebraMap B (Localization.AtPrime n)).comp (algebraMap A B) from rfl,
        ← Ideal.comap_comap]
    rw [show Ideal.comap (algebraMap B (Localization.AtPrime n))
          (IsLocalRing.maximalIdeal (Localization.AtPrime n)) = n from
        IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime n) n]
    exact h
  haveI hsep0 : Algebra.IsSeparable (IsLocalRing.ResidueField A) n.ResidueField :=
    inferInstance
  -- (b) Transport `hsep0` to `IsSeparable (A/m) (B/n)`.
  --     Set up `Algebra (Loc m) (Loc n)` so the residue-field iff lemma applies.
  letI hLmn : Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal A))
      (Localization.AtPrime n) :=
    Localization.AtPrime.algebraOfLiesOver (IsLocalRing.maximalIdeal A) n
  -- The `IsLiesOverAlgebra` instance is automatic.
  -- We have `IsSeparable (ResidueField A) n.ResidueField`. Transport via:
  --   `ResidueField A := A ⧸ maximalIdeal A` definitionally, and
  --   `m.ResidueField` is `IsLocalRing.ResidueField (Loc m)`, isomorphic but
  --   not equal to `ResidueField A`. The residual gap is the
  --   `m.ResidueField ↔ ResidueField A` bridge.
  haveI hsep : Algebra.IsSeparable
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n) := by
    -- Transport `hsep0 : IsSeparable (ResidueField A) n.ResidueField` to
    -- `IsSeparable (A/m) (B/n)`. The base fields agree definitionally
    -- (`ResidueField A := A ⧸ m`); the target rings are related by the
    -- bijection `algebraMap (B/n) n.ResidueField`. Residual sub-sorry: the
    -- algebra-compatibility square between the two algebra structures
    -- (one on `(A/m, B/n)`, the other on `(ResidueField A, n.ResidueField)`).
    refine Algebra.IsSeparable.of_equiv_equiv
      (RingEquiv.refl (IsLocalRing.ResidueField A))
      (RingEquiv.symm (RingEquiv.ofBijective _
        n.bijective_algebraMap_quotient_residueField)) ?_
    -- Compatibility square: both paths from `ResidueField A` to `B/n`
    -- agree on representatives via scalar tower through `A`.
    refine RingHom.ext fun x => ?_
    -- Lift `x : ResidueField A = A/m` to some `a : A`.
    obtain ⟨a, rfl⟩ : ∃ a : A,
        algebraMap A (IsLocalRing.ResidueField A) a = x :=
      Ideal.Quotient.mk_surjective x
    -- Apply the n.ResidueField-bijection (in the forward direction) to both
    -- sides to remove the `.symm`, then both sides equal the canonical
    -- algebraMap A n.ResidueField a (via scalar-tower compatibility).
    apply (RingEquiv.ofBijective _ n.bijective_algebraMap_quotient_residueField).injective
    show (RingEquiv.ofBijective _ n.bijective_algebraMap_quotient_residueField)
        ((algebraMap (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n))
          ((algebraMap A (IsLocalRing.ResidueField A)) a)) =
      (RingEquiv.ofBijective _ n.bijective_algebraMap_quotient_residueField)
        ((RingEquiv.ofBijective _ n.bijective_algebraMap_quotient_residueField).symm
          ((algebraMap (IsLocalRing.ResidueField A) n.ResidueField)
            ((algebraMap A (IsLocalRing.ResidueField A)) a)))
    rw [RingEquiv.apply_symm_apply, RingEquiv.ofBijective_apply]
    -- Both sides equal `algebraMap A n.ResidueField a` via scalar towers.
    show (algebraMap (B ⧸ n) n.ResidueField)
        ((algebraMap (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n))
          ((algebraMap A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A))) a)) = _
    rw [← IsScalarTower.algebraMap_apply A
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n) a,
      ← IsScalarTower.algebraMap_apply A (B ⧸ n) n.ResidueField a,
      ← IsScalarTower.algebraMap_apply A (IsLocalRing.ResidueField A) n.ResidueField a]
  -- (c) Algebraicity from separability (instance).
  haveI : Algebra.IsAlgebraic
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n) := inferInstance
  -- (d) EssFiniteType (A/m) (B/n): from `[FiniteType A B]` (étale ⇒ FP ⇒ FT)
  --     via `algebra_finiteType_of_liesOver`, then FT ⇒ EssFiniteType.
  haveI : Algebra.FiniteType A B := inferInstance
  haveI : Algebra.FiniteType
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n) :=
    algebra_finiteType_of_liesOver n (IsLocalRing.maximalIdeal A)
  haveI : Algebra.EssFiniteType
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n) := inferInstance
  -- (e) Module.Finite via `Algebra.finite_of_essFiniteType_of_isAlgebraic`.
  haveI hfin : Module.Finite
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n) :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  -- ============================================================
  -- Step 3. Primitive element ᾱ ∈ B/n with `k⟮ᾱ⟯ = ⊤`.
  -- ============================================================
  obtain ⟨ᾱ, hα_top⟩ := Field.exists_primitive_element
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n)
  haveI hα_int : IsIntegral (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) ᾱ :=
    Algebra.IsIntegral.isIntegral ᾱ
  -- Minimal polynomial.
  let fbar : Polynomial (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) :=
    minpoly _ ᾱ
  have hfbar_monic : fbar.Monic := minpoly.monic hα_int
  have hfbar_aeval : Polynomial.aeval ᾱ fbar = 0 := minpoly.aeval _ ᾱ
  -- Separability: fbar is separable since ᾱ is.
  have hfbar_sep : fbar.Separable := Algebra.IsSeparable.isSeparable' ᾱ
  -- Derivative does not vanish at ᾱ: fbar'(ᾱ) ≠ 0.
  have hfbar'_aeval_ne : Polynomial.aeval ᾱ fbar.derivative ≠ 0 :=
    hfbar_sep.aeval_derivative_ne_zero hfbar_aeval
  -- ============================================================
  -- Step 4. Lift ᾱ to β ∈ B.
  -- ============================================================
  obtain ⟨β, hβ⟩ : ∃ β : B, Ideal.Quotient.mk n β = ᾱ :=
    Ideal.Quotient.mk_surjective ᾱ
  -- ============================================================
  -- Step 5. Lift f̄ ∈ k[X] to monic f ∈ A[X] with `f.map (algebraMap A k) = f̄`.
  -- ============================================================
  have hmk_surj : Function.Surjective
      (algebraMap A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A))) :=
    Ideal.Quotient.mk_surjective
  -- Polynomial.map of a surjective ring hom is surjective.
  have hPmap_surj :
      Function.Surjective (Polynomial.map
        (algebraMap A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)))) :=
    Polynomial.map_surjective _ hmk_surj
  obtain ⟨f₀, hf₀_map⟩ := hPmap_surj fbar
  have hfbar_lifts : fbar ∈ Polynomial.lifts
      (algebraMap A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A))) := ⟨f₀, hf₀_map⟩
  obtain ⟨f, hf_map, _hf_deg, hf_monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hfbar_lifts hfbar_monic
  -- f : Polynomial A, f.Monic, f.map (algebraMap A k) = fbar.
  refine ⟨β, f, hf_monic, ?_, ?_⟩
  -- ============================================================
  -- Step 6a. f(β) ∈ n: reduce mod n to f̄(ᾱ) = 0.
  -- ============================================================
  · -- Show `Ideal.Quotient.mk n (eval β (f.map (algebraMap A B))) = 0`.
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    -- The composition (B/n)-eval after Ideal.Quotient.mk n equals
    -- aeval ᾱ on the reduction of f.
    show (Ideal.Quotient.mk n)
        (Polynomial.eval β (f.map (algebraMap A B))) = 0
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, hβ]
    -- Goal: eval₂ ((Quotient.mk n).comp (algebraMap A B)) ᾱ f = 0
    -- Composition identifies as algebraMap A (B/n) factored through (A/m).
    have hcomp : (Ideal.Quotient.mk n).comp (algebraMap A B) =
        (algebraMap (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n)).comp
          (algebraMap A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A))) := by
      ext a; rfl
    rw [hcomp, ← Polynomial.eval₂_map, hf_map]
    -- Goal: eval₂ (algebraMap (A/m) (B/n)) ᾱ fbar = 0
    rw [← Polynomial.aeval_def]
    exact hfbar_aeval
  -- ============================================================
  -- Step 6b. f'(β) ∉ n: reduce mod n to f̄'(ᾱ) ≠ 0.
  -- ============================================================
  · -- Negation: assume the value is in n, derive contradiction with fbar'(ᾱ) ≠ 0.
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    intro heq
    apply hfbar'_aeval_ne
    -- Mirror the previous reduction.
    have hcomp : (Ideal.Quotient.mk n).comp (algebraMap A B) =
        (algebraMap (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n)).comp
          (algebraMap A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A))) := by
      ext a; rfl
    have hred :
        (Ideal.Quotient.mk n) (Polynomial.eval β
          (f.derivative.map (algebraMap A B))) =
        Polynomial.eval₂
          ((algebraMap (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) (B ⧸ n)).comp
            (algebraMap A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A))))
          ᾱ f.derivative := by
      rw [Polynomial.eval_map, Polynomial.hom_eval₂, hβ, hcomp]
    rw [hred, ← Polynomial.eval₂_map, ← Polynomial.derivative_map, hf_map] at heq
    rw [Polynomial.aeval_def]
    exact heq

/-- **Helper B.3.a.i.α₀ (idempotent-existence oracle, Step 3 of Stacks 00U7).**

Given an étale `A`-algebra `B` with `A` local and a maximal ideal `n ⊂ B` lying
over `m := maximalIdeal A`, there exists `e ∈ B \ n` whose image in `B/mB` is
the orthogonal idempotent isolating the `n`-factor of the étale decomposition
`B/mB ≃ ∏ k_i`. Concretely: `e ∉ n` and `e * e - e ∈ m · B`.

This is the algebraic content of Step 3 of Stacks 00U7: the bijection between
{primes of `B` over `m`} and the indexing set `I` of the decomposition selects
an index `i_n`; the orthogonal idempotent `Pi.single i_n 1 ∈ ∏ k_i` lifts to
`e_Bk ∈ Bk = B/mB`, which then lifts to `e ∈ B` via the surjection
`B → B/mB`. The lift is idempotent mod `mB` and projects to `1` in the
`n`-factor (hence `e ∉ n`).

**iter-046 strengthening.** The fourth conjunct
`∀ p, p.IsPrime → ¬(m·B ≤ p) → e ∈ p` is the horizontal-killing
clause: `e` is forced to vanish on every prime of `B` not lying above
`m`. Without it, the iter-045 helper `m_map_le_jacobson_of_etale_isolating`
is unsound (counterexample: `A = Z_(p)`, `B = Z_(p) × Q`,
`n = (p) × Q`, `e = 1 = (1,1)`; the horizontal max `Z_(p) × 0` is not
above `m` and `e` survives in it). With the strengthening, the
`m_map_le_jacobson_…` body closes via a pull-back chase. The new
conjunct is left as a separate typed sorry — the rigorous proof needs
Hensel lifting of idempotents over an étale-over-henselian-local
algebra (Stacks 0DXB fragment).

Left as a typed sorry — the explicit `i_n` extraction via the bijection
`{primes of B over m} ↔ I` is the residual structural gap; the rest of Stacks
00U7 (Step 5 vanishing, Step 8 surjectivity) is consumed downstream. -/
private lemma exists_idempotent_lift_isolating_at_maximal
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (_h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    ∃ e : B, e ∉ n ∧
      (e * e - e) ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) ∧
      (∀ x : B, x ∈ n →
        e * x ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) ∧
      (∀ p : Ideal B, p.IsPrime →
        ¬((IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ p) →
        e ∈ p) := by
  classical
  -- `mB := m · B ≤ n` (from `n.comap = m`).
  have hmB_le_n :
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B) : Ideal B) ≤ n :=
    Ideal.map_le_iff_le_comap.mpr _h.ge
  -- Step 1 (iter-048 refactor). Destructure the new Hensel-idempotent-lift
  -- helper to obtain the residue decomposition `Bk ≃ ∀ i, kI i` together
  -- with a TRUE complete orthogonal idempotent system `eLift : I → B`
  -- lifting `{Pi.single i 1}_i`.
  obtain ⟨I, hIfin, _hIdec, kI, hKfield, hKalg, eqv, eLift, hCop, hLift⟩ :=
    Algebra.Etale.exists_completeOrthogonalIdempotents_lift_of_henselian A B
  letI : Fintype I := hIfin
  letI : ∀ i, Field (kI i) := hKfield
  letI : ∀ i, Algebra (IsLocalRing.ResidueField A) (kI i) := hKalg
  -- Step 2. The `A`-algebra map `inj : B → Bk` is surjective
  -- (since `A → A/m` is surjective).
  let inj : B →ₐ[A] TensorProduct A (IsLocalRing.ResidueField A) B :=
    Algebra.TensorProduct.includeRight
  have hinj_surj : Function.Surjective inj :=
    Algebra.TensorProduct.includeRight_surjective B Ideal.Quotient.mk_surjective
  -- Step 3. Identify `ker inj = mB` via the algebra equiv
  -- `B/mB ≃ B ⊗ (A/m) ≃ (A/m) ⊗ B = Bk`.
  let φ_B : (B ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B))) ≃ₐ[B]
      TensorProduct A B (IsLocalRing.ResidueField A) :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal A)
  let φ : (B ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B))) ≃ₐ[A]
      TensorProduct A (IsLocalRing.ResidueField A) B :=
    (φ_B.restrictScalars A).trans
      (Algebra.TensorProduct.comm A B (IsLocalRing.ResidueField A))
  -- `φ ∘ (Quotient.mk) = inj`.
  have hφπ : ∀ b : B, φ ((Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B))) b) = inj b := by
    intro b
    show (Algebra.TensorProduct.comm A B (IsLocalRing.ResidueField A))
        (φ_B (Ideal.Quotient.mk _ b)) = _
    rw [show φ_B (Ideal.Quotient.mk _ b) = b ⊗ₜ[A] (1 : IsLocalRing.ResidueField A) from
        Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk B _ b]
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.includeRight_apply]
  -- Kernel characterization: `inj x = 0 ↔ x ∈ mB`.
  have hker : ∀ x : B, inj x = 0 ↔
      x ∈ ((IsLocalRing.maximalIdeal A).map (algebraMap A B) : Ideal B) := by
    intro x
    constructor
    · intro hx
      have h1 : φ (Ideal.Quotient.mk _ x) = 0 := by rw [hφπ]; exact hx
      have h2 : (Ideal.Quotient.mk _ x :
          B ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B))) = 0 :=
        φ.injective (h1.trans φ.map_zero.symm)
      rwa [Ideal.Quotient.eq_zero_iff_mem] at h2
    · intro hx
      have h2 : (Ideal.Quotient.mk _ x :
          B ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B))) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr hx
      rw [← hφπ, h2, map_zero]
  -- Step 4. Pick `i_n` with `eLift i_n ∉ n`. If all `eLift i ∈ n`, then
  -- `1 = Σ eLift i ∈ n`, contradiction.
  have hex : ∃ i, eLift i ∉ n := by
    by_contra hall_neg
    have hall_neg : ∀ i, eLift i ∈ n := fun i => by
      by_contra he_i; exact hall_neg ⟨i, he_i⟩
    have hsum_in : ∑ i, eLift i ∈ n := n.sum_mem fun i _ => hall_neg i
    have h1mem : (1 : B) ∈ n := by rw [← hCop.complete]; exact hsum_in
    exact ‹n.IsMaximal›.ne_top ((Ideal.eq_top_iff_one n).mpr h1mem)
  obtain ⟨i_n, hi_n⟩ := hex
  refine ⟨eLift i_n, hi_n, ?_, ?_, ?_⟩
  · -- Idempotent conjunct: `eLift i_n * eLift i_n - eLift i_n ∈ m · B`.
    -- Since `eLift i_n` is a true idempotent, the difference is zero.
    have : eLift i_n * eLift i_n - eLift i_n = 0 := by
      rw [(hCop.idem i_n).eq, sub_self]
    rw [this]; exact Submodule.zero_mem _
  · -- Isolation: for `x ∈ n`, `eLift i_n * x ∈ m · B`.
    intro x hx
    rw [← hker]
    -- `eqv (inj (eLift i_n * x)) = Pi.single i_n ((eqv (inj x)) i_n)`.
    have hcomp : eqv (inj (eLift i_n * x)) = Pi.single i_n ((eqv (inj x)) i_n) := by
      rw [map_mul (inj : B →ₐ[A] _), map_mul (eqv : _ ≃ₐ[_] _), hLift i_n,
        ← Pi.single_mul_left, one_mul]
    -- Show `(eqv (inj x)) i_n = 0`.
    have h_zero : (eqv (inj x)) i_n = 0 := by
      by_contra hne
      have hu_unit : IsUnit ((eqv (inj x)) i_n) := isUnit_iff_ne_zero.mpr hne
      obtain ⟨u_inv, hu_inv⟩ := hu_unit.exists_left_inv
      obtain ⟨v, hv⟩ := hinj_surj (eqv.symm (Pi.single i_n u_inv))
      have hcomp2 : eqv (inj (v * (eLift i_n * x))) = Pi.single i_n 1 := by
        rw [map_mul (inj : B →ₐ[A] _), map_mul (eqv : _ ≃ₐ[_] _), hv,
          AlgEquiv.apply_symm_apply, hcomp, ← Pi.single_mul, hu_inv]
      have h_eq_inj : inj (v * (eLift i_n * x)) = inj (eLift i_n) := by
        apply (eqv : _ ≃ₐ[_] _).injective
        rw [hcomp2, hLift i_n]
      have h_diff_in_mB : v * (eLift i_n * x) - eLift i_n ∈
          ((IsLocalRing.maximalIdeal A).map (algebraMap A B) : Ideal B) := by
        rw [← hker, map_sub, h_eq_inj, sub_self]
      have h_diff_in_n : v * (eLift i_n * x) - eLift i_n ∈ n := hmB_le_n h_diff_in_mB
      have h_prod_in_n : v * (eLift i_n * x) ∈ n :=
        n.mul_mem_left _ (n.mul_mem_left _ hx)
      apply hi_n
      have hdiff := n.sub_mem h_prod_in_n h_diff_in_n
      simpa using hdiff
    apply (eqv : _ ≃ₐ[_] _).injective
    rw [hcomp, h_zero, Pi.single_zero, map_zero]
  · -- Horizontal-killing conjunct (iter-046). For any prime `p` of `B` not
    -- containing `m · B`, show `eLift i_n ∈ p`.
    --
    -- iter-048 status: the naive lift `f i_n` of the previous body has been
    -- replaced by the TRUE orthogonal idempotent `eLift i_n` from the
    -- new Hensel-idempotent-lift helper. This gives genuine orthogonality
    -- `eLift i_n * eLift j = 0` for `j ≠ i_n` (via `hCop.ortho`) and
    -- completeness `Σ eLift i = 1` (via `hCop.complete`).
    --
    -- The remaining gap: deriving `eLift i_n ∈ p` from orthogonality
    -- requires showing that each factor `B / (1 - eLift i_n) · B` is
    -- **local** with maximal ideal `m · B / (1 - eLift i_n) · B`. This
    -- local-ness is the substantive content of Stacks 0DXB beyond the
    -- bare idempotent lift, and is not derivable from
    -- `CompleteOrthogonalIdempotents` alone. The iter-048 directive's
    -- sketch ("Build a residue map `B/p ↠ k_{i_n}`") implicitly assumes
    -- this local-ness — without it, the would-be residue map fails to
    -- factor through `B/p`.
    --
    -- Pending the étale-local-decomposition Mathlib API (Stacks 04GH
    -- product-decomposition form) or an extension of the new helper's
    -- conclusion to bundle horizontal-killing alongside orthogonality.
    sorry

/-- **iter-045 shared helper.** For `A` henselian local + `B` étale over `A` + `n`
maximal over `m = maximalIdeal A`, in any localization `Bb = B[1/b]` where the
witness `b` factors through an `n`-isolating idempotent `e` (i.e. `e ∣ b` with
`e` satisfying the conclusion of `exists_idempotent_lift_isolating_at_maximal`),
the extension `m·Bb` is contained in the Jacobson radical of `Bb`.

This is the **shared structural fact** behind both `aeval_f_eq_zero_in_localizationAway_of_etale`
(conclusion (iii)) and `surjective_standardEtalePair_lift_of_etale` (the §5
Nakayama body). The proof would go: every maximal ideal `q` of `Bb` pulls back
to a prime `p` of `B` not containing `b`. Since `e ∣ b`, `e ∉ p`. The
`e`-isolation `_he_isolate` then forces `p ⊆ n`: for any `x ∈ p`, either
`e ∈ p` (excluded) or `x ∈ n` (after multiplying both sides by `e` and using
that `e · x ∈ m·B ⊆ n`). So `p ⊆ n`, hence `p = n` if `p` is itself maximal
over `m`; otherwise `p` corresponds to a non-`m`-prime of `B` and the
contradiction with `q` maximal comes from the étale-going-up that forces
`m ⊆ p` (using `A` local + `Algebra.Etale.iff_exists_algEquiv_prod` + étale
goes up).

**iter-046 fix.** Added hypothesis `_he_horizontal`: `e` lies in every
prime of `B` not above `m`. With this, the body closes via a maximal-
ideal pull-back chase: any maximal `q ⊆ Bb` pulls back to a prime
`p ⊆ B` with `b ∉ p`; since `e ∣ b`, `e ∉ p`; contrapositive of
`_he_horizontal` then forces `m·B ⊆ p`, hence `m·Bb ⊆ q`. -/
private lemma m_map_le_jacobson_of_etale_isolating
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (_h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (e : B)
    (_he_idem : (e * e - e) ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (_he_notmem : e ∉ n)
    (_he_isolate : ∀ x : B, x ∈ n →
      e * x ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (_he_horizontal : ∀ p : Ideal B, p.IsPrime →
      ¬((IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ p) →
      e ∈ p)
    (b : B) (_hb_n : b ∉ n) (_he_div_b : e ∣ b)
    (Bb : Type u) [CommRing Bb] [Algebra B Bb]
    [IsLocalization.Away b Bb] [Algebra A Bb] [IsScalarTower A B Bb] :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A Bb) : Ideal Bb) ≤
      Ideal.jacobson (⊥ : Ideal Bb) := by
  -- Goal: m·Bb ≤ jacobson ⊥. Show m·Bb ≤ q for every maximal q ⊆ Bb.
  rw [Ideal.jacobson]
  refine le_sInf ?_
  rintro q ⟨_, hq_max⟩
  -- Let p be the pull-back of q under algebraMap B Bb.
  set p : Ideal B := q.comap (algebraMap B Bb) with hp_def
  have hp_prime : p.IsPrime := hq_max.isPrime.comap _
  -- algebraMap B Bb sends b to a unit; hence b ∉ p.
  have hbU : IsUnit (algebraMap B Bb b) := IsLocalization.Away.algebraMap_isUnit b
  have hq_ne_top : q ≠ ⊤ := hq_max.ne_top
  have hb_notin_p : b ∉ p := by
    intro hbmem
    -- hbmem : algebraMap B Bb b ∈ q
    apply hq_ne_top
    exact Ideal.eq_top_of_isUnit_mem _ hbmem hbU
  -- e ∣ b ⇒ e ∉ p (else b = e·c ∈ p).
  obtain ⟨c, hbec⟩ := _he_div_b
  have he_notin_p : e ∉ p := by
    intro he
    apply hb_notin_p
    rw [hbec]
    exact p.mul_mem_right c he
  -- Contrapositive of _he_horizontal: e ∉ p ⇒ m·B ⊆ p.
  have hmB_le_p :
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B) : Ideal B) ≤ p := by
    by_contra hle
    exact he_notin_p (_he_horizontal p hp_prime hle)
  -- Rewrite m·Bb = (m·B).map(algebraMap B Bb).
  have hmap_eq :
      ((IsLocalRing.maximalIdeal A).map (algebraMap A Bb) : Ideal Bb) =
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).map (algebraMap B Bb) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B Bb]
  rw [hmap_eq]
  exact Ideal.map_le_iff_le_comap.mpr hmB_le_p

/-- **Stacks 04GF analogue (iter-039).** If `A` is a Henselian local ring,
`C` is étale over `A`, and `q ⊆ C` is a maximal ideal lying over
`IsLocalRing.maximalIdeal A`, then the localization
`Localization.AtPrime q.primeCompl` is a Henselian local ring.

This is the algebraic content of Stacks 04GF: "an étale algebra over a
Henselian local ring is Henselian at every maximal ideal lying over the
closed point". The proof goes through the lifting characterisation of
Henselianness: given a monic `g ∈ Cq[X]` (where `Cq := Localization.AtPrime
q.primeCompl`) and a seed `α ∈ Cq` with `g(α) ∈ maximalIdeal Cq` and
`IsUnit (g'(α))`, the étale `A`-algebra `C'_α := Cq[X] / (g)` is itself
étale over `Cq`, hence (by composition with `A → Cq`) étale over `A`.
The seed `α` defines an `A`-algebra map `C'_α → Cq` modulo the maximal
ideal, and Henselianness of `A` lifts this to a true `A`-algebra section
`C'_α → Cq`. Reading off the image of `X` gives the Hensel-root.

Currently a typed `sorry` — the substantive Mathlib gap is the étale-lifting
step. The structure of the proof is laid out in the iter-039 blueprint:
the `Localization.AtPrime.isLocalRing` instance gives the local-ring
structure trivially; only the lifting property requires substantive work.
The first consumer is Step C's body (descent through
`Localization.AtPrime n_Bb.primeCompl`). -/
private theorem henselianLocalRing_of_etale_atPrime
    {A C : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing C] [Algebra A C] [Algebra.Etale A C]
    (q : Ideal C) [q.IsMaximal]
    (_hq : q.comap (algebraMap A C) = IsLocalRing.maximalIdeal A) :
    HenselianLocalRing (Localization.AtPrime q) := by
  -- The local-ring structure on `Cq := Localization.AtPrime q.primeCompl` is
  -- the Mathlib instance `Localization.AtPrime.isLocalRing`. The substantive
  -- content is the Hensel-lifting property, which is the Stacks 04GF Mathlib
  -- gap (no direct Mathlib lemma at iter-039).
  --
  -- Construction sketch (Stacks 04GF):
  -- * Given monic `g : Polynomial Cq` and `α ∈ Cq` with `g.eval α ∈ maximalIdeal Cq`
  --   and `IsUnit (g.derivative.eval α)`, form `C'_α := Cq[X] / (g) = Cq ⊗_{Cq[X]}
  --   AdjoinRoot g`. Since `g` is monic with `g'(α)` a unit at the seed, `C'_α`
  --   is étale over `Cq` near the seed; étale-over-Henselian + lying-over gives
  --   the Hensel-root in `Cq`.
  --
  -- Left as a typed sorry — the étale-lifting infrastructure is the residual gap.
  sorry

/-- **Helper B.3.a.i.α (substantive sub-helper, Step 5).** This is the truly
substantive residual gap (étale Hensel-uniqueness across the nilpotent
thickening `m · Bb`).

Given the primitive-element data of Helper B.1 plus an idempotent lift `e ∈ B`
isolating the `n`-factor of `B/mB ≃ ∏ k_i` (from
`exists_idempotent_lift_isolating_at_maximal`), the value `f(β)` vanishes in
every localization `Bb = B[1/(e · f'(β))]`.

The classical proof (Stacks 00U7 Step 3, blueprint `b := e · f'(β)`):

* In `Bb`, `b = e · f'(β)` is a unit, so both `e` and `f'(β)` are units
  (`isUnit_of_mul_isUnit_right`/`_left`).
* `e * e - e ∈ m · B` implies `e * e = e` mod `m · Bb`; combined with `e` a
  unit, `e = 1` in `Bb / m · Bb`.
* In `Bk = B/mB ≃ ∏ k_i`, `e · f(β)` lies only in the `i_n`-factor, where
  `f(β) = 0` (since `f(β) ∈ n` and the `i_n`-factor is `B/n`). Hence
  `e · f(β) ∈ m · B`.
* Push to `Bb`: `e · f(β) ∈ m · Bb`. Since `e = 1` mod `m · Bb`,
  `f(β) ∈ m · Bb`.
* Étale Hensel-uniqueness across the nilpotent thickening `m · Bb` pushes
  the mod-`m` vanishing up to `f(β) = 0` exactly.

The final step (étale-lifting across the nilpotent thickening) is the
substantive Mathlib gap. -/
private lemma aeval_f_eq_zero_in_localizationAway_of_etale
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (_h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (β : B) (f : Polynomial A) (_hf : f.Monic)
    (_hfβ : Polynomial.eval β (f.map (algebraMap A B)) ∈ n)
    (_hfdβ : Polynomial.eval β (f.derivative.map (algebraMap A B)) ∉ n)
    (e : B)
    (_he_idem :
      (e * e - e) ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (_he_notmem : e ∉ n)
    (_he_isolate : ∀ x : B, x ∈ n →
      e * x ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (_he_horizontal : ∀ p : Ideal B, p.IsPrime →
      ¬((IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ p) →
      e ∈ p) :
    ∃ s_B : B, s_B ∉ n ∧
      ∀ (Bb : Type u) [CommRing Bb] [Algebra B Bb]
        [IsLocalization.Away
          (e * Polynomial.eval β (f.derivative.map (algebraMap A B)) * s_B) Bb]
        [Algebra A Bb] [IsScalarTower A B Bb],
        ∃ β' : Bb,
          β' - algebraMap B Bb β ∈
            (IsLocalRing.maximalIdeal A).map (algebraMap A Bb) ∧
          Polynomial.aeval β' f = 0 ∧
          IsUnit (Polynomial.aeval β' f.derivative) := by
  -- iter-042 refactor: signature drops the consumer-supplied `Bb` head args.
  -- All Hensel-lifting now occurs inside an INTERNAL away-localization
  -- `Bb₀ := Localization.Away (e * f'(β))`; the outer `∃ s_B` selects a
  -- further-localization scalar via `IsLocalization.surj` so the inner
  -- `∀ Bb [Away (e * f'(β) * s_B) Bb]` instance has both `e * f'(β)` and
  -- `s_B` as units, enabling descent `Bb₀ → Bb` via `IsLocalization.Away.lift`.
  --
  -- Step 0. Internal away-localization Bb₀ = B[1/(e·f'(β))].
  let efβ : B := e * Polynomial.eval β (f.derivative.map (algebraMap A B))
  let Bb₀ : Type u := Localization.Away efβ
  haveI : IsScalarTower A B Bb₀ := .of_algebraMap_eq fun _ => rfl
  -- Step 1. `efβ` is a unit in Bb₀; hence both `e` and `f'(β)` are units.
  have hb_unit₀ : IsUnit (algebraMap B Bb₀ efβ) :=
    IsLocalization.Away.algebraMap_isUnit (S := Bb₀) _
  have hb_unit₀_mul :
      IsUnit (algebraMap B Bb₀ e *
        algebraMap B Bb₀
          (Polynomial.eval β (f.derivative.map (algebraMap A B)))) := by
    rw [← map_mul]; exact hb_unit₀
  have he_unit₀ : IsUnit (algebraMap B Bb₀ e) :=
    isUnit_of_mul_isUnit_left hb_unit₀_mul
  have _hfd_unit₀ : IsUnit (algebraMap B Bb₀
      (Polynomial.eval β (f.derivative.map (algebraMap A B)))) :=
    isUnit_of_mul_isUnit_right hb_unit₀_mul
  -- Step 2. From `_he_isolate _hfβ`: `e * f(β) ∈ m · B`.
  have h_efβ_in : e * Polynomial.eval β (f.map (algebraMap A B)) ∈
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B) : Ideal B) :=
    _he_isolate _ _hfβ
  -- Step 3. Push to Bb₀.
  have h_efβ_Bb₀_in :
      algebraMap B Bb₀ (e * Polynomial.eval β (f.map (algebraMap A B))) ∈
      ((IsLocalRing.maximalIdeal A).map (algebraMap A Bb₀) : Ideal Bb₀) := by
    have htower : (algebraMap A Bb₀ : A →+* Bb₀) =
        (algebraMap B Bb₀).comp (algebraMap A B) :=
      IsScalarTower.algebraMap_eq A B Bb₀
    rw [htower, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ h_efβ_in
  -- Step 4. Cancel `e`.
  rw [map_mul] at h_efβ_Bb₀_in
  have h_fβ_Bb₀_in :
      algebraMap B Bb₀ (Polynomial.eval β (f.map (algebraMap A B))) ∈
        ((IsLocalRing.maximalIdeal A).map (algebraMap A Bb₀) : Ideal Bb₀) := by
    rcases he_unit₀ with ⟨u, hu⟩
    have hrw :
        algebraMap B Bb₀ (Polynomial.eval β (f.map (algebraMap A B))) =
          (↑u⁻¹) *
            (algebraMap B Bb₀ e *
              algebraMap B Bb₀ (Polynomial.eval β (f.map (algebraMap A B)))) := by
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul]
    rw [hrw]
    exact Ideal.mul_mem_left _ _ h_efβ_Bb₀_in
  -- Step 5. Rewrite LHS as aeval.
  have hkey :
      algebraMap B Bb₀ (Polynomial.eval β (f.map (algebraMap A B))) =
        Polynomial.aeval (algebraMap B Bb₀ β) f := by
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def,
      Polynomial.eval_map]
  rw [hkey] at h_fβ_Bb₀_in
  -- Step 6. IsUnit (aeval ... f.derivative) in Bb₀.
  have hfd_unit_aeval₀ :
      IsUnit (Polynomial.aeval (algebraMap B Bb₀ β) f.derivative) := by
    have hkey_d :
        Polynomial.aeval (algebraMap B Bb₀ β) f.derivative =
          algebraMap B Bb₀
            (Polynomial.eval β (f.derivative.map (algebraMap A B))) := by
      rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def,
        Polynomial.eval_map]
    rw [hkey_d]
    exact _hfd_unit₀
  -- Step 7. `m · B ⊆ n` (from `_h`), and `efβ ∉ n`.
  have hmB_le_n :
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B) : Ideal B) ≤ n := by
    rw [Ideal.map_le_iff_le_comap, _h]
  have hb_notmem₀ : efβ ∉ n := by
    intro hmem
    rcases ‹n.IsMaximal›.isPrime.mem_or_mem hmem with h1 | h1
    · exact _he_notmem h1
    · exact _hfdβ h1
  have hn_disjoint : Disjoint (Submonoid.powers efβ : Set B) (n : Set B) := by
    rw [Set.disjoint_left]
    intro x hxp hxn
    obtain ⟨k, rfl⟩ := hxp
    exact hb_notmem₀ (‹n.IsMaximal›.isPrime.mem_of_pow_mem k hxn)
  -- Step 8. Define `nB := n.map (algebraMap B Bb₀)`. Its comap is `n` (since
  -- `n` is disjoint from the inverted submonoid), and it inherits primality
  -- and maximality from `n`.
  let nB : Ideal Bb₀ := n.map (algebraMap B Bb₀)
  have hcomap_nB : nB.comap (algebraMap B Bb₀) = n := by
    have hu := IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers efβ) Bb₀ (I := n) ‹n.IsMaximal›.isPrime hn_disjoint
    simpa [nB, Ideal.under] using hu
  haveI hnB_prime : nB.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers efβ) Bb₀ n ‹n.IsMaximal›.isPrime hn_disjoint
  haveI hnB_under_max : (nB.under B).IsMaximal := by
    show (Ideal.comap (algebraMap B Bb₀) nB).IsMaximal
    rw [hcomap_nB]; infer_instance
  haveI hnB_max : nB.IsMaximal :=
    Ideal.IsMaximal.of_isLocalization_of_disjoint (Submonoid.powers efβ)
  -- Step 9. `nB.comap (algebraMap A Bb₀) = m`.
  have hnB_comap_A : nB.comap (algebraMap A Bb₀) = IsLocalRing.maximalIdeal A := by
    have htower : (algebraMap A Bb₀ : A →+* Bb₀) =
        (algebraMap B Bb₀).comp (algebraMap A B) :=
      IsScalarTower.algebraMap_eq A B Bb₀
    rw [show (Ideal.comap (algebraMap A Bb₀) nB : Ideal A) =
          Ideal.comap (algebraMap A B) (Ideal.comap (algebraMap B Bb₀) nB) from by
        rw [htower, ← Ideal.comap_comap], hcomap_nB, _h]
  -- m.map (algebraMap A Bb₀) ⊆ nB (transport `m · B ⊆ n` along `algebraMap B Bb₀`).
  have hmBb₀_le_nB :
      ((IsLocalRing.maximalIdeal A).map (algebraMap A Bb₀) : Ideal Bb₀) ≤ nB := by
    have htower : (algebraMap A Bb₀ : A →+* Bb₀) =
        (algebraMap B Bb₀).comp (algebraMap A B) :=
      IsScalarTower.algebraMap_eq A B Bb₀
    rw [htower, ← Ideal.map_map]
    exact Ideal.map_mono hmB_le_n
  -- Step 10. Algebra.Etale instances on Bb₀ (auto + composition).
  haveI : Algebra.Etale B Bb₀ := Algebra.Etale.of_isLocalizationAway efβ
  haveI : Algebra.Etale A Bb₀ := Algebra.Etale.comp A B Bb₀
  -- Step 11. HenselianLocalRing on Bbn = Localization.AtPrime nB via §2 helper.
  haveI hHensBbn : HenselianLocalRing (Localization.AtPrime nB) :=
    henselianLocalRing_of_etale_atPrime nB hnB_comap_A
  -- Step 12. Hensel-lift seed = algebraMap Bb₀ Bbn (algebraMap B Bb₀ β) in Bbn.
  let Bbn : Type u := Localization.AtPrime nB
  haveI : IsScalarTower A Bb₀ Bbn := .of_algebraMap_eq fun _ => rfl
  let seed : Bbn := algebraMap Bb₀ Bbn (algebraMap B Bb₀ β)
  have h_aeval_in_nB :
      Polynomial.aeval (algebraMap B Bb₀ β) f ∈ nB :=
    hmBb₀_le_nB h_fβ_Bb₀_in
  have h_seed_in :
      Polynomial.aeval seed f ∈ IsLocalRing.maximalIdeal Bbn := by
    rw [show Polynomial.aeval seed f =
        algebraMap Bb₀ Bbn (Polynomial.aeval (algebraMap B Bb₀ β) f) from
        Polynomial.aeval_algebraMap_apply (B := Bbn) _ _]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Bbn nB _).mpr h_aeval_in_nB
  have h_seed_d_unit :
      IsUnit (Polynomial.aeval seed f.derivative) := by
    rw [show Polynomial.aeval seed f.derivative =
        algebraMap Bb₀ Bbn (Polynomial.aeval (algebraMap B Bb₀ β) f.derivative) from
        Polynomial.aeval_algebraMap_apply (B := Bbn) _ _]
    exact hfd_unit_aeval₀.map _
  let fBbn : Polynomial Bbn := f.map (algebraMap A Bbn)
  have hfBbn_monic : fBbn.Monic := _hf.map _
  have h_eval_seed :
      fBbn.eval seed = Polynomial.aeval seed f := by
    simp [fBbn, Polynomial.aeval_def, Polynomial.eval_map]
  have h_eval_seed_d :
      fBbn.derivative.eval seed = Polynomial.aeval seed f.derivative := by
    simp [fBbn, Polynomial.derivative_map, Polynomial.aeval_def, Polynomial.eval_map]
  obtain ⟨β'', hβ''_root, hβ''_close⟩ :=
    HenselianLocalRing.is_henselian fBbn hfBbn_monic seed
      (by rw [h_eval_seed]; exact h_seed_in)
      (by rw [h_eval_seed_d]; exact h_seed_d_unit)
  have h_aeval_β''_zero : Polynomial.aeval β'' f = 0 := by
    have : fBbn.eval β'' = Polynomial.aeval β'' f := by
      simp [fBbn, Polynomial.aeval_def, Polynomial.eval_map]
    rw [← this]; exact hβ''_root
  -- Step 13.a (mk'-extraction): β'' = mk' Bbn b₀ s₀ with s₀ ∈ nB.primeCompl.
  obtain ⟨b₀, s₀, hmk'⟩ :=
    IsLocalization.exists_mk'_eq (M := nB.primeCompl) (S := Bbn) β''
  -- Step 13.b (surj on Bb₀): project s₀.val ∈ Bb₀ down to B via the away
  -- localization. Result: `s₀.val * algebraMap B Bb₀ sm = algebraMap B Bb₀ s_B`
  -- for some `s_B : B` and `sm : Submonoid.powers efβ`.
  obtain ⟨⟨s_B, sm⟩, hsurj_eq⟩ :=
    IsLocalization.surj (M := Submonoid.powers efβ) (S := Bb₀) s₀.val
  -- Step 13.c (s_B ∉ n): the image `algebraMap B Bb₀ s_B = s₀.val * (unit) ∉ nB`
  -- by primality of nB and s₀.val ∉ nB. Pull back via hcomap_nB.
  have hsm_unit₀ : IsUnit (algebraMap B Bb₀ sm.val) := by
    obtain ⟨k, hk⟩ := sm.property
    rw [show sm.val = efβ ^ k from hk.symm, map_pow]
    exact hb_unit₀.pow k
  have hs₀_notmem : s₀.val ∉ nB := s₀.property
  have h_image_notmem : algebraMap B Bb₀ s_B ∉ nB := by
    rw [← hsurj_eq]
    intro hmem
    rcases hnB_prime.mem_or_mem hmem with h1 | h1
    · exact hs₀_notmem h1
    · exact hnB_prime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 hsm_unit₀)
  have hs_B_notmem : s_B ∉ n := by
    intro hs_B_n
    exact h_image_notmem (Ideal.mem_map_of_mem _ hs_B_n)
  -- Step 13.f.1 (transport `h_aeval_β''_zero` through `f.map (algebraMap A Bb₀)`).
  -- The polynomial `f : A[X]` evaluates the same whether seen over A or over Bb₀,
  -- by `Polynomial.aeval_map_algebraMap` in the tower `A → Bb₀ → Bbn`.
  have h_aeval_β''_zero' :
      Polynomial.aeval β'' (f.map (algebraMap A Bb₀)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact h_aeval_β''_zero
  -- Step 13.f.2 (apply `scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero`).
  -- Using `mk' Bbn b₀ s₀ = β''` (hmk'), we obtain
  -- `aeval (algebraMap Bb₀ Bbn b₀) (scaleRoots (f.map _) s₀.val) = 0` in Bbn.
  have h_scale_zero :
      Polynomial.aeval (algebraMap Bb₀ Bbn b₀)
        (Polynomial.scaleRoots (f.map (algebraMap A Bb₀)) s₀.val) = 0 := by
    apply scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero
    rw [hmk']
    exact h_aeval_β''_zero'
  -- Step 13.f.3 (extract `t ∈ nB.primeCompl`).
  -- By `aeval_algebraMap_apply`, the Step 2 conclusion reads
  -- `algebraMap Bb₀ Bbn (aeval b₀ q) = 0` in Bbn, where `q := scaleRoots (f.map _) s₀.val`.
  -- `IsLocalization.exists_of_eq` at `M := nB.primeCompl, S := Bbn` then yields
  -- `∃ t : nB.primeCompl, t.val * aeval b₀ q = 0` in Bb₀.
  have h_alg_zero :
      algebraMap Bb₀ Bbn
          (Polynomial.aeval b₀
            (Polynomial.scaleRoots (f.map (algebraMap A Bb₀)) s₀.val)) =
        algebraMap Bb₀ Bbn 0 := by
    rw [map_zero, ← h_scale_zero,
        Polynomial.aeval_algebraMap_apply (B := Bbn) b₀ _]
  obtain ⟨t, ht_eq⟩ :=
    IsLocalization.exists_of_eq (M := nB.primeCompl) (S := Bbn) h_alg_zero
  -- `ht_eq : t.val * aeval b₀ q = t.val * 0`, i.e. `t.val * aeval b₀ q = 0` in Bb₀.
  have ht_zero :
      t.val * Polynomial.aeval b₀
          (Polynomial.scaleRoots (f.map (algebraMap A Bb₀)) s₀.val) = 0 := by
    rw [ht_eq, mul_zero]
  -- Step 13.f.4 (project `t : Bb₀` down to `t_B : B`).
  obtain ⟨⟨t_B, tm⟩, ht_surj⟩ :=
    IsLocalization.surj (M := Submonoid.powers efβ) (S := Bb₀) t.val
  -- `tm` is a power of `efβ`, hence its image in Bb₀ is a unit.
  have htm_unit₀ : IsUnit (algebraMap B Bb₀ tm.val) := by
    obtain ⟨k, hk⟩ := tm.property
    rw [show tm.val = efβ ^ k from hk.symm, map_pow]
    exact hb_unit₀.pow k
  -- `t_B ∉ n` by the same primality argument as `s_B`.
  have h_image_t_notmem : algebraMap B Bb₀ t_B ∉ nB := by
    rw [← ht_surj]
    intro hmem
    rcases hnB_prime.mem_or_mem hmem with h1 | h1
    · exact t.property h1
    · exact hnB_prime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 htm_unit₀)
  have ht_B_notmem : t_B ∉ n := by
    intro h
    exact h_image_t_notmem (Ideal.mem_map_of_mem _ h)
  -- Step 13.d (RESTRUCTURED iter-043 — bind outer past Steps 13.f.1–4).
  -- Choose outer `s_B := s_B_init * t_B`. The product is outside the prime `n`
  -- since both factors are. The inner `∀ Bb [Away (efβ * (s_B_init * t_B)) Bb]`
  -- instance then provides `efβ`, `s_B_init`, `t_B` all as units in `Bb`.
  refine ⟨s_B * t_B, ?_, fun Bb _ _ _ _ _ => ?_⟩
  · -- `s_B_init * t_B ∉ n` by primality of `n`.
    intro hmem
    rcases ‹n.IsMaximal›.isPrime.mem_or_mem hmem with h | h
    · exact hs_B_notmem h
    · exact ht_B_notmem h
  -- Step 13.e (inner): destructure the away unit and lift Bb₀ → Bb.
  have hbsB_unit : IsUnit (algebraMap B Bb (efβ * (s_B * t_B))) :=
    IsLocalization.Away.algebraMap_isUnit (S := Bb) _
  rw [map_mul] at hbsB_unit
  have hefβ_unit_Bb : IsUnit (algebraMap B Bb efβ) :=
    isUnit_of_mul_isUnit_left hbsB_unit
  have hsBtB_unit_Bb_raw : IsUnit (algebraMap B Bb (s_B * t_B)) :=
    isUnit_of_mul_isUnit_right hbsB_unit
  rw [map_mul] at hsBtB_unit_Bb_raw
  have hs_B_unit_Bb : IsUnit (algebraMap B Bb s_B) :=
    isUnit_of_mul_isUnit_left hsBtB_unit_Bb_raw
  have ht_B_unit_Bb : IsUnit (algebraMap B Bb t_B) :=
    isUnit_of_mul_isUnit_right hsBtB_unit_Bb_raw
  -- Step 13.e' (lift Bb₀ → Bb): since `efβ` is a unit in Bb, the universal
  -- property of `Bb₀ = B[1/efβ]` yields `lift_Bb : Bb₀ →+* Bb` extending
  -- `algebraMap B Bb`.
  let lift_Bb : Bb₀ →+* Bb := IsLocalization.Away.lift (S := Bb₀) efβ hefβ_unit_Bb
  have h_lift_comp : lift_Bb.comp (algebraMap B Bb₀) = algebraMap B Bb :=
    IsLocalization.Away.lift_comp (S := Bb₀) (x := efβ) hefβ_unit_Bb
  -- Step 13.f.5 (build β' and verify three conclusions) — residual.
  -- Recipe (preserved verbatim for iter-044 closure):
  --   * Apply `lift_Bb` to `t.val * aeval b₀ q = 0` (Step 13.f.3 `ht_zero`):
  --     `lift_Bb t.val * lift_Bb (aeval b₀ q) = 0` in Bb.
  --   * `lift_Bb t.val` is a unit: by `ht_surj` and `h_lift_comp`,
  --     `lift_Bb t.val * algebraMap B Bb tm.val = algebraMap B Bb t_B`, with both
  --     `algebraMap B Bb tm.val` (power of `efβ`, image of unit) and
  --     `algebraMap B Bb t_B` (= `ht_B_unit_Bb`) units; hence so is `lift_Bb t.val`.
  --   * Cancel `lift_Bb t.val`: `lift_Bb (aeval b₀ q) = 0` in Bb.
  --   * `lift_Bb (aeval b₀ q) = aeval (lift_Bb b₀) (q.map lift_Bb)`
  --     by `Polynomial.aeval_algHom`/`eval_map`-style transport.
  --   * `q.map lift_Bb = scaleRoots (f.map (algebraMap A Bb)) (lift_Bb s₀.val)`
  --     by `Polynomial.scaleRoots_map` + `Polynomial.map_map` + `h_lift_comp` +
  --     `IsScalarTower.algebraMap_eq A B Bb`.
  --   * `lift_Bb s₀.val` is a unit in Bb: apply `lift_Bb` to `hsurj_eq`
  --     (`s₀.val * algebraMap B Bb₀ sm.val = algebraMap B Bb₀ s_B`), use
  --     `h_lift_comp` to rewrite the RHS as `algebraMap B Bb s_B` (a unit by
  --     `hs_B_unit_Bb`) and the LHS factor `lift_Bb (algebraMap B Bb₀ sm.val) =
  --     algebraMap B Bb sm.val` (a unit since `sm.val` is a power of `efβ`,
  --     image of a unit). Conclude `lift_Bb s₀.val` is a unit.
  --   * Set `β' := (lift_Bb s₀.val)⁻¹.val * lift_Bb b₀`. Then
  --     `lift_Bb b₀ = lift_Bb s₀.val * β'`, so by `Polynomial.scaleRoots_eval_mul`
  --     applied to `p := f.map (algebraMap A Bb)`, `r := β'`, `s := lift_Bb s₀.val`,
  --     `eval (lift_Bb s₀.val * β') (scaleRoots (f.map _) (lift_Bb s₀.val))
  --       = (lift_Bb s₀.val)^d * eval β' (f.map (algebraMap A Bb))`. The LHS is
  --     the `q.map lift_Bb` value at `lift_Bb b₀`, hence zero. The
  --     `(lift_Bb s₀.val)^d` factor is a unit, so `eval β' (f.map _) = 0`,
  --     i.e. `aeval β' f = 0` — conclusion (i).
  --   * Conclusion (ii) `β' - algebraMap B Bb β ∈ m·Bb`: derive from
  --     `hβ''_close : β'' - seed ∈ maximalIdeal Bbn` via `lift_Bb` transport
  --     (using `nB ⊇ m·Bb₀` from `hmBb₀_le_nB` and `hβ''_close`'s shape
  --     `mk' b₀ s₀ - algebraMap Bb₀ Bbn (algebraMap B Bb₀ β) ∈ maximalIdeal Bbn`).
  --   * Conclusion (iii) `IsUnit (aeval β' f.derivative)`: parallel to (i)
  --     using `f.derivative` and `hfd_unit_aeval₀` to transport unitness
  --     through `lift_Bb`.
  -- Convenience: lift_Bb collapses with `algebraMap B Bb₀ b` to `algebraMap B Bb b`.
  have h_lift_apply (b : B) : lift_Bb (algebraMap B Bb₀ b) = algebraMap B Bb b :=
    RingHom.congr_fun h_lift_comp b
  -- The images of `sm.val` and `tm.val` in `Bb` are units (powers of `efβ`).
  have hsm_unit_Bb : IsUnit (algebraMap B Bb sm.val) := by
    obtain ⟨k, hk⟩ := sm.property
    rw [show sm.val = efβ ^ k from hk.symm, map_pow]
    exact hefβ_unit_Bb.pow k
  have htm_unit_Bb : IsUnit (algebraMap B Bb tm.val) := by
    obtain ⟨k, hk⟩ := tm.property
    rw [show tm.val = efβ ^ k from hk.symm, map_pow]
    exact hefβ_unit_Bb.pow k
  -- Apply `lift_Bb` to `hsurj_eq` and `ht_surj` to get the Bb-level surj equations.
  have hsurj_Bb :
      lift_Bb s₀.val * algebraMap B Bb sm.val = algebraMap B Bb s_B := by
    have h := congrArg lift_Bb hsurj_eq
    rwa [map_mul, h_lift_apply, h_lift_apply] at h
  have ht_surj_Bb :
      lift_Bb t.val * algebraMap B Bb tm.val = algebraMap B Bb t_B := by
    have h := congrArg lift_Bb ht_surj
    rwa [map_mul, h_lift_apply, h_lift_apply] at h
  -- `lift_Bb s₀.val` is a unit in Bb (from `hsurj_Bb` + `hs_B_unit_Bb`).
  have hlift_s₀_unit : IsUnit (lift_Bb s₀.val) := by
    have hprod : IsUnit (lift_Bb s₀.val * algebraMap B Bb sm.val) :=
      hsurj_Bb ▸ hs_B_unit_Bb
    exact isUnit_of_mul_isUnit_left hprod
  -- `lift_Bb t.val` is a unit in Bb (from `ht_surj_Bb` + `ht_B_unit_Bb`).
  have hlift_t_unit : IsUnit (lift_Bb t.val) := by
    have hprod : IsUnit (lift_Bb t.val * algebraMap B Bb tm.val) :=
      ht_surj_Bb ▸ ht_B_unit_Bb
    exact isUnit_of_mul_isUnit_left hprod
  -- `algebraMap B Bb e` is a unit (`efβ = e * fdβ` and `hefβ_unit_Bb`).
  have he_unit_Bb : IsUnit (algebraMap B Bb e) := by
    have hprod :
        IsUnit (algebraMap B Bb e *
          algebraMap B Bb (Polynomial.eval β (f.derivative.map (algebraMap A B)))) := by
      rw [← map_mul]; exact hefβ_unit_Bb
    exact isUnit_of_mul_isUnit_left hprod
  -- `algebraMap B Bb fdβ` is a unit (right factor of `hefβ_unit_Bb`).
  have hfdβ_unit_Bb :
      IsUnit (algebraMap B Bb
        (Polynomial.eval β (f.derivative.map (algebraMap A B)))) := by
    have hprod :
        IsUnit (algebraMap B Bb e *
          algebraMap B Bb (Polynomial.eval β (f.derivative.map (algebraMap A B)))) := by
      rw [← map_mul]; exact hefβ_unit_Bb
    exact isUnit_of_mul_isUnit_right hprod
  -- Build β' := (lift_Bb s₀.val)⁻¹ * lift_Bb b₀.
  obtain ⟨u_s, hu_s⟩ := hlift_s₀_unit
  set β' : Bb := (u_s⁻¹ : Bbˣ).val * lift_Bb b₀ with β'_def
  -- Identity: `lift_Bb s₀.val * β' = lift_Bb b₀`.
  have h_s_mul_β' : lift_Bb s₀.val * β' = lift_Bb b₀ := by
    rw [β'_def, ← mul_assoc, ← hu_s]
    show (u_s : Bb) * (u_s⁻¹ : Bbˣ).val * lift_Bb b₀ = lift_Bb b₀
    rw [show ((u_s : Bb)) * (u_s⁻¹ : Bbˣ).val = 1 from u_s.mul_inv, one_mul]
  -- Step (d).1: Express β' - algebraMap B Bb β as `(unit) * lift_Bb (b₀ - s₀.val * β̃)`.
  have h_s_β_lift :
      lift_Bb s₀.val * algebraMap B Bb β =
        lift_Bb (s₀.val * algebraMap B Bb₀ β) := by
    rw [map_mul, h_lift_apply]
  have h_diff_form :
      β' - algebraMap B Bb β =
        (u_s⁻¹ : Bbˣ).val * lift_Bb (b₀ - s₀.val * algebraMap B Bb₀ β) := by
    have h1 : algebraMap B Bb β =
        (u_s⁻¹ : Bbˣ).val * (lift_Bb s₀.val * algebraMap B Bb β) := by
      rw [← hu_s, ← mul_assoc,
        show (u_s⁻¹ : Bbˣ).val * (u_s : Bb) = 1 from u_s.inv_mul, one_mul]
    rw [β'_def, h1, h_s_β_lift, map_sub, mul_sub]
  -- Step (d).3: `b₀ - s₀.val * algebraMap B Bb₀ β ∈ nB` via mk'_spec route.
  have h_sub_in_nB :
      b₀ - s₀.val * algebraMap B Bb₀ β ∈ nB := by
    -- `algebraMap _ Bbn s₀.val * (β'' - seed) = algebraMap _ Bbn (b₀ - s₀.val * algebraMap B Bb₀ β)`
    have h_seed_eq :
        seed = algebraMap Bb₀ Bbn (algebraMap B Bb₀ β) := rfl
    have h_calc :
        algebraMap Bb₀ Bbn (b₀ - s₀.val * algebraMap B Bb₀ β) =
          algebraMap Bb₀ Bbn s₀.val * (β'' - seed) := by
      rw [h_seed_eq, ← hmk', map_sub, mul_sub, mul_comm _ (IsLocalization.mk' _ _ _),
        IsLocalization.mk'_spec, map_mul]
    have h_in_max :
        algebraMap Bb₀ Bbn (b₀ - s₀.val * algebraMap B Bb₀ β) ∈
          IsLocalRing.maximalIdeal Bbn := by
      rw [h_calc]
      exact Ideal.mul_mem_left _ _ hβ''_close
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (S := Bbn) (I := nB) _).mp h_in_max
  -- Step (d).4: lift_Bb sends nB into n.map (algebraMap B Bb).
  have h_n_map_image :
      lift_Bb (b₀ - s₀.val * algebraMap B Bb₀ β) ∈
        (n.map (algebraMap B Bb) : Ideal Bb) := by
    have h_map_lift :
        (n.map (algebraMap B Bb₀)).map lift_Bb = n.map (algebraMap B Bb) := by
      rw [Ideal.map_map, h_lift_comp]
    rw [← h_map_lift]
    exact Ideal.mem_map_of_mem _ h_sub_in_nB
  -- Step (d).5: n.map (algebraMap B Bb) ⊆ m.map (algebraMap A Bb) via e-isolation.
  have h_n_map_le :
      (n.map (algebraMap B Bb) : Ideal Bb) ≤
        (IsLocalRing.maximalIdeal A).map (algebraMap A Bb) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hex_B : e * x ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) :=
      _he_isolate x hx
    have hex_Bb :
        algebraMap B Bb (e * x) ∈
          (IsLocalRing.maximalIdeal A).map (algebraMap A Bb) := by
      rw [show (algebraMap A Bb : A →+* Bb) =
            (algebraMap B Bb).comp (algebraMap A B) from
          IsScalarTower.algebraMap_eq A B Bb, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ hex_B
    obtain ⟨ue, hue⟩ := he_unit_Bb
    have heq :
        algebraMap B Bb x = (ue⁻¹ : Bbˣ).val * algebraMap B Bb (e * x) := by
      rw [map_mul, ← hue, ← mul_assoc,
        show (ue⁻¹ : Bbˣ).val * (ue : Bb) = 1 from ue.inv_mul, one_mul]
    rw [Ideal.mem_comap, heq]
    exact Ideal.mul_mem_left _ _ hex_Bb
  -- Conclusion (ii) — assembled at the outer scope for reuse in conclusion (iii).
  have h_diff_in_m :
      β' - algebraMap B Bb β ∈
        (IsLocalRing.maximalIdeal A).map (algebraMap A Bb) := by
    rw [h_diff_form]
    exact Ideal.mul_mem_left _ _ (h_n_map_le h_n_map_image)
  -- Assemble the existential.
  refine ⟨β', h_diff_in_m, ?_, ?_⟩
  · -- Conclusion (i): aeval β' f = 0.
    haveI hBb_nontriv : Nontrivial Bb := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      rw [IsLocalization.subsingleton_iff
        (M := Submonoid.powers (efβ * (s_B * t_B)))] at hsub
      obtain ⟨k, hk⟩ := hsub
      have hnotmem : efβ * (s_B * t_B) ∉ n := by
        intro hmem
        rcases ‹n.IsMaximal›.isPrime.mem_or_mem hmem with h1 | h2
        · exact hb_notmem₀ h1
        rcases ‹n.IsMaximal›.isPrime.mem_or_mem h2 with h2a | h2b
        · exact hs_B_notmem h2a
        · exact ht_B_notmem h2b
      have hpow_in : (efβ * (s_B * t_B))^k ∈ n := by
        change (fun x => (efβ * (s_B * t_B))^x) k ∈ n
        rw [hk]; exact Ideal.zero_mem _
      exact hnotmem (‹n.IsMaximal›.isPrime.mem_of_pow_mem k hpow_in)
    have h_fmap_eq :
        f.map (algebraMap A Bb) = (f.map (algebraMap A Bb₀)).map lift_Bb := by
      rw [Polynomial.map_map]
      congr 1
      rw [show (algebraMap A Bb₀ : A →+* Bb₀) =
            (algebraMap B Bb₀).comp (algebraMap A B) from
          IsScalarTower.algebraMap_eq A B Bb₀, ← RingHom.comp_assoc, h_lift_comp,
        ← IsScalarTower.algebraMap_eq A B Bb]
    have h_lc_eq : (f.map (algebraMap A Bb₀)).leadingCoeff = 1 :=
      (_hf.map (algebraMap A Bb₀))
    have h_leading_nonzero :
        lift_Bb ((f.map (algebraMap A Bb₀)).leadingCoeff) ≠ 0 := by
      rw [h_lc_eq, map_one]; exact one_ne_zero
    have h_q_map :
        ((f.map (algebraMap A Bb₀)).scaleRoots s₀.val).map lift_Bb =
          (f.map (algebraMap A Bb)).scaleRoots (lift_Bb s₀.val) := by
      rw [Polynomial.map_scaleRoots _ _ _ h_leading_nonzero, ← h_fmap_eq]
    have h_lift_t_aeval :
        lift_Bb t.val * lift_Bb (Polynomial.aeval b₀
          ((f.map (algebraMap A Bb₀)).scaleRoots s₀.val)) = 0 := by
      rw [← map_mul, ht_zero, map_zero]
    have h_lift_aeval :
        lift_Bb (Polynomial.aeval b₀
          ((f.map (algebraMap A Bb₀)).scaleRoots s₀.val)) = 0 :=
      hlift_t_unit.mul_left_cancel
        (by rw [mul_zero]; exact h_lift_t_aeval)
    have h_eval_lift :
        Polynomial.eval (lift_Bb b₀)
          (((f.map (algebraMap A Bb₀)).scaleRoots s₀.val).map lift_Bb) =
        lift_Bb (Polynomial.aeval b₀
          ((f.map (algebraMap A Bb₀)).scaleRoots s₀.val)) := by
      rw [Polynomial.eval_map, Polynomial.aeval_def, Algebra.algebraMap_self,
        Polynomial.hom_eval₂, RingHom.comp_id]
    have h_sr :
        Polynomial.eval (lift_Bb s₀.val * β')
            ((f.map (algebraMap A Bb)).scaleRoots (lift_Bb s₀.val)) =
          (lift_Bb s₀.val) ^ (f.map (algebraMap A Bb)).natDegree *
            Polynomial.eval β' (f.map (algebraMap A Bb)) :=
      Polynomial.scaleRoots_eval_mul (f.map (algebraMap A Bb)) β' (lift_Bb s₀.val)
    rw [h_s_mul_β'] at h_sr
    rw [← h_q_map, h_eval_lift, h_lift_aeval] at h_sr
    have h_d_unit :
        IsUnit ((lift_Bb s₀.val) ^ (f.map (algebraMap A Bb)).natDegree) :=
      (hu_s ▸ u_s.isUnit : IsUnit (lift_Bb s₀.val)).pow _
    have h_eval_zero :
        Polynomial.eval β' (f.map (algebraMap A Bb)) = 0 := by
      apply h_d_unit.mul_left_cancel
      rw [mul_zero]; exact h_sr.symm
    rw [show Polynomial.aeval β' f = Polynomial.eval β' (f.map (algebraMap A Bb)) from by
      rw [Polynomial.aeval_def, Polynomial.eval_map]]
    exact h_eval_zero
  · -- Conclusion (iii): IsUnit (aeval β' f.derivative).
    -- Decompose `aeval β' f.derivative = algebraMap B Bb fdβ + δ` with `δ ∈ m·Bb`.
    set p : Polynomial Bb := f.derivative.map (algebraMap A Bb) with hp_def
    have h_aeval_eq_eval :
        Polynomial.aeval β' f.derivative = Polynomial.eval β' p := by
      rw [hp_def, Polynomial.aeval_def, Polynomial.eval_map]
    have h_eval_β_lift :
        Polynomial.eval (algebraMap B Bb β) p =
          algebraMap B Bb
            (Polynomial.eval β (f.derivative.map (algebraMap A B))) := by
      rw [hp_def,
        show (algebraMap A Bb : A →+* Bb) =
            (algebraMap B Bb).comp (algebraMap A B) from
          IsScalarTower.algebraMap_eq A B Bb, ← Polynomial.map_map,
        Polynomial.eval_map]
      exact Polynomial.eval₂_hom (algebraMap B Bb) β
    set δ : Bb := Polynomial.eval β' p - Polynomial.eval (algebraMap B Bb β) p with δ_def
    have h_dvd : β' - algebraMap B Bb β ∣ δ :=
      Polynomial.sub_dvd_eval_sub β' (algebraMap B Bb β) p
    have h_δ_in_m :
        δ ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A Bb) := by
      obtain ⟨c, hc⟩ := h_dvd
      rw [hc]
      exact Ideal.mul_mem_right _ _ h_diff_in_m
    have h_aeval_decomp :
        Polynomial.aeval β' f.derivative =
          algebraMap B Bb
            (Polynomial.eval β (f.derivative.map (algebraMap A B))) + δ := by
      rw [h_aeval_eq_eval, ← h_eval_β_lift, δ_def]; ring
    rw [h_aeval_decomp]
    -- iter-045 close (iii): apply the shared Jacobson-containment helper
    -- `m_map_le_jacobson_of_etale_isolating`. With `v + δ` where `v` is a unit
    -- and `δ ∈ Jacobson Bb`, factor `v + δ = v * (1 + δ * v⁻¹)`; the second
    -- factor is a unit by `Ideal.mem_jacobson_bot` (since `δ * v⁻¹ ∈ Jacobson`).
    have hb_outer_notmem : efβ * (s_B * t_B) ∉ n := by
      intro hmem
      rcases ‹n.IsMaximal›.isPrime.mem_or_mem hmem with h1 | h2
      · exact hb_notmem₀ h1
      rcases ‹n.IsMaximal›.isPrime.mem_or_mem h2 with h2a | h2b
      · exact hs_B_notmem h2a
      · exact ht_B_notmem h2b
    have he_div_b : e ∣ (efβ * (s_B * t_B)) := by
      show e ∣
        (e * Polynomial.eval β (f.derivative.map (algebraMap A B)) * (s_B * t_B))
      rw [mul_assoc]; exact dvd_mul_right _ _
    have h_jacob :
        ((IsLocalRing.maximalIdeal A).map (algebraMap A Bb) : Ideal Bb) ≤
          Ideal.jacobson (⊥ : Ideal Bb) :=
      m_map_le_jacobson_of_etale_isolating n _h e _he_idem _he_notmem _he_isolate
        _he_horizontal (efβ * (s_B * t_B)) hb_outer_notmem he_div_b Bb
    have h_δ_jacob : δ ∈ Ideal.jacobson (⊥ : Ideal Bb) := h_jacob h_δ_in_m
    obtain ⟨u, hu⟩ := hfdβ_unit_Bb
    let vinv : Bb := (u⁻¹ : Bbˣ).val
    have hv_mul_inv : (u : Bb) * vinv = 1 := u.mul_inv
    have h_one_plus : IsUnit (δ * vinv + 1) :=
      (Ideal.mem_jacobson_bot.mp h_δ_jacob) _
    have h_eq :
        algebraMap B Bb (Polynomial.eval β (f.derivative.map (algebraMap A B))) + δ =
          (u : Bb) * (δ * vinv + 1) := by
      rw [← hu]
      linear_combination -δ * hv_mul_inv
    rw [h_eq]
    exact u.isUnit.mul h_one_plus

/-- **Helper B.3.a.i (sub-helper, Steps 1–6).** With `b := e · f'(β)` (the
blueprint's choice, repaired from the iter-034 unsound `b := f'(β)`), the
`HasMap` data for `(standardEtalePairOfMonic f hf)` at `algebraMap B Bb β`
holds in every localization `Bb = B[1/b]`:

* `f(β) = 0` (substantive — delegated to
  `aeval_f_eq_zero_in_localizationAway_of_etale`),
* `f'(β)` is a unit, deduced from `b = e · f'(β)` being a unit in `Bb`
  (`IsLocalization.Away.algebraMap_isUnit`) plus "divisors of a unit are
  units" (`isUnit_of_mul_isUnit_right`).

The idempotent `e` comes from `exists_idempotent_lift_isolating_at_maximal`
(structural typed sorry tracking the bijection
`{primes of B over m} ↔ I`). -/
private lemma exists_etale_witness_for_standardEtalePair
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (β : B) (f : Polynomial A) (hf : f.Monic)
    (hfβ : Polynomial.eval β (f.map (algebraMap A B)) ∈ n)
    (hfdβ : Polynomial.eval β (f.derivative.map (algebraMap A B)) ∉ n) :
    ∃ e : B,
      e ∉ n ∧
      (e * e - e) ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) ∧
      (∀ x : B, x ∈ n →
        e * x ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) ∧
      (∀ p : Ideal B, p.IsPrime →
        ¬((IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ p) →
        e ∈ p) ∧
      (e * Polynomial.eval β (f.derivative.map (algebraMap A B))) ∉ n ∧
      ∃ s_B : B, s_B ∉ n ∧
      ∀ (Bb : Type u) [CommRing Bb] [Algebra B Bb]
        [IsLocalization.Away
          (e * Polynomial.eval β (f.derivative.map (algebraMap A B)) * s_B) Bb]
        [Algebra A Bb] [IsScalarTower A B Bb],
        ∃ β' : Bb,
          β' - algebraMap B Bb β ∈
            (IsLocalRing.maximalIdeal A).map (algebraMap A Bb) ∧
          Polynomial.aeval β' f = 0 ∧
          IsUnit (Polynomial.aeval β' f.derivative) := by
  -- Step 1. Extract the strengthened idempotent lift (iter-046: 5-tuple).
  obtain ⟨e, he_notmem, he_idem, he_isolate, he_horizontal⟩ :=
    exists_idempotent_lift_isolating_at_maximal (A := A) (B := B) n h
  -- Step 2 (iter-042). Extract the §3 outer existential: `∃ s_B ∈ B \ n` plus
  -- the per-`Bb` Hensel descent in any `Bb [Away (e * f'(β) * s_B) Bb]`.
  obtain ⟨s_B, hs_B_notmem, hwit⟩ :=
    aeval_f_eq_zero_in_localizationAway_of_etale (A := A) (B := B)
      n h β f hf hfβ hfdβ e he_idem he_notmem he_isolate he_horizontal
  refine ⟨e, he_notmem, he_idem, he_isolate, he_horizontal, ?_,
    s_B, hs_B_notmem, fun Bb _ _ _ _ _ => ?_⟩
  · -- `e * f'(β) ∉ n`: both factors are outside the prime `n`.
    intro hmem
    rcases (‹n.IsMaximal›.isPrime.mem_or_mem hmem) with h1 | h1
    · exact he_notmem h1
    · exact hfdβ h1
  · -- Inner ∀ Bb: delegate to §3's per-Bb witness.
    exact hwit Bb

/-- **Helper B.3.a.ii (sub-helper, Step 8).** Surjectivity of the lifted
`ψ : P.Ring →ₐ[A] Bb` from `_P.lift`. The image of `ψ` contains
`algebraMap B Bb β` (the image of `_P.X`) and all of `algebraMap A Bb`.
Modulo `m · Bb`, the image surjects onto `Bb / m · Bb` (since the
projection to the `i₀`-factor of `Bk = B/mB` is generated by the image of
`β` and `A/m`, by primitive-element data). Nakayama (using the
iter-045 Jacobson-containment hypothesis `_h_m_jacob`, derived by the
caller via `m_map_le_jacobson_of_etale_isolating`) then forces the image
to be all of `Bb`.

iter-045 REFACTOR: signature gains the `_h_m_jacob` hypothesis (single
additional hypothesis, authorized by the iter-045 directive). The body
remains a typed `sorry` — the substantive residual is now the
primitive-element-on-`Bb/m·Bb` step (`image(ψ) + m·Bb = ⊤`), conjoined
with `_h_m_jacob` via `Submodule.le_of_le_smul_of_le_jacobson_bot`. -/
private lemma surjective_standardEtalePair_lift_of_etale
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (_h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (β : B) (f : Polynomial A) (hf : f.Monic)
    (_hfβ : Polynomial.eval β (f.map (algebraMap A B)) ∈ n)
    (_hfdβ : Polynomial.eval β (f.derivative.map (algebraMap A B)) ∉ n)
    (e : B)
    (_he_idem : (e * e - e) ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (_he_notmem : e ∉ n)
    (_he_isolate : ∀ x : B, x ∈ n →
      e * x ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (_he_horizontal : ∀ p : Ideal B, p.IsPrime →
      ¬((IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ p) →
      e ∈ p)
    (_s_B : B)
    (Bb : Type u) [CommRing Bb] [Algebra B Bb]
    [IsLocalization.Away
      (e * Polynomial.eval β (f.derivative.map (algebraMap A B)) * _s_B) Bb]
    [Algebra A Bb] [IsScalarTower A B Bb]
    (β' : Bb)
    (_hβ'_lift : β' - algebraMap B Bb β ∈
      (IsLocalRing.maximalIdeal A).map (algebraMap A Bb))
    (ψ : (standardEtalePairOfMonic f hf).Ring →ₐ[A] Bb)
    (_hψ_X : ψ (standardEtalePairOfMonic f hf).X = β')
    (_h_m_jacob :
      ((IsLocalRing.maximalIdeal A).map (algebraMap A Bb) : Ideal Bb) ≤
        Ideal.jacobson (⊥ : Ideal Bb)) :
    Function.Surjective ψ := by
  -- iter-045 partial: route through `AlgHom.range_eq_top`, then focus the
  -- residual sorry on the primitive-element step
  -- `⊤ ≤ ψ.range.toSubmodule ⊔ (m·Bb) • ⊤` (as A-submodules of `Bb`).
  --
  -- With that step in place, the Nakayama close uses
  -- `Submodule.le_of_le_smul_of_le_jacobson_bot` (`R := Bb`, `M := Bb`),
  -- exploiting `_h_m_jacob`. The substantive gap is the primitive-element
  -- claim itself: `Bb / m·Bb ≃ k_{i_n}` (the i_n-factor of `B/mB ≃ ∏ k_i`),
  -- and the image `image(ψ)` contains `algebraMap A Bb` (reducing to `k`)
  -- and `β'` (reducing to a primitive element of `k_{i_n}` over `k`).
  -- iter-046+ target: identify `Bb/m·Bb = k_{i_n}` via the `e`-isolation and
  -- formalize the primitive-element image fact, then thread through Nakayama.
  classical
  rw [← AlgHom.range_eq_top]
  -- iter-047 Step 2a — image-covers-A: `algebraMap A Bb a ∈ ψ.range` for all `a`.
  have h_A_in_S : ∀ a : A, algebraMap A Bb a ∈ ψ.range :=
    fun a => ψ.range.algebraMap_mem a
  -- iter-047 Step 2b — image-covers-β': `β' ∈ ψ.range` (via `_hψ_X`).
  have h_X_in_S : β' ∈ ψ.range :=
    _hψ_X ▸ AlgHom.mem_range_self ψ (standardEtalePairOfMonic f hf).X
  -- iter-047 Step 2c — image-covers-f'(β'): any polynomial in `β'` with `A`-coefficients
  -- lies in `ψ.range`; in particular `Polynomial.aeval β' f.derivative ∈ ψ.range`.
  have h_fdβ'_in_S : Polynomial.aeval β' f.derivative ∈ ψ.range := by
    refine ⟨Polynomial.aeval (standardEtalePairOfMonic f hf).X f.derivative, ?_⟩
    have h := Polynomial.aeval_algHom (R := A) ψ (standardEtalePairOfMonic f hf).X
    have h' := congrArg (fun g : _ →ₐ[A] _ => g f.derivative) h
    -- `h' : Polynomial.aeval (ψ P.X) f.derivative = ψ (Polynomial.aeval P.X f.derivative)`
    simp only at h'
    rw [_hψ_X] at h'
    exact h'.symm
  -- iter-047 Step 1 — étale-product decomposition setup. The classical proof of
  -- Stacks 00U7 Step 8 uses the étale decomposition `B ⊗_A k ≃ ∏_i k_i` (each
  -- `k_i` finite separable over `k = A/m`) and identifies `Bb/(m·Bb)` with the
  -- `i_n`-factor `k_{i_n}` (via the localization-at-the-idempotent `Pi.single i_n 1`).
  -- We set up the decomposition here for use in the residue identification.
  haveI hBkEt : Algebra.Etale (IsLocalRing.ResidueField A)
      (TensorProduct A (IsLocalRing.ResidueField A) B) :=
    Algebra.Etale.baseChange A B (IsLocalRing.ResidueField A)
  obtain ⟨I, hIfin, kI, hKfield, hKalg, eqv, hKsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := IsLocalRing.ResidueField A)
      (A := TensorProduct A (IsLocalRing.ResidueField A) B)).mp inferInstance
  letI : Finite I := hIfin
  letI : Fintype I := Fintype.ofFinite I
  letI : ∀ i, Field (kI i) := hKfield
  letI : ∀ i, Algebra (IsLocalRing.ResidueField A) (kI i) := hKalg
  -- iter-047 Step 3+4 substantive residual. With the witnesses `h_A_in_S`,
  -- `h_X_in_S`, `h_fdβ'_in_S` and the étale decomposition `eqv` in hand, the
  -- remaining work decomposes as:
  --
  -- (i) Residue identification `Bb/(m·Bb) ≃ k_{i_n}` (the `i_n`-factor of
  --     `B/mB ≃ ∏ k_i`), via the localization-quotient commutation:
  --     `Bb/(m·Bb) ≃ (B/mB)[1/b̄] ≃ (∏ k_i)[1/b̄]`. The image of
  --     `b := e * f'(β) * s_B` in `B/mB ≃ ∏ k_i` projects to a component
  --     supported only at `i_n` (since `e` is the `i_n`-isolating idempotent
  --     and the other factors `f'(β)`, `s_B` are non-zero divisors there).
  --     Localizing at such an element collapses to the `i_n`-factor.
  --
  -- (ii) Image-covers-residue: the composite `ψ.range ↪ Bb ↠ Bb/(m·Bb) ≃ k_{i_n}`
  --      is surjective, since `β'` reduces (via `_hβ'_lift`) to the image of
  --      `β` in `k_{i_n}`, which is a primitive element of `k_{i_n}` over `k`
  --      by Helper B.1.
  --
  -- (iii) A-submodule equality `ψ.range.toSubmodule + (m·Bb) = ⊤` in `Bb`,
  --       directly from (ii).
  --
  -- (iv) Nakayama close: combine (iii) with `_h_m_jacob` to conclude
  --      `ψ.range = ⊤`. The standard Mathlib lemma
  --      `Submodule.le_of_le_smul_of_le_jacobson_bot` requires the larger
  --      submodule (i.e. `⊤`) to be finitely generated; here `Bb` is NOT
  --      finite over `A`, so the close needs an étale-Nakayama variant
  --      (e.g. "A-subalgebra-Nakayama for finite-type étale extensions").
  --
  -- Steps (i)–(iv) require infrastructure not present in Mathlib at iter-047
  -- (the localization-of-products-of-fields hook, the primitive-element-on-
  -- localization fact, and the étale-Nakayama variant). iter-048 refactor
  -- subagent target. The structural witnesses above (`h_A_in_S`, `h_X_in_S`,
  -- `h_fdβ'_in_S`, `eqv`, `hKsep`) preserve all reusable scaffolding.
  --
  -- ============================================================
  -- iter-048: substantive scaffolding for Steps (i)–(iv).
  --
  -- The §5 body is decomposed into four named sub-claims, each typed
  -- inline. The deepest residuals (residue identification + étale-Hensel
  -- close) are tagged as Gap A / Gap B respectively and are the
  -- Mathlib-PR-quality content to extract in iter-049+ refactor.
  -- ============================================================
  --
  -- Step (i.a). Set up the mod-m ideal of `Bb`.
  let mBb : Ideal Bb := (IsLocalRing.maximalIdeal A).map (algebraMap A Bb)
  -- Step (i.b). Note the propagated Jacobson-containment hypothesis.
  have _h_mBb_jacob : mBb ≤ Ideal.jacobson (⊥ : Ideal Bb) := _h_m_jacob
  -- Step (ii). The composite `ψ̄ : P.Ring →+* (Bb ⧸ mBb)` is surjective.
  --
  -- Substantive Stacks 00U7 Step 8 content. Two sub-claims fuse here:
  -- (1) Gap A: `Bb ⧸ mBb` is a finite separable field extension of
  --     `k := A/m`, identified with the `i_n`-factor `k_{i_n}` of the
  --     étale-product decomposition `eqv : B ⊗_A k ≃ ∀ i, kI i`. The
  --     identification uses the idempotent isolation in `e` (from
  --     `exists_idempotent_lift_isolating_at_maximal`) plus localization-
  --     quotient commutation at the inverted element `e * f'(β) * s_B`.
  -- (2) Primitive-element image: the image of `(standardEtalePairOfMonic f hf).X`
  --     under `ψ̄` is the residue of `β'`; by `_hβ'_lift` this equals the
  --     residue of `β`, which is a primitive element of `k_{i_n}` over `k`
  --     (Helper B.1 / `exists_lift_separablePrimitiveElement_of_etale_at_maxIdeal`).
  --     Combined with the ring-hom image containing `algebraMap A Bk'`, the
  --     image equals `k_{i_n} = Bb ⧸ mBb`.
  have h_ψ_bar_surj :
      Function.Surjective ((Ideal.Quotient.mk mBb).comp ψ.toRingHom) := by
    -- ============================================================
    -- iter-049 Gap A substantive scaffolding (Minimum-band attempt).
    --
    -- Decomposition into named sub-claims:
    --   (S1) Residue commutation: `mk_mBb (ψ P.X) = mk_mBb β'`.
    --   (S2) Residue identity: `mk_mBb β' = mk_mBb (algebraMap B Bb β)`
    --        (from `_hβ'_lift`).
    --   (S3) Range contains `mk_mBb (algebraMap A Bb a)` for every `a : A`.
    --   (S4) Range contains `mk_mBb (aeval β' p)` for every `p : A[X]`
    --        (polynomial expressions in `β'` with `A`-coefficients).
    --   (S5) `e` is a unit in `Bb` (divides the inverted element of the
    --        `IsLocalization.Away` instance).
    --   (S6) `n.map (algebraMap B Bb) ≤ mBb`, via `_he_isolate` + (S5).
    --   (S7) Gap A residue identification + primitive-element image
    --        (typed sub-sorry; Pi-localization collapse).
    -- ============================================================
    -- (S1) Residue commutation: image of `P.X` under `ψ̄` is `mk_mBb β'`.
    have h_r_X :
        (Ideal.Quotient.mk mBb) (ψ (standardEtalePairOfMonic f hf).X) =
          (Ideal.Quotient.mk mBb) β' := by
      rw [_hψ_X]
    -- (S2) Residues of `β'` and `algebraMap B Bb β` agree in `Bb ⧸ mBb`.
    have h_β'_β : (Ideal.Quotient.mk mBb) β' =
        (Ideal.Quotient.mk mBb) (algebraMap B Bb β) := by
      rw [eq_comm, Ideal.Quotient.eq]
      rw [show algebraMap B Bb β - β' = -(β' - algebraMap B Bb β) from by ring]
      exact mBb.neg_mem _hβ'_lift
    -- (S3) Range contains residues of `algebraMap A Bb`.
    have h_r_A : ∀ a : A,
        (Ideal.Quotient.mk mBb) ((algebraMap A Bb) a) ∈
          ((Ideal.Quotient.mk mBb).comp ψ.toRingHom).range := by
      intro a
      refine ⟨(algebraMap A (standardEtalePairOfMonic f hf).Ring) a, ?_⟩
      show (Ideal.Quotient.mk mBb) (ψ ((algebraMap A _) a)) = _
      rw [ψ.commutes]
    -- (S4) Range contains residues of every polynomial in `β'` over `A`.
    have h_r_poly : ∀ (p : Polynomial A),
        (Ideal.Quotient.mk mBb) (Polynomial.aeval β' p) ∈
          ((Ideal.Quotient.mk mBb).comp ψ.toRingHom).range := by
      intro p
      refine ⟨Polynomial.aeval (standardEtalePairOfMonic f hf).X p, ?_⟩
      show (Ideal.Quotient.mk mBb)
          (ψ (Polynomial.aeval (standardEtalePairOfMonic f hf).X p)) = _
      rw [← Polynomial.aeval_algHom_apply, _hψ_X]
    -- (S5) `algebraMap B Bb e` is a unit in `Bb`: it divides the inverted
    -- element `e * f'(β) * _s_B` of the `IsLocalization.Away` instance.
    have he_unit_Bb : IsUnit (algebraMap B Bb e) := by
      have h_b_unit : IsUnit (algebraMap B Bb
          (e * Polynomial.eval β (f.derivative.map (algebraMap A B)) * _s_B)) :=
        IsLocalization.Away.algebraMap_isUnit (S := Bb) _
      refine isUnit_of_dvd_unit ?_ h_b_unit
      rw [show (e * Polynomial.eval β (f.derivative.map (algebraMap A B)) * _s_B) =
              e * (Polynomial.eval β (f.derivative.map (algebraMap A B)) * _s_B)
            from by ring, map_mul]
      exact dvd_mul_right _ _
    -- (S6) For every `x ∈ n`, `algebraMap B Bb x ∈ mBb`. Uses `_he_isolate`
    -- to lift `e * x ∈ m·B`, plus (S5) to "divide out" the unit `e`.
    have h_mB_map_eq :
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).map (algebraMap B Bb)
          = mBb := by
      show ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).map (algebraMap B Bb) =
        (IsLocalRing.maximalIdeal A).map (algebraMap A Bb)
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A B Bb]
    have h_mB_map_le_mBb :
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).map (algebraMap B Bb)
          ≤ mBb := h_mB_map_eq.le
    have h_n_in_mBb : ∀ x : B, x ∈ n → algebraMap B Bb x ∈ mBb := by
      intro x hx
      have h_ex_in_mB := _he_isolate x hx
      have h_aex_in_mBb : algebraMap B Bb (e * x) ∈ mBb :=
        h_mB_map_le_mBb (Ideal.mem_map_of_mem _ h_ex_in_mB)
      obtain ⟨u, hu⟩ := he_unit_Bb
      have key : algebraMap B Bb x = (↑u⁻¹ : Bb) * algebraMap B Bb (e * x) := by
        rw [map_mul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
      rw [key]
      exact mBb.mul_mem_left _ h_aex_in_mBb
    -- (S7) Gap A residue identification + primitive-element image
    -- (iter-050+ Mathlib-PR target).
    --
    -- The remaining substantive content: identify `Bb ⧸ mBb` with `k_{i_n}`,
    -- the i_n-factor of the étale-product decomposition
    -- `eqv : k ⊗_A B ≃ ∀ i, kI i` (with `k := ResidueField A`,
    -- `kI i` finite separable over `k`). Steps:
    --
    --   (a) Quotient-localization commutation: `Bb ⧸ mBb ≃ (B ⧸ mB)[1/b̄]`,
    --       where `b̄` is the image of `e * f'(β) * _s_B` in `B ⧸ mB`.
    --   (b) Étale-decomposition transfer: `B ⧸ mB ≃ ∀ i, kI i` via `eqv`.
    --   (c) Pi-localization collapse: under `eqv`, the image of `e` projects
    --       to the idempotent `Pi.single i_n 1` (where `i_n` is the index
    --       corresponding to `n`, via the bijection
    --       `{primes of B over m} ↔ I`); hence `(∀ i, kI i)[1/eqv(b̄)]
    --       ≃ kI i_n`.
    --   (d) Primitive-element generation: the residue of `β` in `kI i_n`
    --       (= `B ⧸ n` via the étale-product decomposition) generates `kI i_n`
    --       over `k`, by Helper B.1 / the primitive-element data.
    --
    -- With (a)-(d) in hand, surjectivity follows: every element of
    -- `Bb ⧸ mBb ≃ kI i_n` is a polynomial in residue(β) = residue(β') with
    -- `k`-coefficients (= `A/m`-residues, in (S3)). Combined with (S4)
    -- (polynomials in β' with `A`-coefficients in the range), this gives
    -- the conclusion.
    --
    -- Authorized helper-file extraction:
    -- `Proetale/Mathlib/RingTheory/Localization/AtIdempotent.lean` for the
    -- Pi-localization collapse (step (c)).
    -- ============================================================
    -- iter-051 wiring (Acceptable band).
    --
    -- The substantive Stacks 00U7 Step 8 content (Steps A-D) is bundled
    -- into the polynomial-lift surjectivity claim `h_polylift`: every
    -- residue in `Bb ⧸ mBb` is the image of a polynomial in `β'` with
    -- coefficients in `A`. Concretely the four bridging sub-steps are:
    --
    --   (A) Quotient-localization commutation:
    --       `Bb ⧸ mBb ≃ Localization.Away (mk_mB b₀)`,
    --       where `b₀ = e * f'(β) * _s_B` is the inverted element of
    --       the `IsLocalization.Away` instance and `mk_mB b₀ ∈ B ⧸ mB`
    --       its image.
    --   (B) Étale-decomposition transfer via the existing `eqv`:
    --       `B ⧸ mB ≃ ∀ i, kI i` (over `k := ResidueField A`), through
    --       the canonical iso `(B ⊗_A k) ≃ (B ⧸ mB)` + `eqv`.
    --   (C) Pi-localization collapse via the iter-050 Mathlib-PR helper
    --       `Localization.Away_pi_field_supportedAt` from
    --       `Proetale/Mathlib/RingTheory/Localization/AtIdempotent.lean`:
    --       `(∀ i, kI i)[1/r̄] ≃ kI i_n`, where `i_n ∈ I` is the index
    --       corresponding to `n` via the bijection
    --       {primes of B over m} ↔ I. The support data `r̄ i_n ≠ 0`
    --       (resp. `r̄ i = 0` for `i ≠ i_n`) comes from `_he_notmem` and
    --       `_hfdβ` (resp. `_he_isolate` via the étale transfer).
    --   (D) Primitive-element image: residue of `β` generates `kI i_n`
    --       over `k`, via `hKsep i_n` and Helper B.1.
    --
    -- Combining (A)-(D), every residue is a `k`-polynomial in residue β';
    -- lifting `k = A/m`-coefficients to `A`-coefficients (using
    -- `Ideal.Quotient.mk_surjective`) yields the polynomial-lift claim.
    --
    -- The (C1) `i_n`-identification step requires the bijection
    -- {primes of B over m} ↔ I, which is HenselianPair-idempotent-
    -- bijection content (Stacks 04GG / 0DXB) deferred to iter-052+.
    -- The entire `h_polylift` claim is the single typed sub-sorry
    -- tagged accordingly.
    have h_polylift : ∀ y : Bb,
        ∃ p : Polynomial A,
          Ideal.Quotient.mk mBb y =
            Ideal.Quotient.mk mBb (Polynomial.aeval β' p) := by
      -- iter-052+ HenselianPair-idempotent-bijection target.
      sorry
    -- Polynomial lifting through `ψ`: every residue of `Bb ⧸ mBb`,
    -- being a residue of `Polynomial.aeval β' p` (by `h_polylift`), is
    -- the image of `Polynomial.aeval (standardEtalePairOfMonic f hf).X p`
    -- under the composite `(Ideal.Quotient.mk mBb).comp ψ.toRingHom`
    -- (via `_hψ_X` and `Polynomial.aeval_algHom_apply`).
    intro y
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpy⟩ := h_polylift b
    refine ⟨Polynomial.aeval (standardEtalePairOfMonic f hf).X p, ?_⟩
    show (Ideal.Quotient.mk mBb)
        (ψ (Polynomial.aeval (standardEtalePairOfMonic f hf).X p)) = y
    rw [← Polynomial.aeval_algHom_apply, _hψ_X, ← hpy]
    exact hb
  -- Step (iii). Recast Step (ii) as an additive decomposition on `Bb`.
  --
  -- For every `b : Bb`, there is `p : P.Ring` and `δ ∈ mBb` with `b = ψ p + δ`.
  -- This is a mechanical consequence of `h_ψ_bar_surj`: the residue of `b`
  -- is hit by `ψ̄ p` for some `p`, so `b - ψ p` lies in `mBb`.
  have h_decompose : ∀ b : Bb,
      ∃ p : (standardEtalePairOfMonic f hf).Ring, ∃ δ ∈ mBb, b = ψ p + δ := by
    intro b
    obtain ⟨p, hp⟩ := h_ψ_bar_surj (Ideal.Quotient.mk mBb b)
    refine ⟨p, b - ψ p, ?_, by ring⟩
    have hsub : (Ideal.Quotient.mk mBb) (b - ψ p) = 0 := by
      rw [map_sub]
      have hpres : (Ideal.Quotient.mk mBb) (ψ p) =
          ((Ideal.Quotient.mk mBb).comp ψ.toRingHom) p := rfl
      rw [hpres, hp, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hsub
  -- Step (iv). Étale-Hensel close. The substantive Mathlib gap.
  --
  -- We must conclude `ψ.range = ⊤`. The straightforward Nakayama path via
  -- `Submodule.le_of_le_smul_of_le_jacobson_bot` requires the ambient
  -- module to be A-finitely-generated, which `Bb` is not. The Stacks 00U7
  -- proof bridges this gap using the Henselian-étale lifting content:
  -- given the decomposition `b = ψ p + δ` (with `δ ∈ mBb ⊆ jacobson(⊥)`),
  -- one applies an étale-Hensel lift to `δ` to obtain `δ' ∈ ψ.range`
  -- with `b = ψ p + δ' ∈ ψ.range`. The lift exists because `ψ : P.Ring → Bb`
  -- is étale (composition of étale `A → P.Ring` and `A → Bb`, both étale)
  -- and `_h_m_jacob` provides the Henselian condition needed to lift roots.
  -- Gap B: étale-Hensel-Nakayama variant. iter-049+ Mathlib-PR target.
  refine Algebra.eq_top_iff.mpr fun b => ?_
  obtain ⟨p, δ, hδ, hb⟩ := h_decompose b
  -- Reduces to showing `δ ∈ ψ.range`, then `b = ψ p + δ ∈ ψ.range`.
  -- The étale-Hensel close: for `δ ∈ mBb`, there exists `q : P.Ring` with
  -- `ψ q = δ`. (Substantive Stacks 04D1 / 04GE content; Mathlib gap.)
  sorry

/-- **Helper B.3.a (substantive sub-helper): surjective polynomial presentation
after Zariski localization.**

Given the primitive-element data from Helper B.1, there exist `b ∈ B \ n` and,
in every localization `Bb = B[1/b]`, a surjective `A`-algebra homomorphism
`ψ : (standardEtalePairOfMonic f hf).Ring →ₐ[A] Bb`. The map sends the
generator `X` to the image of `β` in `Bb`.

The classical proof (Stacks 00U7, Step 3) refines `b` to be `f'(β) · e`, where
`e ∈ B` is the orthogonal idempotent in `B/mB` projecting onto the `n`-factor
of the decomposition `B/mB ≃ ∏ k_i` (obtained from
`Algebra.Etale.iff_exists_algEquiv_prod`). The element `e` is chosen so that
modulo `mB` only the `n`-factor survives in `Bb`, ensuring:
* `f(β) = 0` in `Bb` (since modulo `mB · Bb` it lies only in the (vanishing)
  other factors, and étaleness lifts the vanishing across the nilpotent
  thickening `mB · Bb`), and
* `f'(β)` is a unit in `Bb` (since `b` divides it).

These imply `P.HasMap (algebraMap B Bb β)` so `P.lift` yields the desired
`ψ`; surjectivity follows from the surjection
`A[X]/(f) → B/n ≃ k_{i_0}` combined with Nakayama for the idempotent `e`.

The body is now the mechanical 4-line assembly of the two sub-helpers
`exists_etale_witness_for_standardEtalePair` (Steps 1–5, substantive Raynaud
content) and `surjective_standardEtalePair_lift_of_etale` (Step 8 Nakayama). -/
private lemma exists_localization_surjective_standardEtale
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (_h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (β : B) (f : Polynomial A) (hf : f.Monic)
    (_hfβ : Polynomial.eval β (f.map (algebraMap A B)) ∈ n)
    (_hfdβ : Polynomial.eval β (f.derivative.map (algebraMap A B)) ∉ n) :
    ∃ b : B, b ∉ n ∧
      ∀ (Bb : Type u) [CommRing Bb] [Algebra B Bb] [IsLocalization.Away b Bb]
        [Algebra A Bb] [IsScalarTower A B Bb],
        ∃ ψ : (standardEtalePairOfMonic f hf).Ring →ₐ[A] Bb,
          Function.Surjective ψ := by
  -- Step (a). Extract the strengthened witness (idempotent `e` + isolation +
  -- iter-046 horizontal-killing conjunct + iter-042 further-localization
  -- scalar `s_B` + the per-`Bb` `HasMap` data) from B.3.a.i.
  obtain ⟨e, he_notmem, he_idem, he_isolate, he_horizontal, hb_notmem, s_B, hs_B_notmem, hwit⟩ :=
    exists_etale_witness_for_standardEtalePair (A := A) (B := B) n _h β f hf _hfβ _hfdβ
  -- The Zariski-localization witness is now `b := e * f'(β) * s_B`.
  refine ⟨e * Polynomial.eval β (f.derivative.map (algebraMap A B)) * s_B,
          ?_, fun Bb _ _ _ _ _ => ?_⟩
  · -- `e * f'(β) * s_B ∉ n` (each factor outside the prime `n`).
    intro hmem
    rcases (‹n.IsMaximal›.isPrime.mem_or_mem hmem) with h1 | h1
    · exact hb_notmem h1
    · exact hs_B_notmem h1
  -- Step (b). Destructure B′'s Route-C2 existential to obtain the Hensel-lifted
  -- `β' : Bb` (in the §4-refactored `Bb [Away (e * f'(β) * s_B) Bb]` instance),
  -- then build the lift `ψ := _P.lift β' ⟨hfβ', hfd'⟩`.
  obtain ⟨β', hβ'_lift, hfβ'_zero, hfdβ'_unit⟩ := hwit Bb
  let _P : StandardEtalePair A := standardEtalePairOfMonic f hf
  have hHas : _P.HasMap β' := ⟨hfβ'_zero, hfdβ'_unit⟩
  refine ⟨_P.lift β' hHas, ?_⟩
  -- iter-045: derive the shared Jacobson-containment fact for the §5 caller.
  have hb_outer_notmem :
      e * Polynomial.eval β (f.derivative.map (algebraMap A B)) * s_B ∉ n := by
    intro hmem
    rcases (‹n.IsMaximal›.isPrime.mem_or_mem hmem) with h1 | h1
    · exact hb_notmem h1
    · exact hs_B_notmem h1
  have he_div_b :
      e ∣ (e * Polynomial.eval β (f.derivative.map (algebraMap A B)) * s_B) := by
    rw [mul_assoc]; exact dvd_mul_right _ _
  have h_m_jacob :
      ((IsLocalRing.maximalIdeal A).map (algebraMap A Bb) : Ideal Bb) ≤
        Ideal.jacobson (⊥ : Ideal Bb) :=
    m_map_le_jacobson_of_etale_isolating n _h e he_idem he_notmem he_isolate
      he_horizontal
      (e * Polynomial.eval β (f.derivative.map (algebraMap A B)) * s_B)
      hb_outer_notmem he_div_b Bb
  -- Step (c). Surjectivity via B.3.a.ii (Nakayama on `Bb / m · Bb`), now
  -- consuming the propagated Jacobson-containment hypothesis.
  exact surjective_standardEtalePair_lift_of_etale (A := A) (B := B) n _h β f hf
    _hfβ _hfdβ e he_idem he_notmem he_isolate he_horizontal s_B Bb β' hβ'_lift
    (_P.lift β' hHas)
    (_P.lift_X β' hHas)
    h_m_jacob

/-- **Helper B.3: assemble the standard-étale presentation after Zariski localization.**

Given the primitive-element data from Helper B.1 (`β ∈ B` and a monic `f ∈ A[X]`
with `f(β) ∈ n`, `f'(β) ∉ n`), find an element `b ∈ B \ n` such that the
localization `Bb = B[1/b]` is a standard étale `A`-algebra.

The body is the integration of Helper B.3.a
(`exists_localization_surjective_standardEtale`, the substantive residual
gap) with Mathlib's `Algebra.IsStandardEtale.of_surjective`: any étale
algebra that is a surjective image of a standard étale algebra is itself
standard étale.

The classical proof (Stacks 00U7, Step 3) lives in B.3.a; the integration here
is mechanical once B.3.a is closed. -/
private lemma isStandardEtale_of_etale_via_lift
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (_h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (β : B) (f : Polynomial A) (hf : f.Monic)
    (_hfβ : Polynomial.eval β (f.map (algebraMap A B)) ∈ n)
    (_hfdβ : Polynomial.eval β (f.derivative.map (algebraMap A B)) ∉ n) :
    ∃ b : B, b ∉ n ∧
      ∀ (Bb : Type u) [CommRing Bb] [Algebra B Bb] [IsLocalization.Away b Bb]
        [Algebra A Bb] [IsScalarTower A B Bb],
        Algebra.IsStandardEtale A Bb := by
  -- The intended `StandardEtalePair` is `standardEtalePairOfMonic f hf`.
  let _P : StandardEtalePair A := standardEtalePairOfMonic f hf
  -- Invoke B.3.a: extract the witness `b ∉ n` and the surjection
  -- `ψ : _P.Ring →ₐ[A] Bb` for every `Bb = B[1/b]`.
  obtain ⟨b, hb_n, hsurj_data⟩ :=
    exists_localization_surjective_standardEtale (A := A) (B := B)
      n _h β f hf _hfβ _hfdβ
  refine ⟨b, hb_n, fun Bb _ _ _ _ _ => ?_⟩
  -- `Bb` is étale over `A`: `B → Bb` is étale (localization away), and
  -- `A → B` is étale by hypothesis.
  haveI : Algebra.Etale B Bb := Algebra.Etale.of_isLocalizationAway b
  haveI : Algebra.Etale A Bb := Algebra.Etale.comp A B Bb
  obtain ⟨ψ, hψ_surj⟩ := hsurj_data Bb
  exact Algebra.IsStandardEtale.of_surjective ψ hψ_surj

/-- **Helper B for Phase 2: étale ⇒ locally standard-étale at a maximal ideal.**

For an étale algebra `B/A` and a maximal ideal `n` of `B` lying over the maximal
ideal of `A`, there is `b ∈ B \ n` such that any localization `Bb` away from `b`
is a standard étale `A`-algebra.

This is Stacks `00U7` / EGA IV 17.6.1. Mathlib's `Algebra.exists_etale_of_isEtaleAt`
gives étale (not standard étale) locally. Body decomposed into B.1
(`exists_lift_separablePrimitiveElement_of_etale_at_maxIdeal`) + B.3
(`isStandardEtale_of_etale_via_lift`). B.2 (`standardEtalePairOfMonic`) is the
trivial assembly used inside B.3. -/
private lemma isStandardEtale_localizationAway_of_etale_at_maxIdeal
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    ∃ b : B, b ∉ n ∧
      ∀ (Bb : Type u) [CommRing Bb] [Algebra B Bb] [IsLocalization.Away b Bb]
        [Algebra A Bb] [IsScalarTower A B Bb],
        Algebra.IsStandardEtale A Bb := by
  obtain ⟨β, f, hf, hfβ, hfdβ⟩ :=
    exists_lift_separablePrimitiveElement_of_etale_at_maxIdeal (A := A) (B := B) n h
  exact isStandardEtale_of_etale_via_lift (A := A) (B := B) n h β f hf hfβ hfdβ

/-- **Phase 2 helper for Stage 1: étale-Henselian section lift.**

Given a Henselian local ring `A` and an étale `A`-algebra `B`, any `A`-algebra map
`g : B →ₐ[A] k` (with `k = ResidueField A` the residue field) lifts to an `A`-algebra
section `σ : B →ₐ[A] A` whose reduction modulo `maximalIdeal A` equals `g`.

This is the forward direction of "Henselian ⟺ unique lifting of residue-field
sections of étale algebras". The proof decomposes via Helper A (standard-étale
Hensel section-lift, closed sorry-free) and Helper B (étale ⇒ locally
standard-étale at a maximal ideal, the residual Mathlib gap). Reference: Stacks
04GH / EGA IV 18.5.13. -/
private lemma exists_section_of_residueField_section
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (g : B →ₐ[A] IsLocalRing.ResidueField A) :
    ∃ σ : B →ₐ[A] A,
      (IsLocalRing.residue A).comp σ.toRingHom = g.toRingHom := by
  -- Step 1. `g` is surjective: every element of `k = A⧸m` is `residue A a`
  -- for some `a : A`, and `g (algebraMap A B a) = residue A a` by `AlgHom.commutes`.
  have hg_surj : Function.Surjective (g : B → IsLocalRing.ResidueField A) := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal A) y
    exact ⟨algebraMap A B a, by rw [AlgHom.commutes]; rfl⟩
  -- Step 2. `n := ker g` is maximal (quotient is a field).
  let n : Ideal B := RingHom.ker g.toRingHom
  haveI hn_max : n.IsMaximal := by
    have heq : (B ⧸ n) ≃+* IsLocalRing.ResidueField A :=
      RingHom.quotientKerEquivOfSurjective hg_surj
    exact Ideal.Quotient.maximal_of_isField n
      (MulEquiv.isField (Field.toIsField (IsLocalRing.ResidueField A)) heq.toMulEquiv)
  -- Step 3. `n` lies over `maximalIdeal A`.
  have hn_over : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A := by
    ext a
    show g.toRingHom (algebraMap A B a) = 0 ↔ a ∈ IsLocalRing.maximalIdeal A
    show g (algebraMap A B a) = 0 ↔ a ∈ IsLocalRing.maximalIdeal A
    rw [AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem
  -- Step 4. Apply Helper B to find `b ∉ n` with `Localization.Away b` standard étale.
  haveI : IsLocalRing A := inferInstance
  obtain ⟨b, hb_n, hSE⟩ :=
    isStandardEtale_localizationAway_of_etale_at_maxIdeal (A := A) (B := B) n hn_over
  let Bb : Type u := Localization.Away b
  haveI : IsScalarTower A B Bb := .of_algebraMap_eq fun _ => rfl
  haveI hSE' : Algebra.IsStandardEtale A Bb := hSE Bb
  -- Step 5. Lift `g.toRingHom : B →+* k` to `g_loc_rh : Bb →+* k` via the universal
  -- property of `Localization.Away b` (using that `g b ≠ 0`, hence `g b` is a unit
  -- in the field `k`).
  have hgb_unit : IsUnit (g.toRingHom b) := by
    rw [isUnit_iff_ne_zero]
    intro hgb_zero
    exact hb_n hgb_zero
  let g_loc_rh : Bb →+* IsLocalRing.ResidueField A :=
    IsLocalization.Away.lift (S := Bb) b (g := g.toRingHom) hgb_unit
  have hg_loc_lift_eq : g_loc_rh.comp (algebraMap B Bb) = g.toRingHom :=
    IsLocalization.Away.lift_comp (S := Bb) (x := b) (g := g.toRingHom) hgb_unit
  -- Upgrade to an `A`-algebra hom.
  let g_loc : Bb →ₐ[A] IsLocalRing.ResidueField A :=
    { __ := g_loc_rh
      commutes' := fun a => by
        show g_loc_rh (algebraMap A Bb a) = _
        have ha_eq : (algebraMap A Bb : A →+* Bb) a =
            (algebraMap B Bb) ((algebraMap A B) a) := rfl
        rw [ha_eq,
            show g_loc_rh ((algebraMap B Bb) ((algebraMap A B) a)) =
              g.toRingHom ((algebraMap A B) a) from RingHom.congr_fun hg_loc_lift_eq _]
        exact g.commutes a }
  -- Step 6. Pick a `StandardEtalePresentation A Bb` from `hSE'`.
  obtain ⟨pres⟩ := (Algebra.IsStandardEtale.nonempty_standardEtalePresentation :
      Nonempty (StandardEtalePresentation A Bb))
  -- Step 7. Transport `g_loc` to `pres.P.Ring →ₐ[A] k`.
  let g_P : pres.P.Ring →ₐ[A] IsLocalRing.ResidueField A :=
    g_loc.comp pres.equivRing.symm.toAlgHom
  -- Step 8. Apply Helper A to obtain `σ_P : pres.P.Ring →ₐ[A] A`
  -- with `(residue A).comp σ_P = g_P`.
  obtain ⟨σ_P, hσ_P⟩ := exists_section_of_standardEtalePair pres.P g_P
  -- Step 9. Transport back: `σ_loc := σ_P.comp pres.equivRing.toAlgHom : Bb →ₐ[A] A`.
  let σ_loc : Bb →ₐ[A] A := σ_P.comp pres.equivRing.toAlgHom
  -- Step 10. Final retraction: `σ := σ_loc.comp (IsScalarTower.toAlgHom A B Bb)`.
  refine ⟨σ_loc.comp (IsScalarTower.toAlgHom A B Bb), ?_⟩
  -- Step 11. Residue compatibility (diagram chase).
  -- `(residue A).comp σ_loc.toRingHom = g_loc.toRingHom` because
  --   `(residue A).comp σ_P.toRingHom = g_P.toRingHom = g_loc.comp pres.equivRing.symm`
  -- and composing with `pres.equivRing` gives `g_loc`.
  have h_res_σ_loc : (IsLocalRing.residue A).comp σ_loc.toRingHom = g_loc.toRingHom := by
    ext x
    have h_aux : IsLocalRing.residue A (σ_P (pres.equivRing x)) =
        g_P (pres.equivRing x) := RingHom.congr_fun hσ_P (pres.equivRing x)
    show IsLocalRing.residue A (σ_P (pres.equivRing x)) = g_loc x
    rw [h_aux]
    show g_loc (pres.equivRing.symm (pres.equivRing x)) = g_loc x
    rw [pres.equivRing.symm_apply_apply]
  -- Combine: σ.toRingHom = σ_loc.toRingHom.comp (algebraMap B Bb)
  show (IsLocalRing.residue A).comp
      (σ_loc.comp (IsScalarTower.toAlgHom A B Bb)).toRingHom = g.toRingHom
  rw [show (σ_loc.comp (IsScalarTower.toAlgHom A B Bb)).toRingHom =
        σ_loc.toRingHom.comp (algebraMap B Bb) from rfl,
      ← RingHom.comp_assoc, h_res_σ_loc]
  -- Goal: g_loc.toRingHom.comp (algebraMap B Bb) = g.toRingHom
  show g_loc_rh.comp (algebraMap B Bb) = g.toRingHom
  exact hg_loc_lift_eq

/-- **Stage 1 (raw retraction + decomposition data).**

Given an étale `A`-algebra `B` with a maximal ideal `n` lying over the maximal ideal
`m` of `A`, the étale-over-field decomposition `B/mB ≃ ∏ k_i` (Mathlib's
`Algebra.Etale.iff_exists_algEquiv_prod` applied to `B ⊗_A (A/m)`) yields three facts
simultaneously:

* there are only finitely many primes of `B` lying over `m`
  (one per factor `k_i`);
* every such prime is maximal (the corresponding factor `k_i` is a field);
* there exists a retraction `r : B →ₐ[A] A`. This `r` is built by choosing the
  factor corresponding to `n`, identifying it with `k = A/m` (which equals
  `k^sep` since `A` is strictly Henselian), and then Hensel-lifting the composite
  `B → B/n = k = A/m` to `B → A` via `IsStrictlyHenselianLocalRing.is_henselian`.

The body remains a typed `sorry` — this is the only residual `sorry` in 04GH. -/
private theorem stage1_raw_retraction
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (_h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    (((IsLocalRing.maximalIdeal A).primesOver B).Finite) ∧
      (∀ p ∈ (IsLocalRing.maximalIdeal A).primesOver B, p.IsMaximal) ∧
      Nonempty (B →ₐ[A] A) := by
  -- Blueprint outline (Stacks 04GH stage 1):
  --
  -- Set `k := A/m = ResidueField A`. The fibre algebra `k ⊗_A B = B/mB` is étale over
  -- `k`; by `Algebra.Etale.iff_exists_algEquiv_prod` it splits as a finite product
  -- `k ⊗_A B ≃ ∏_{i ∈ I} k_i` with `I` finite and each `k_i` a finite separable extension
  -- of `k`. The finiteness of `I` plus the bijection {primes of B over m} ≃ {primes of
  -- B/mB} ≃ I gives the finiteness assertion, and each `k_i` is a field gives the
  -- maximality assertion. The quotient `B/n`, being a quotient of `B/mB`, is one of
  -- the `k_i`. Choose an embedding `B/n ↪ k^sep`; since `A` is strictly Henselian,
  -- `k = k^sep`, so the embedding is an isomorphism `B/n ≃ k = A/m`. By Hensel's lemma
  -- (étale-Henselian lifting via `henselian_if_exists_section` or
  -- `HenselianLocalRing.is_henselian`), the composite `B → B/n = A/m` lifts to a
  -- retraction `r : B →ₐ[A] A`.
  -- ----------------------------------------------------------------------
  -- Step 1. Set up the residue field `k = A/m` and the fibre `Bk := k ⊗[A] B`.
  -- Bk is étale over k by `Algebra.Etale.baseChange`.
  let k : Type u := IsLocalRing.ResidueField A
  let Bk : Type u := TensorProduct A k B
  -- Step 2. Apply the étale-over-field decomposition to obtain `Bk ≃ ∏_i kᵢ`
  -- with `I` finite and each `kᵢ` a finite separable extension of `k`.
  obtain ⟨I, hIfin, kI, hKfield, hKalg, e, hKsep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := k) (A := Bk)).mp inferInstance
  -- Step 3 (residual). The remaining work — proving the bijection between primes of
  -- `B` over `m` and primes of `Bk`, lifting through the decomposition, and
  -- Hensel-lifting the composite `B → B/n = k = A/m` to `B → A` — is non-trivial
  -- and requires substantial infrastructure (étale-Henselian lifting from
  -- `IsStrictlyHenselianLocalRing.is_henselian`, plus the universal property of
  -- the residue field). Left as a typed sorry to track progress.
  -- Etale ⇒ FormallyUnramified + FinitePresentation ⇒ EssFiniteType ⇒ QuasiFinite.
  -- (Mathlib has `[EssFiniteType R S] [FormallyUnramified R S] : QuasiFinite R S` as a
  -- low-priority instance; we materialize it here so all three subgoals can use it.)
  haveI hQF : Algebra.QuasiFinite A B := by
    refine ⟨fun P _ => ?_⟩
    haveI : Algebra.Etale P.ResidueField (P.Fiber B) :=
      Algebra.Etale.baseChange A B P.ResidueField
    obtain ⟨J, hJfin, Aj, hField, hAlg, eq, hprod⟩ :=
      (Algebra.Etale.iff_exists_algEquiv_prod P.ResidueField (P.Fiber B)).mp inferInstance
    haveI : Finite J := hJfin
    letI : ∀ i, Field (Aj i) := hField
    letI : ∀ i, Algebra P.ResidueField (Aj i) := hAlg
    haveI : ∀ i, Module.Finite P.ResidueField (Aj i) := fun i => (hprod i).1
    haveI : Module.Finite P.ResidueField (∀ i, Aj i) := Module.Finite.pi
    exact Module.Finite.of_surjective eq.symm.toLinearMap eq.symm.surjective
  refine ⟨?_, ?_, ?_⟩
  · -- Finiteness: primes of B over m are finite since A → B is quasi-finite.
    exact Algebra.QuasiFinite.finite_primesOver _
  · -- Maximality: any prime P of B over m must be maximal. Argument:
    -- take a maximal Q ⊇ P; Q.under A is a prime of A containing m (since P.under = m
    -- and P ⊆ Q), and A is local with maximal m, so Q.under = m. Now P and Q both
    -- lie over m with P ≤ Q, and `QuasiFiniteAt A Q` gives P = Q, so P is maximal.
    rintro P ⟨hP_prime, hP_liesOver⟩
    haveI hPp : P.IsPrime := hP_prime
    have hP_under : P.under A = IsLocalRing.maximalIdeal A := hP_liesOver.over.symm
    -- Find a maximal Q ⊇ P.
    obtain ⟨Q, hQ_max, hPQ⟩ := Ideal.exists_le_maximal P hP_prime.ne_top
    haveI hQp : Q.IsPrime := hQ_max.isPrime
    -- `Q.under A` is a prime of A, hence ≤ m (A is local).
    haveI hQu_prime : (Q.under A).IsPrime := by
      rw [Ideal.under_def]; exact Ideal.comap_isPrime _ _
    have hQ_under : Q.under A = IsLocalRing.maximalIdeal A := by
      apply le_antisymm
      · exact IsLocalRing.le_maximalIdeal_of_isPrime _
      · rw [← hP_under]
        rw [Ideal.under_def, Ideal.under_def]
        exact Ideal.comap_mono hPQ
    -- `QuasiFiniteAt A Q` is automatic from `QuasiFinite A B`.
    haveI : Algebra.QuasiFiniteAt A Q := inferInstance
    have hPQ_eq : P = Q :=
      Algebra.QuasiFiniteAt.eq_of_le_of_under_eq hPQ (hP_under.trans hQ_under.symm)
    exact hPQ_eq ▸ hQ_max
  · -- Existence of a raw retraction `B →ₐ[A] A`:
    -- Pick the factor `kᵢ` corresponding to `n` (where `B/n` injects). Since
    -- `A` is strictly Henselian, `k = k^sep`, so `kᵢ = k`. Compose
    -- `B → B/n ↪ kᵢ = k = A/m` and Hensel-lift through `B` being étale over `A`.
    --
    -- Construction sketch:
    --   * `e : Bk ≃ₐ[k] (∀ i, kI i)` from `iff_exists_algEquiv_prod`.
    --   * `IsSepClosed k` (from `IsStrictlyHenselianLocalRing.isSepClosed_residueField`)
    --     forces each finite-separable `kI i` to be `≃ₐ[k] k`.
    --   * The composite `B → Bk ≃ ∏ kI i → kI i₀ ≃ k = A/m` gives a section
    --     of `A/m → B/n` for the index `i₀` matching `n`.
    --   * Hensel-lift this section to `B → A` using the étale-Henselian lifting
    --     property (the converse direction of `henselian_if_exists_section`).
    --
    -- iter-028 decomposition: the residual sorry is split into two typed-sorry
    -- helpers `exists_residueField_algHom_of_etale_max` (Phase 1, residue-class
    -- section) and `exists_section_of_residueField_section` (Phase 2, Hensel lift).
    -- This expression already closes the goal sorry-free modulo those helpers.
    obtain ⟨g⟩ := exists_residueField_algHom_of_etale_max (A := A) n _h
    obtain ⟨σ, _hσ⟩ := exists_section_of_residueField_section (A := A) g
    exact ⟨σ⟩

/-- **Stage 2 (residue compatibility via prime avoidance + localization).**

Given an étale `A`-algebra `B` with a maximal ideal `n` lying over `m`, there exists
an `A`-algebra retraction `s : B →ₐ[A] A` with `n = m.comap s.toRingHom`.

The proof: apply stage 1 to `(B, n)` to extract finiteness + maximality of all primes
of `B` over `m`. Apply prime avoidance to find `b ∉ n` with `b` in every other prime
over `m`. Form `B_b := Localization.Away b`. Then `B_b` is étale over `A` (composition),
`n.map (algebraMap B B_b)` is the unique prime of `B_b` over `m`, and applying stage 1
to `(B_b, n.map ..)` yields a retraction `r_b : B_b →ₐ[A] A`. The composite
`s := r_b ∘ (algebraMap B B_b) : B →ₐ[A] A` then satisfies `n = m.comap s.toRingHom`
automatically, because `s.toRingHom ⁻¹ m` is a prime of `B` over `m` containing
`ker(B → B_b)` (the primes of `B` containing some `b^k` are killed by localization) and
hence corresponds to the unique prime `n` of `B_b` over `m`. -/
private theorem stage2_make_residue_compatible
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal]
    (h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    ∃ s : B →ₐ[A] A, n = (IsLocalRing.maximalIdeal A).comap s.toRingHom := by
  -- Step 1. Extract finiteness, maximality, and a (currently unused) raw retraction
  -- from stage 1.
  obtain ⟨hfin, hmax, _⟩ := stage1_raw_retraction B n h
  -- Step 2. Convert to a Finset and erase `n` to obtain the set of "other" primes.
  have hn_mem : n ∈ (IsLocalRing.maximalIdeal A).primesOver B := by
    refine ⟨inferInstance, ⟨?_⟩⟩
    exact h.symm
  let s : Finset (Ideal B) := hfin.toFinset.erase n
  -- Step 3. Each other prime is maximal and therefore not contained in `n`.
  have hnot_le : ∀ p ∈ s, ¬ ((fun q => q) p) ≤ n := by
    intro p hp
    simp only [s, Finset.mem_erase, Set.Finite.mem_toFinset] at hp
    obtain ⟨hpn, hps⟩ := hp
    have hp_max : p.IsMaximal := hmax p hps
    intro hle
    exact hpn (hp_max.eq_of_le (‹n.IsMaximal›.ne_top) hle)
  -- Step 4. Prime avoidance: find `b ∉ n` lying in every other prime over `m`.
  obtain ⟨b, hb_n, hb_s⟩ := exists_mem_finset_inf_notMem_of_isPrime hnot_le
  -- Step 5. Set up the localization `B_b := Localization.Away b`, equipped with an
  -- `A`-algebra structure via the composition `A → B → B_b`, and the scalar tower.
  let Bb : Type u := Localization.Away b
  letI : CommRing Bb := inferInstanceAs (CommRing (Localization.Away b))
  letI : Algebra B Bb := inferInstanceAs (Algebra B (Localization.Away b))
  letI : IsLocalization.Away b Bb := inferInstanceAs (IsLocalization.Away b (Localization.Away b))
  -- `Algebra A Bb` is auto-derived from `Algebra A B` via the `OreLocalization`
  -- algebra instance, with `algebraMap A Bb = (algebraMap B Bb).comp (algebraMap A B)`.
  haveI : IsScalarTower A B Bb := .of_algebraMap_eq fun _ => rfl
  -- Step 6. `Bb` is étale over `A` (auto-derived: étale of base + localization at one
  -- element preserves étale via `Algebra.Etale.instAway`).
  haveI : Algebra.Etale A Bb := inferInstance
  -- Step 7. Let `nb := n.map (algebraMap B Bb)`. Show it is maximal and lies over `m`.
  let nb : Ideal Bb := n.map (algebraMap B Bb)
  have hb_disjoint : Disjoint (Submonoid.powers b : Set B) (n : Set B) := by
    rw [Set.disjoint_left]
    intro x hxp hxn
    obtain ⟨k, rfl⟩ := hxp
    -- `b^k ∈ n` and `n.IsPrime` ⇒ `b ∈ n`, contradicting `hb_n`.
    exact hb_n (‹n.IsMaximal›.isPrime.mem_of_pow_mem k hxn)
  have hcomap_nb : Ideal.comap (algebraMap B Bb) nb = n := by
    have := IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers b) Bb (I := n) ‹n.IsMaximal›.isPrime hb_disjoint
    -- `Ideal.under B nb = n`, and `under` unfolds to `comap`.
    simpa [nb, Ideal.under] using this
  haveI hnb_prime : nb.IsPrime := by
    rw [IsLocalization.isPrime_iff_isPrime_disjoint (M := Submonoid.powers b) (S := Bb)]
    simp only [Ideal.under, hcomap_nb]
    exact ⟨‹n.IsMaximal›.isPrime, hb_disjoint⟩
  haveI hnb_max : nb.IsMaximal := by
    have hcomap_max : (Ideal.comap (algebraMap B Bb) nb).IsMaximal := hcomap_nb ▸ ‹n.IsMaximal›
    exact Ideal.IsMaximal.of_isLocalization_of_disjoint (Submonoid.powers b)
  have hnb_over : nb.comap (algebraMap A Bb) = IsLocalRing.maximalIdeal A := by
    -- `algebraMap A Bb = (algebraMap B Bb).comp (algebraMap A B)`.
    have hcomp : (algebraMap A Bb : A →+* Bb) =
        (algebraMap B Bb).comp (algebraMap A B) := rfl
    rw [show (Ideal.comap (algebraMap A Bb) nb : Ideal A) =
          Ideal.comap (algebraMap A B) (Ideal.comap (algebraMap B Bb) nb) from by
        rw [hcomp, ← Ideal.comap_comap], hcomap_nb, h]
  -- Step 8. Apply stage 1 to `(Bb, nb)` to obtain a raw retraction `r_b : Bb →ₐ[A] A`.
  obtain ⟨_, _, ⟨r_b⟩⟩ := stage1_raw_retraction Bb nb hnb_over
  -- Step 9. The composite `s := r_b ∘ (algebraMap B Bb) : B →ₐ[A] A`.
  let s_ret : B →ₐ[A] A := r_b.comp (IsScalarTower.toAlgHom A B Bb)
  refine ⟨s_ret, ?_⟩
  -- Step 10. We must show `n = (maximalIdeal A).comap s_ret.toRingHom`.
  -- Set `P := (maximalIdeal A).comap r_b.toRingHom`. This `P` is a maximal ideal of `Bb`
  -- lying over `m` (since `r_b` is an `A`-algebra section of `algebraMap A Bb`, so
  -- `r_b ∘ algebraMap A Bb = id`, hence the comap of `m` along `r_b` lies over `m`;
  -- and it is maximal because `m` is maximal and `A` is a field modulo `m`, but more
  -- directly because `Bb / P ↪ A / m`).
  -- We show `P = nb` by uniqueness of the prime of `Bb` over `m`.
  have h_unique : ∀ (P : Ideal Bb), P.IsPrime → P.comap (algebraMap A Bb) =
      IsLocalRing.maximalIdeal A → P = nb := by
    intro P hP hP_over
    -- `Q := P.comap (algebraMap B Bb)` is a prime of `B` over `m` (using
    -- `hP_over` and the comap composition).
    set Q : Ideal B := P.comap (algebraMap B Bb)
    have hQ_prime : Q.IsPrime := Ideal.comap_isPrime _ _
    have hQ_over : Q.comap (algebraMap A B) = IsLocalRing.maximalIdeal A := by
      rw [← hP_over]
      have hcomp : (algebraMap A Bb : A →+* Bb) =
          (algebraMap B Bb).comp (algebraMap A B) := rfl
      rw [show (Ideal.comap (algebraMap A Bb) P : Ideal A) =
            Ideal.comap (algebraMap A B) (Ideal.comap (algebraMap B Bb) P) from by
          rw [hcomp, ← Ideal.comap_comap]]
    -- `Q ∈ primesOver m` ⇒ `Q ∈ hfin.toFinset`.
    have hQ_mem_set : Q ∈ (IsLocalRing.maximalIdeal A).primesOver B := by
      refine ⟨hQ_prime, ⟨hQ_over.symm⟩⟩
    -- `b ∉ Q`: otherwise some power of `b` is in `P`, but `P` is prime so `b ∈ Q`
    -- would force `algebraMap B Bb b ∈ P`, contradicting that `algebraMap B Bb b` is
    -- a unit in `Bb`.
    have hb_not_in_Q : b ∉ Q := by
      intro hbQ
      -- `algebraMap B Bb b ∈ P` because `b ∈ Q := P.comap _`.
      have hbP : algebraMap B Bb b ∈ P := hbQ
      -- `algebraMap B Bb b` is a unit since `IsLocalization.Away b Bb`.
      have hb_unit : IsUnit (algebraMap B Bb b) :=
        IsLocalization.Away.algebraMap_isUnit (S := Bb) b
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hbP hb_unit)
    -- If `Q ≠ n`, then `Q ∈ s` so `b ∈ Q`, contradiction.
    have hQ_eq_n : Q = n := by
      by_contra hne
      have hQ_in_s : Q ∈ s := by
        simp only [s, Finset.mem_erase, Set.Finite.mem_toFinset]
        exact ⟨hne, hQ_mem_set⟩
      exact hb_not_in_Q (hb_s Q hQ_in_s)
    -- So `Q = n`, meaning `nb = n.map (algebraMap B Bb) = Q.map _`. We want `P = nb`.
    -- Since `P` is prime in `Bb` and `nb` is the unique prime of `Bb` whose comap is
    -- `n`, and `Q = P.comap = n`, we have via the localization bijection
    -- `P = (P.comap (algebraMap B Bb)).map (algebraMap B Bb)` for prime ideals disjoint
    -- from the inverted submonoid.
    have hPmap : (Q : Ideal B).map (algebraMap B Bb) = P := by
      apply IsLocalization.map_comap (M := Submonoid.powers b) (S := Bb)
    -- so `P = Q.map = n.map = nb`.
    show P = nb
    rw [← hPmap, hQ_eq_n]
  -- Now apply uniqueness to `P := (maximalIdeal A).comap r_b.toRingHom`.
  have hPover : ((IsLocalRing.maximalIdeal A).comap r_b.toRingHom).comap
      (algebraMap A Bb) = IsLocalRing.maximalIdeal A := by
    -- `r_b ∘ algebraMap A Bb = algebraMap A A = id` (since `r_b` is an `A`-algebra map).
    have hcomp : (r_b.toRingHom : Bb →+* A).comp (algebraMap A Bb) = algebraMap A A := by
      ext a
      simpa using r_b.commutes a
    rw [show (Ideal.comap (algebraMap A Bb)
            (Ideal.comap r_b.toRingHom (IsLocalRing.maximalIdeal A)) : Ideal A) =
          Ideal.comap ((r_b.toRingHom : Bb →+* A).comp (algebraMap A Bb))
            (IsLocalRing.maximalIdeal A) from by rw [Ideal.comap_comap]]
    rw [hcomp]
    -- `Ideal.comap (algebraMap A A) m = m` since `algebraMap A A = RingHom.id _`.
    show Ideal.comap (RingHom.id A) (IsLocalRing.maximalIdeal A) = _
    rw [Ideal.comap_id]
  have hPprime : ((IsLocalRing.maximalIdeal A).comap r_b.toRingHom).IsPrime := by
    apply Ideal.comap_isPrime
  have hP_eq_nb : (IsLocalRing.maximalIdeal A).comap r_b.toRingHom = nb :=
    h_unique _ hPprime hPover
  -- Step 11. Conclude: `s_ret.toRingHom = r_b.toRingHom.comp (algebraMap B Bb)`. So
  -- `comap s_ret.toRingHom m = comap (algebraMap B Bb) (comap r_b.toRingHom m) =
  -- comap (algebraMap B Bb) nb = n`.
  have hs_ret_eq : (s_ret.toRingHom : B →+* A) =
      (r_b.toRingHom : Bb →+* A).comp (algebraMap B Bb) := by
    ext x
    simp [s_ret, IsScalarTower.toAlgHom, IsScalarTower.coe_toAlgHom]
  rw [show (IsLocalRing.maximalIdeal A).comap s_ret.toRingHom =
        Ideal.comap (algebraMap B Bb)
          (Ideal.comap r_b.toRingHom (IsLocalRing.maximalIdeal A)) from by
      rw [hs_ret_eq, ← Ideal.comap_comap]]
  rw [hP_eq_nb, hcomap_nb]

/-- **Étale-cancellation step: a section of an étale ring map has idempotent kernel,
generated by an idempotent.**

If `B` is étale over `A` and `s : B →ₐ[A] A` is any `A`-algebra retraction, then the kernel
of `s` is principal, generated by an idempotent `e ∈ B`. This is the algebraic content of
"the closed immersion defined by a section of an étale morphism is also an open immersion".

The proof has three ingredients:

* `Algebra.FormallyEtale.of_restrictScalars`: cancellation in the tower `A → B → A` whose
  composition is the identity gives `Algebra.FormallyEtale B A`.
* `Algebra.FormallyEtale.iff_of_surjective`: for a surjective algebra map, formally étale
  ⇔ kernel is idempotent (as an ideal).
* `Algebra.FinitePresentation.ker_fG_of_surjective` + `Ideal.isIdempotentElem_iff_of_fg`:
  the kernel is f.g. (étale ⇒ FP) and FG-idempotent ideals are principal idempotent. -/
private lemma ker_idempotent_of_etale_section
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (s : B →ₐ[A] A) :
    ∃ e : B, IsIdempotentElem e ∧ RingHom.ker s.toRingHom = Ideal.span {e} := by
  -- Equip `A` with a `B`-algebra structure via `s`. The composition `A → B → A`
  -- is then the identity, making `A → B → A` a scalar tower.
  letI : Algebra B A := s.toRingHom.toAlgebra
  haveI : IsScalarTower A B A :=
    IsScalarTower.of_algebraMap_eq fun a => (s.commutes a).symm
  -- Cancellation: `A → B` is formally unramified (étale) and `A → A` is formally étale,
  -- so `B → A` is formally étale.
  haveI : Algebra.FormallyEtale B A := Algebra.FormallyEtale.of_restrictScalars (R := A)
  -- The section `s` is surjective.
  have hsurj : Function.Surjective (algebraMap B A) :=
    fun a => ⟨algebraMap A B a, s.commutes a⟩
  -- Kernel is idempotent as an ideal.
  have h_idem : IsIdempotentElem (RingHom.ker (algebraMap B A : B →+* A)) :=
    (Algebra.FormallyEtale.iff_of_surjective hsurj).mp inferInstance
  -- Kernel is f.g.: A is FP over A (trivially), B is FP over A (étale ⇒ FP).
  have h_fg : (RingHom.ker s.toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (R := A) s hsurj
  -- Combine: FG-idempotent ⇒ principal-by-idempotent.
  obtain ⟨e, he_idem, he_span⟩ := (Ideal.isIdempotentElem_iff_of_fg _ h_fg).mp h_idem
  refine ⟨e, he_idem, ?_⟩
  rw [he_span]

variable (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]

/-- **Stacks `04GH` (good retraction).** If `A` is a strictly Henselian local ring and
`A → B` is étale, then every maximal ideal `n` of `B` lying over the maximal ideal `m`
of `A` admits an `A`-algebra retraction `s : B →ₐ[A] A` with `n = m.comap s.toRingHom`.

Blueprint: `local-structure.tex`, `thm:strictly-henselian-good-retraction`. -/
theorem strictlyHenselian_good_retraction
    (n : Ideal B) [n.IsMaximal]
    (h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    ∃ s : B →ₐ[A] A, n = (IsLocalRing.maximalIdeal A).comap s.toRingHom :=
  stage2_make_residue_compatible B n h

/-- **Stacks `04GG` (étale over strictly Henselian, localization is an isomorphism).**
Let `A` be a strictly Henselian local ring, `A → B` étale, and `n ⊂ B` a maximal ideal
lying over the maximal ideal `m` of `A`. Then the canonical local ring homomorphism
`Localization.AtPrime m → B_n` is bijective; equivalently, `A → B_n` is an isomorphism.

Blueprint: `local-structure.tex`,
`thm:etale-over-strictly-henselian-localization-isom`. -/
theorem bijective_localRingHom_of_strictlyHenselian
    (n : Ideal B) [n.IsMaximal]
    (h : n.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) :
    Function.Bijective
      (Localization.localRingHom (n.comap (algebraMap A B)) n (algebraMap A B) rfl) := by
  -- Blueprint diagram chase:
  --
  -- Let `s : B →ₐ[A] A` be the good retraction from
  -- `strictlyHenselian_good_retraction`, with `n = m.comap s.toRingHom`. Since `A` is
  -- local with maximal ideal `m`, the canonical map `A → Loc m` is bijective. The
  -- diagram
  --   `Loc m → Loc n → Loc m`
  -- (the first map is the canonical `localRingHom`, and the second comes from the
  -- universal property applied to `s : B → A` since `s(B \ n) ⊆ A \ m = A^×`) composes
  -- to the identity on `Loc m`. Hence the second map is surjective and the first is
  -- injective. The remaining surjectivity of `localRingHom` (equivalently injectivity
  -- of the section) is the cancellation step.
  --
  -- We reduce the goal to bijectivity of `algebraMap A (Loc n)` (composition
  -- `A → B → Loc n`). Injectivity is immediate from the section `s_loc : Loc n → A`
  -- built from `s`. Surjectivity remains the deeper claim and is encoded in the
  -- structured typed sorry `surjective_algebraMap_AtPrime_of_section` below.
  -- ----------------------------------------------------------------------
  -- Step 1. Extract the good retraction from 04GH.
  obtain ⟨s, hs⟩ := strictlyHenselian_good_retraction B n h
  -- Step 2. `n.primeCompl` maps under `s` to units of `A`. (Because `n = s⁻¹(m)`, so
  -- `y ∉ n ⇒ s(y) ∉ m`; and `A` is local with maximal `m`, so `A \ m = A^×`.)
  have hs_unit : ∀ y : n.primeCompl, IsUnit (s.toRingHom (y : B)) := by
    rintro ⟨y, hy⟩
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hsm
    apply hy
    -- `hs : n = comap s.toRingHom (maximalIdeal A)` and `hsm : s.toRingHom y ∈ maximalIdeal A`.
    -- So `y ∈ comap s.toRingHom (maximalIdeal A) = n`.
    rw [hs]
    exact hsm
  -- Step 3. Lift `s : B → A` through the localization `B → Loc n` to get
  -- `s_loc : Loc n →+* A`.
  let s_loc : Localization.AtPrime n →+* A := IsLocalization.lift hs_unit
  -- Step 4. `s_loc` is a left inverse of the canonical map `A → Loc n` (via `B`).
  -- That is, `s_loc ∘ (algebraMap B (Loc n)) ∘ (algebraMap A B) = id_A`.
  have hs_loc_comp_B : s_loc.comp (algebraMap B (Localization.AtPrime n)) = s.toRingHom :=
    IsLocalization.lift_comp hs_unit
  have hs_loc_section :
      s_loc.comp ((algebraMap B (Localization.AtPrime n)).comp (algebraMap A B)) =
        RingHom.id A := by
    rw [← RingHom.comp_assoc, hs_loc_comp_B]
    ext a
    exact s.commutes a
  -- Step 5. The diagram identity:
  -- `localRingHom ∘ algebraMap A (Loc m') = (algebraMap B (Loc n)) ∘ (algebraMap A B)`.
  set m' : Ideal A := n.comap (algebraMap A B) with hm'_def
  set Lm : Type u := Localization.AtPrime m'
  set Ln : Type u := Localization.AtPrime n
  set lrh : Lm →+* Ln :=
    Localization.localRingHom (n.comap (algebraMap A B)) n (algebraMap A B) rfl
  have h_lrh_diag :
      lrh.comp (algebraMap A Lm) =
        (algebraMap B Ln).comp (algebraMap A B) := by
    ext a
    show lrh ((algebraMap A Lm) a) = (algebraMap B Ln) ((algebraMap A B) a)
    exact Localization.localRingHom_to_map _ _ _ _ _
  -- Step 6. The map `algebraMap A Lm` is bijective, because `m' = maximalIdeal A`
  -- and `A` is local. Equivalently, `m'.primeCompl ≤ IsUnit.submonoid A`.
  have h_Lm_bij : Function.Bijective (algebraMap A Lm) := by
    have hmcompl_le : m'.primeCompl ≤ IsUnit.submonoid A := by
      intro x hx
      -- `hx : x ∈ m'.primeCompl`, i.e., `x ∉ m'`. By `h`, `x ∉ maximalIdeal A`.
      have hxA : x ∉ IsLocalRing.maximalIdeal A := by rw [← h]; exact hx
      exact (IsUnit.mem_submonoid_iff x).mpr (IsLocalRing.notMem_maximalIdeal.mp hxA)
    exact (IsLocalization.atUnits A m'.primeCompl hmcompl_le).bijective
  -- Step 7. Reduce `Function.Bijective lrh` to `Function.Bijective ((algebraMap B Ln).comp
  -- (algebraMap A B))` using h_Lm_bij and h_lrh_diag.
  have h_reduce :
      Function.Bijective lrh ↔
        Function.Bijective ((algebraMap B Ln).comp (algebraMap A B) : A →+* Ln) := by
    constructor
    · intro hlrh
      rw [← h_lrh_diag]
      exact hlrh.comp h_Lm_bij
    · intro hcomp
      -- lrh ∘ aLm = aLn (= comp). Since aLm bijective, lrh = aLn ∘ aLm.symm; both bijective.
      -- Equivalently, factor lrh through the iso aLm.
      have : Function.Bijective (lrh ∘ algebraMap A Lm) := by
        rw [show (lrh ∘ algebraMap A Lm) = _ from congrArg DFunLike.coe h_lrh_diag]
        exact hcomp
      -- bijective composition with bijective on the right ⇒ first factor bijective.
      refine ⟨?_, ?_⟩
      · -- lrh injective
        intro x y hxy
        obtain ⟨a, rfl⟩ := h_Lm_bij.surjective x
        obtain ⟨b, rfl⟩ := h_Lm_bij.surjective y
        exact congrArg (algebraMap A Lm) (this.injective (by simpa using hxy))
      · -- lrh surjective
        intro z
        obtain ⟨a, ha⟩ := this.surjective z
        exact ⟨algebraMap A Lm a, ha⟩
  rw [h_reduce]
  -- Step 8. Show `(algebraMap B Ln).comp (algebraMap A B) : A → Ln` is bijective.
  -- Injectivity: it's split mono via `s_loc`. Surjectivity is the deeper claim.
  refine ⟨?_, ?_⟩
  · -- Injectivity: `s_loc ∘ ((algebraMap B Ln) ∘ (algebraMap A B)) = id_A`.
    intro x y hxy
    have hxy' : s_loc ((algebraMap B Ln) ((algebraMap A B) x)) =
        s_loc ((algebraMap B Ln) ((algebraMap A B) y)) := congrArg s_loc hxy
    have hx := congrFun (congrArg DFunLike.coe hs_loc_section) x
    have hy := congrFun (congrArg DFunLike.coe hs_loc_section) y
    simp only [RingHom.comp_apply, RingHom.id_apply] at hx hy
    rw [← hx, ← hy]
    exact hxy'
  · -- Surjectivity via the étale-cancellation helper.
    -- Strategy: show `aLn ∘ s_loc = id_Ln`. Then for any `z : Ln`, `aLn (s_loc z) = z`,
    -- exhibiting `s_loc z : A` as the preimage of `z` under `aLn`. To get the identity,
    -- we use `IsLocalization.ringHom_ext` (it suffices to check after precomposition
    -- with `algebraMap B Ln`). That reduces to: `algebraMap B Ln (algebraMap A B (s b)) =
    -- algebraMap B Ln b` for every `b ∈ B`, i.e., `algebraMap A B (s b) - b ∈ ker s` is
    -- annihilated in `Ln`. The étale-cancellation helper provides an idempotent
    -- `e ∈ B` generating `ker s`, and `e ∈ n` (since `s e = 0 ∈ m`), so `1 - e ∈
    -- n.primeCompl` kills every element of `ker s` in `Ln`.
    obtain ⟨e, he_idem, he_span⟩ := ker_idempotent_of_etale_section s
    -- `e ∈ n`: from `s e = 0 ∈ m` and `n = m.comap s.toRingHom`.
    have he_ker : e ∈ RingHom.ker s.toRingHom := by
      rw [he_span]; exact Ideal.subset_span rfl
    have hse : s.toRingHom e = 0 := he_ker
    have he_n : e ∈ n := by
      rw [hs]
      show s.toRingHom e ∈ IsLocalRing.maximalIdeal A
      rw [hse]; exact Submodule.zero_mem _
    -- `1 - e ∈ n.primeCompl`.
    have h1e_compl : (1 - e) ∈ n.primeCompl := by
      intro h_mem
      apply (‹n.IsMaximal›.isPrime).ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : e + (1 - e) = 1 := by ring
      rw [← h1]
      exact Ideal.add_mem _ he_n h_mem
    -- `algebraMap B Ln` annihilates `ker s`.
    have h_ker_zero : ∀ x ∈ RingHom.ker s.toRingHom,
        algebraMap B Ln x = 0 := by
      intro x hx
      rw [he_span, Ideal.mem_span_singleton] at hx
      obtain ⟨r, rfl⟩ := hx
      -- `(1 - e) * (e * r) = 0` from idempotence of `e`.
      have h_kill : (1 - e) * (e * r) = 0 := by
        have he2 : e * e = e := he_idem
        have : (1 - e) * (e * r) = (e - e * e) * r := by ring
        rw [this, he2]
        ring
      have hunit : IsUnit (algebraMap B Ln (1 - e)) :=
        IsLocalization.map_units Ln ⟨1 - e, h1e_compl⟩
      have hmul : algebraMap B Ln (1 - e) * algebraMap B Ln (e * r) = 0 := by
        rw [← map_mul, h_kill, map_zero]
      exact (IsUnit.mul_right_eq_zero hunit).mp hmul
    -- `aLn ∘ s_loc = id_Ln`.
    have h_aLn_sLoc :
        ((algebraMap B Ln).comp (algebraMap A B)).comp s_loc = RingHom.id Ln := by
      apply IsLocalization.ringHom_ext n.primeCompl (S := Ln)
      ext b
      show ((algebraMap B Ln).comp (algebraMap A B)) (s_loc (algebraMap B Ln b)) =
        algebraMap B Ln b
      have hsb : s_loc (algebraMap B Ln b) = s.toRingHom b :=
        RingHom.congr_fun hs_loc_comp_B b
      rw [hsb]
      -- Goal: algebraMap B Ln (algebraMap A B (s b)) = algebraMap B Ln b.
      have hin_ker : algebraMap A B (s.toRingHom b) - b ∈ RingHom.ker s.toRingHom := by
        show s.toRingHom (algebraMap A B (s.toRingHom b) - b) = 0
        rw [map_sub]
        have hsc : s.toRingHom (algebraMap A B (s.toRingHom b)) = s.toRingHom b := by
          simp [s.commutes]
        rw [hsc, sub_self]
      have hzero := h_ker_zero _ hin_ker
      rw [map_sub, sub_eq_zero] at hzero
      exact hzero
    -- Conclude surjectivity.
    intro z
    exact ⟨s_loc z, RingHom.congr_fun h_aLn_sLoc z⟩

end Algebra.Etale
