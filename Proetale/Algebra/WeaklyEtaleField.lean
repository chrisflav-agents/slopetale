/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.HopkinsLevitzki
import Proetale.Algebra.IndEtale
import Proetale.Algebra.WeakDimension
import Proetale.Algebra.WeaklyEtale
import Proetale.Mathlib.RingTheory.TensorProduct.Maps
import Proetale.Mathlib.RingTheory.WeaklyEtale.Localization

/-!
# Weakly étale algebras over a field

Let `K → L` be a weakly étale extension of fields. This file collects basic
properties of the tensor product `L ⊗[K] L` and the multiplication map
`μ : L ⊗[K] L → L`, in preparation for the proof of
[Stacks 092P](https://stacks.math.columbia.edu/tag/092P) (a weakly étale extension
of fields is separable algebraic).

## Main results

* `Algebra.WeaklyEtale.absolutelyFlat_tensor_self` —
  if `K → L` is weakly étale and `L` is absolutely flat (in particular,
  a field), then `L ⊗[K] L` is absolutely flat. Reducedness follows
  automatically from the general `Ring.AbsolutelyFlat ⇒ IsReduced` instance.

We also introduce the `L`-algebra evaluation map
`tensorEvalRight : L[X] →ₐ[L] L ⊗[K] L`, `X ↦ 1 ⊗ a`, and check its basic
properties (`X`, `C`, and `X - C a` evaluations, plus that composing with
multiplication recovers `Polynomial.aeval a`).
-/

universe u

open scoped TensorProduct

variable {k : Type u} [Field k] {R : Type u} [CommRing R] [Algebra k R]

namespace Algebra.WeaklyEtale

/-- For `K` a field and `R` weakly étale over `K`, every element of `R` is algebraic over
`K`. This is Stacks [0CKR] (3) / Stacks [092Q] part (2): a weakly étale algebra over a field
is integral over the field.

iter-129 status: trivial case (δ = 0 ⟹ a ∈ image K) closed via K-linear independence; the
substantive case δ ≠ 0 (where δ = 1 ⊗ a - a ⊗ 1) remains as a typed sub-sorry. The full
Stacks 092Q argument: `R` is absolutely flat (Stacks 092I), every prime of `R` is maximal,
the residue field `R/q` is weakly étale over `K`, hence by Stacks `absolutely-flat-fields`
it is separably algebraic over `K`. For `a ∈ R \ image(K)`, lifting a minimal prime of
`K[a]` to a prime `q` of `R` via `Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective`
gives `K[a]/p ↪ R/q`, hence `K[a]/p` is sep algebraic over `K`, hence finite (every elt
algebraic + FG = finite), hence `K[a]/p` is a field. Combined with `K[a]` reduced + dim 0,
`K[a]` is a finite product of finite separable extensions of `K`, in particular `a` is
algebraic over `K`. The substantive gap is the descent `K → R/q` weakly étale (requires
localizations preserve weak étaleness, which is Mathlib infrastructure not yet available
beyond the formally étale instance `Algebra.FormallyEtale.of_isLocalization`). -/
theorem isAlgebraic_of_weaklyEtale [WeaklyEtale k R] : Algebra.IsAlgebraic k R := by
  haveI : Ring.AbsolutelyFlat R :=
    Ring.AbsolutelyFlat.of_flat_lmul' k R (Algebra.WeaklyEtale.flat_lmul' k R)
  haveI : IsReduced R := inferInstance
  refine ⟨fun a => ?_⟩
  -- Handle the degenerate case R subsingleton (a = 0, satisfies X).
  by_cases hnt : Nontrivial R
  swap
  · rw [not_nontrivial_iff_subsingleton] at hnt
    refine ⟨Polynomial.X, Polynomial.X_ne_zero, ?_⟩
    simp [Subsingleton.elim a 0]
  -- Case split on whether `δ := 1 ⊗ a - a ⊗ 1` vanishes in `R ⊗_k R`.
  by_cases hδ : (1 ⊗ₜ[k] a - a ⊗ₜ[k] 1 : R ⊗[k] R) = 0
  · -- Trivial case δ = 0: by K-linear independence of `{1, a}` (when `a ∉ image k`), the
    -- tensor pair is also K-LI, so `1 ⊗ a = a ⊗ 1` forces `a ∈ image(algebraMap k R)`,
    -- whence `a` satisfies `X - C k_val` for some `k_val ∈ k`.
    have h_a_in_K : ∃ k_val : k, algebraMap k R k_val = a := by
      by_contra h_not_in_K
      simp only [not_exists] at h_not_in_K
      have hli : LinearIndependent k (![(1 : R), a]) := by
        rw [LinearIndependent.pair_iff' (one_ne_zero (α := R))]
        intro k' hk'
        apply h_not_in_K k'
        rw [Algebra.smul_def, mul_one] at hk'
        exact hk'
      have hli2 : LinearIndependent k
          (fun ij : Fin 2 × Fin 2 =>
            (![(1 : R), a] ij.1) ⊗ₜ[k] (![(1 : R), a] ij.2)) :=
        hli.tmul_of_flat_left hli
      have h_inj : Function.Injective (fun ij : Fin 2 × Fin 2 =>
          (![(1 : R), a] ij.1) ⊗ₜ[k] (![(1 : R), a] ij.2)) := hli2.injective
      have h_tmul_eq : (1 ⊗ₜ[k] a : R ⊗[k] R) = a ⊗ₜ[k] 1 := sub_eq_zero.mp hδ
      have h01_eq_10 : ((0 : Fin 2), (1 : Fin 2)) = ((1 : Fin 2), (0 : Fin 2)) := by
        apply h_inj
        simp [h_tmul_eq]
      simp at h01_eq_10
    obtain ⟨k_val, hk⟩ := h_a_in_K
    refine ⟨Polynomial.X - Polynomial.C k_val, Polynomial.X_sub_C_ne_zero k_val, ?_⟩
    simp [hk]
  · -- Substantive case δ ≠ 0: Stacks 092Q part (2). Per-prime route via the
    -- iter-142 Lane M closure `Algebra.WeaklyEtale.of_isLocalization` plus the
    -- L49 lemma `isAlgebraic` (Stacks 092P) above.
    --
    -- Strategy (single-prime version, avoiding the multi-prime product over
    -- minimal primes of `K[a]`):
    --   1. Set `A := Algebra.adjoin k {a} ⊆ R`. If `a` is algebraic, done; assume
    --      `a` is transcendental over `k`. Then `Polynomial.aeval a` is injective,
    --      so `A` is isomorphic to `k[X]`. In particular `A` is a domain, with
    --      unique minimal prime `(⊥)`.
    --   2. Lift `(⊥)` to a prime `q` of `R` via
    --      `Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective` applied to the
    --      injection `A.subtype : A → R`. By construction `A.subtype ⁻¹ q = ⊥`,
    --      i.e. `A ∩ q = 0` in `A`.
    --   3. `R` is absolutely flat ⇒ `Localization.AtPrime q` is a field.
    --      `Algebra.WeaklyEtale.of_isLocalization` (Lane M) gives
    --      `WeaklyEtale R (Localization.AtPrime q)`. Composing with `K → R` via
    --      `Algebra.WeaklyEtale.trans` yields `WeaklyEtale k (Localization.AtPrime q)`.
    --   4. Apply `isAlgebraic` (L49) to get
    --      `Algebra.IsSeparable k (Localization.AtPrime q)`, hence
    --      `Algebra.IsAlgebraic k (Localization.AtPrime q)`.
    --   5. The image of `a` in `Localization.AtPrime q` is algebraic over `k`, so
    --      there exists a non-zero `μ ∈ k[X]` with `μ` evaluated at the image equal
    --      to `0`. Pulling back along `R → Localization.AtPrime q`, this says
    --      `μ(a) ∈ q` in `R`.
    --   6. Since `μ(a) ∈ A` (it is `Polynomial.aeval a μ`) and `A ∩ q = 0`, we get
    --      `μ(a) = 0` in `A`, hence `0` in `R`. This contradicts `μ ≠ 0` and the
    --      injectivity of `Polynomial.aeval a` from transcendence.
    --
    -- The Lean translation of steps 5 and 6 turns on a clean injectivity argument
    -- through the composite `Polynomial k → A → R → Localization.AtPrime q`,
    -- whose kernel is `(0)` by injectivity of all three factors (and the chosen
    -- contraction `A.subtype ⁻¹ q = ⊥`). Step 6 is therefore a contradiction
    -- with the existence of any non-zero polynomial annihilating `a` in
    -- `Localization.AtPrime q`.
    --
    -- iter-143 status: per-prime weak-étale infrastructure laid out below
    -- (Lane M + transitivity + field-of-localization). The injectivity / kernel
    -- translation of step 6 is the remaining typed sub-sorry; it is structurally
    -- mechanical (chase through the algebraMap composition) and depends on
    -- L49 closing.
    classical
    by_contra h_not_alg
    -- Step 1: `a` not algebraic ⇒ `Polynomial.aeval a` is injective.
    have h_transc : Transcendental k a := h_not_alg
    have h_aeval_inj : Function.Injective
        (Polynomial.aeval a : Polynomial k →ₐ[k] R) :=
      transcendental_iff_injective.mp h_transc
    -- `A := adjoin k {a}`; `A.subtype` is injective; `A` is a domain via `aeval a`.
    let A : Subalgebra k R := Algebra.adjoin k ({a} : Set R)
    have hA_eq_range : (Polynomial.aeval a : Polynomial k →ₐ[k] R).range = A :=
      (Algebra.adjoin_singleton_eq_range_aeval k a).symm
    let φ : Polynomial k ≃ₐ[k] A :=
      (AlgEquiv.ofInjective (Polynomial.aeval a : Polynomial k →ₐ[k] R) h_aeval_inj).trans
        (Subalgebra.equivOfEq _ A hA_eq_range)
    haveI hA_domain : IsDomain A := φ.symm.toRingEquiv.toMulEquiv.isDomain (Polynomial k)
    have hAsub_inj : Function.Injective (A.subtype : A →+* R) := Subtype.val_injective
    -- Step 2: `(⊥)` is a minimal prime of `A` (domain); lift to prime `q` of `R`.
    have hbot_min : (⊥ : Ideal A) ∈ minimalPrimes A := by
      rw [IsDomain.minimalPrimes_eq_singleton_bot]
      exact rfl
    obtain ⟨q, hq_prime, hq_eq⟩ :=
      Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
        (f := (A.subtype : A →+* R)) hAsub_inj _ hbot_min
    haveI : q.IsPrime := hq_prime
    -- Step 3: `Localization.AtPrime q` is a field, weakly étale over `k`.
    have hIsField : IsField (Localization.AtPrime q) :=
      Ring.AbsolutelyFlat.isField_of_isLocalization_prime (R := R) q
        (Localization.AtPrime q)
    letI hLocField : Field (Localization.AtPrime q) := hIsField.toField
    haveI hloc_we_R : Algebra.WeaklyEtale R (Localization.AtPrime q) :=
      Algebra.WeaklyEtale.localization R q.primeCompl
    -- The `k`-algebra and scalar-tower instances on `Localization.AtPrime q` are
    -- automatic via the inherited `Algebra k R` structure.
    haveI hWE_kLoc : Algebra.WeaklyEtale k (Localization.AtPrime q) :=
      Algebra.WeaklyEtale.trans k R (Localization.AtPrime q)
    -- Step 4: algebraicity of `aLoc` (image of `a` in `Loc q`) over `k`.
    -- iter-144 file reorder: the headline `isAlgebraic` lemma (Stacks [092P]) sits
    -- BELOW this declaration so it can consume `etale_of_fg`; this declaration can
    -- no longer forward-reference it. The substitute below is a typed local sorry.
    --
    -- iter-146 investigation (cycle confirmed structural). The natural carriers for
    -- closure all transitively call `isAlgebraic_of_weaklyEtale` (this lemma):
    --   * `Algebra.WeaklyEtale.isAlgebraic` (this file, L332): consumes `etale_of_fg`.
    --   * `Algebra.WeaklyEtale.adjoin_singleton` (Subalgebra.lean): consumes
    --     `etale_of_fg`.
    --   * `Algebra.WeaklyEtale.isSeparable_algebraic_of_isField` (FieldExtension.lean):
    --     consumes both.
    --   * Mathlib `Algebra.FormallyUnramified.isSeparable` requires `EssFiniteType`,
    --     which `Loc q` does NOT satisfy (it is not f.t. over k).
    --   * Element-wise reduction to `F := IntermediateField.adjoin k {aLoc}` works
    --     for EssFT (F is a localization of f.g.), but requires
    --     `FormallyUnramified k F`. The FieldExtension.lean L455-486 derivation of
    --     this fact uses `Module.Finite K F`, which holds only in the algebraic case
    --     — itself the conclusion we are trying to reach.
    --   * The Stacks 092Q minimal-primes route (lift minimal primes of `k[aLoc]` to
    --     `Loc q`, identify `k[aLoc]/p` with a subring of `κ(q) = Loc q` which is
    --     separable algebraic over `k` by 092P) routes through 092P at residue
    --     fields — same cycle.
    --
    -- iter-147+ structural fix: introduce a subalgebra-descent of the pure-ideal
    -- property that does NOT route through `etale_of_fg`. Needed carrier shape:
    -- "if `K → L` is weakly étale with `L` a field and `a' ∈ L`, then `K → L'` is
    -- formally unramified for `L' := IntermediateField.adjoin K {a'}`". Proof
    -- skeleton: `L ⊗_K L` is absolutely flat (`absolutelyFlat_tensor_self` —
    -- already proved in this file at L376), hence its multiplication kernel
    -- `I_L` is pure, hence idempotent; the subring `L' ⊗_K L'` injects into
    -- `L ⊗_K L` via K-flatness, and its multiplication kernel `I_{L'}` is the
    -- contraction of `I_L`; idempotence of `I_L` ⇒ idempotence of `I_{L'}` once
    -- the descent for purity-along-flat-injection is provided. This Mathlib
    -- carrier is missing; FLAG for mathlib-analogist subagent in iter-147 plan.
    --
    -- The L195 obligation has been tightened to `IsAlgebraic k aLoc` (only the
    -- single element appearing downstream), strictly weaker than the iter-145
    -- recipe target `Algebra.IsSeparable k (Loc q)`.
    set aLoc : Localization.AtPrime q := algebraMap R (Localization.AtPrime q) a
      with haLoc_def
    have h_aLoc_alg : IsAlgebraic k aLoc := by
      -- Apply the same δ-dichotomy to `aLoc` in the WE k-field `Loc q`.
      -- If `1 ⊗ aLoc - aLoc ⊗ 1 = 0` in `Loc q ⊗_k Loc q`, then by K-linear
      -- independence of `{1, aLoc}` (when `aLoc ∉ image k`) and the K-flat
      -- tensor pairing, `aLoc` lies in `image (algebraMap k (Loc q))`, hence
      -- satisfies `X - C k_val` for some `k_val ∈ k`.
      by_cases hδLoc : (1 ⊗ₜ[k] aLoc - aLoc ⊗ₜ[k] 1 : Localization.AtPrime q ⊗[k]
          Localization.AtPrime q) = 0
      · -- Trivial sub-case: closed by `{1, aLoc}` K-linear independence + flat tensor.
        have h_aLoc_in_k : ∃ k_val : k, algebraMap k (Localization.AtPrime q) k_val = aLoc := by
          by_contra h_not_in_k
          simp only [not_exists] at h_not_in_k
          have hli : LinearIndependent k (![(1 : Localization.AtPrime q), aLoc]) := by
            rw [LinearIndependent.pair_iff' (one_ne_zero (α := Localization.AtPrime q))]
            intro k' hk'
            apply h_not_in_k k'
            rw [Algebra.smul_def, mul_one] at hk'
            exact hk'
          have hli2 : LinearIndependent k
              (fun ij : Fin 2 × Fin 2 =>
                (![(1 : Localization.AtPrime q), aLoc] ij.1) ⊗ₜ[k]
                  (![(1 : Localization.AtPrime q), aLoc] ij.2)) :=
            hli.tmul_of_flat_left hli
          have h_inj : Function.Injective (fun ij : Fin 2 × Fin 2 =>
              (![(1 : Localization.AtPrime q), aLoc] ij.1) ⊗ₜ[k]
                (![(1 : Localization.AtPrime q), aLoc] ij.2)) := hli2.injective
          have h_tmul_eq : (1 ⊗ₜ[k] aLoc : Localization.AtPrime q ⊗[k] Localization.AtPrime q) =
              aLoc ⊗ₜ[k] 1 := sub_eq_zero.mp hδLoc
          have h01_eq_10 : ((0 : Fin 2), (1 : Fin 2)) = ((1 : Fin 2), (0 : Fin 2)) := by
            apply h_inj
            simp [h_tmul_eq]
          simp at h01_eq_10
        obtain ⟨k_val, hk⟩ := h_aLoc_in_k
        refine ⟨Polynomial.X - Polynomial.C k_val, Polynomial.X_sub_C_ne_zero k_val, ?_⟩
        simp [hk]
      · -- Substantive sub-case: structural cycle. See block comment above.
        sorry
    obtain ⟨μ, hμ_ne, hμ_eval⟩ := h_aLoc_alg
    -- Step 6: derive a contradiction.
    -- Translate `Polynomial.aeval aLoc μ = 0` to `algebraMap R Loc (aeval a μ) = 0`
    -- using `aeval_algHom_apply` on the `k`-algebra map `R →ₐ[k] Loc`.
    have h_aeval_loc :
        algebraMap R (Localization.AtPrime q) (Polynomial.aeval a μ) = 0 := by
      have hcommute := Polynomial.aeval_algHom_apply
        (IsScalarTower.toAlgHom k R (Localization.AtPrime q)) a μ
      -- `hcommute : aeval (algebraMap R Loc a) μ = algebraMap R Loc (aeval a μ)`
      have hl : Polynomial.aeval (algebraMap R (Localization.AtPrime q) a) μ = 0 := by
        rw [← haLoc_def]; exact hμ_eval
      simpa [IsScalarTower.toAlgHom, hl] using hcommute.symm
    -- The kernel of `algebraMap R Loc` is detected via the localization at q.primeCompl.
    obtain ⟨⟨s, hs_not_in_q⟩, hsr⟩ :=
      (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) _).mp
        h_aeval_loc
    -- `s * aeval a μ = 0 ∈ q` and `s ∉ q`, so by primality `aeval a μ ∈ q`.
    have hmem_q : Polynomial.aeval a μ ∈ q := by
      have h_in : (s : R) * (Polynomial.aeval a μ) ∈ q := hsr ▸ q.zero_mem
      rcases hq_prime.mem_or_mem h_in with h | h
      · exact (hs_not_in_q h).elim
      · exact h
    -- `aeval a μ ∈ A` since `A` is the range of `aeval a`.
    have h_in_A : Polynomial.aeval a μ ∈ A := by
      rw [show A = (Polynomial.aeval a : Polynomial k →ₐ[k] R).range from hA_eq_range.symm]
      exact ⟨μ, rfl⟩
    -- Combine using `A.subtype ⁻¹ q = ⊥`: `aeval a μ` viewed in `A` is in `⊥`, hence `0`.
    let rA : A := ⟨Polynomial.aeval a μ, h_in_A⟩
    have hrA_in_comap : rA ∈ Ideal.comap (A.subtype : A →+* R) q := hmem_q
    rw [hq_eq, Ideal.mem_bot] at hrA_in_comap
    -- `rA = 0` in `A` ⇒ `aeval a μ = 0` in `R`.
    have h_aeval_zero : Polynomial.aeval a μ = 0 := by
      have hrA_zero : rA = (0 : A) := hrA_in_comap
      have : (rA : R) = ((0 : A) : R) := congrArg (·.val) hrA_zero
      simpa [rA] using this
    -- Injectivity of `aeval a` then forces `μ = 0`, contradicting `hμ_ne`.
    have hμ_zero : μ = 0 :=
      h_aeval_inj (by simp [h_aeval_zero])
    exact hμ_ne hμ_zero

/-- Any finitely-generated subalgebra of a weakly étale algebra is étale.

This is Stacks [0CKR] (3) / Stacks [092Q]: every finitely generated `K`-subalgebra of a
weakly étale `K`-algebra is étale over `K` (when `K` is a field).

**Proof outline (Stacks 092Q):**
1. `R` is absolutely flat (Stacks 092I), so reduced.
2. `A` is a finite product of finite separable field extensions of `K` (the substantive
   structural conclusion). We obtain this via:
   - `A` is integral over `K` (each element of `A ⊆ R` is algebraic — see
     `isAlgebraic_of_weaklyEtale`).
   - FG + integral ⇒ `Module.Finite K A`.
   - `A` is reduced + finite over `K` ⇒ `A` is Artinian + semisimple.
   - `A ⊗_K A` is similarly finite + reduced + semisimple. In a semisimple ring every
     ideal is generated by an idempotent, so `KaehlerDifferential.ideal K A` is idempotent.
   - Hence `Subsingleton Ω[A/K]`, i.e. `FormallyUnramified K A`.
3. Over an EssFiniteType base over a field, formally unramified ⇒ formally étale
   (`Algebra.FormallyEtale.of_formallyUnramified_of_field`).
4. Finite presentation follows from FG over the Noetherian base field. -/
lemma etale_of_fg [WeaklyEtale k R] (A : Subalgebra k R) (hA : A.FG) : Etale k A := by
  haveI hFT : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType _).mp hA
  -- `R` is absolutely flat (Stacks 092I): `k` is a field (hence absolutely flat), and a
  -- weakly étale algebra over an absolutely flat ring is absolutely flat.
  haveI hAFR : Ring.AbsolutelyFlat R :=
    Ring.AbsolutelyFlat.of_flat_lmul' k R (Algebra.WeaklyEtale.flat_lmul' k R)
  -- `R` is reduced (every absolutely flat ring is reduced), hence `A ⊆ R` is reduced.
  haveI : IsReduced R := inferInstance
  haveI hAred : IsReduced A := isReduced_of_injective A.subtype Subtype.val_injective
  -- Every element of `R` is algebraic over `k`; hence every element of `A ⊆ R` is
  -- integral over `k`.
  haveI : Algebra.IsAlgebraic k R := isAlgebraic_of_weaklyEtale
  haveI : Algebra.IsIntegral k R := Algebra.IsAlgebraic.isIntegral
  haveI : Algebra.IsIntegral k A := Algebra.IsIntegral.of_injective A.val Subtype.val_injective
  -- FG + integral over `k` ⇒ `Module.Finite k A`.
  haveI hFin : Module.Finite k A := Algebra.IsIntegral.finite
  haveI : Algebra.EssFiniteType k A := Algebra.EssFiniteType.of_finiteType k A
  -- `A` is a finite-dimensional `k`-algebra (so Artinian); reduced + Artinian ⇒ semisimple.
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : IsSemisimpleRing A := IsArtinianRing.isSemisimpleRing_of_isReduced A
  -- The tensor product `A ⊗_k A` is also finite over `k` (so Artinian), and injects into
  -- the reduced ring `R ⊗_k R` (which is reduced because `R` is absolutely flat over the
  -- field `k`, hence `R ⊗_k R` is absolutely flat).
  haveI hRRabsflat : Ring.AbsolutelyFlat (R ⊗[k] R) :=
    Ring.AbsolutelyFlat.of_flat_lmul' R (R ⊗[k] R)
      (Algebra.WeaklyEtale.flat_lmul' R (R ⊗[k] R))
  haveI : IsReduced (R ⊗[k] R) := inferInstance
  have hinj_AA : Function.Injective
      ((Algebra.TensorProduct.map A.val A.val).toRingHom : (A ⊗[k] A) →+* R ⊗[k] R) :=
    TensorProduct.map_injective_of_flat_flat _ _
      (Subtype.val_injective : Function.Injective ⇑A.val.toLinearMap)
      (Subtype.val_injective : Function.Injective ⇑A.val.toLinearMap)
  haveI hAAred : IsReduced (A ⊗[k] A) := isReduced_of_injective _ hinj_AA
  haveI : Module.Finite k (A ⊗[k] A) := Module.Finite.tensorProduct k A A
  haveI : IsArtinianRing (A ⊗[k] A) := IsArtinianRing.of_finite k (A ⊗[k] A)
  haveI : IsSemisimpleRing (A ⊗[k] A) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  -- In the semisimple ring `A ⊗_k A`, every ideal is generated by an idempotent. Applied
  -- to `KaehlerDifferential.ideal k A`, this makes the ideal idempotent, hence
  -- `Subsingleton Ω[A/k]`, i.e. `FormallyUnramified k A`.
  haveI : Algebra.FormallyUnramified k A := by
    obtain ⟨e, he, hsp⟩ :=
      IsSemisimpleRing.ideal_eq_span_idempotent (KaehlerDifferential.ideal k A)
    have hIdem : IsIdempotentElem (KaehlerDifferential.ideal k A) := by
      show KaehlerDifferential.ideal k A * KaehlerDifferential.ideal k A =
          KaehlerDifferential.ideal k A
      rw [hsp, Ideal.span_singleton_mul_span_singleton, he.eq]
    rw [Algebra.formallyUnramified_iff]
    exact (Ideal.cotangent_subsingleton_iff _).mpr hIdem
  -- FormallyUnramified + EssFiniteType over a field ⇒ FormallyEtale.
  haveI : Algebra.FormallyEtale k A :=
    Algebra.FormallyEtale.of_formallyUnramified_of_field k A
  -- FG over the Noetherian field `k` ⇒ FinitePresentation.
  haveI : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp hFT
  -- Étale = FormallyEtale + FinitePresentation.
  exact ⟨inferInstance, inferInstance⟩

/-- Any weakly étale extension of fields is separable algebraic.
This is Stacks [092P] / `lem:flat-tensor-over-field-imples-algebraic`.

iter-144 closure (Option B / file reorder): `isAlgebraic` consumes `etale_of_fg`
element-wise. For each `a : L`, the FG subalgebra `A := Algebra.adjoin k {a}` is
étale over `k` by `etale_of_fg`, hence module-finite over `k` (via
`Algebra.finite_adjoin_simple_of_isIntegral`, since `a` is algebraic by the
upstream `isAlgebraic_of_weaklyEtale`). A module-finite reduced domain over a
field is itself a field (`isField_of_isIntegral_of_isField'`), so we can apply
`Algebra.FormallyUnramified.isSeparable` to `A`. The separability of `a ∈ A`
transfers to `IsSeparable k a` via `minpoly.algHom_eq` along the injective
inclusion `A.val : A → L`.

The cycle with `isAlgebraic_of_weaklyEtale` (which historically consumed this
lemma) is broken by replacing the per-prime Step 4 call in that proof with a
typed local `sorry`. See the task report for the full structural story. -/
lemma isAlgebraic {L : Type u} [Field L] [Algebra k L] [WeaklyEtale k L] :
    Algebra.IsSeparable k L := by
  -- Algebraicity of `L` follows from `isAlgebraic_of_weaklyEtale` (which uses an
  -- internal typed `sorry` in its substantive δ ≠ 0 case after the iter-144 reorder).
  haveI hAlg : Algebra.IsAlgebraic k L := isAlgebraic_of_weaklyEtale
  refine ⟨fun a => ?_⟩
  have ha_int : IsIntegral k a := (hAlg.isAlgebraic a).isIntegral
  -- Set `A := Algebra.adjoin k {a}`, the FG `k`-subalgebra generated by `a`.
  let A : Subalgebra k L := Algebra.adjoin k ({a} : Set L)
  have ha_in_A : a ∈ A := Algebra.self_mem_adjoin_singleton k a
  have hA_fg : A.FG := ⟨{a}, by simp [A]⟩
  -- `A` is étale over `k` by `etale_of_fg`.
  haveI hEt : Algebra.Etale k A := etale_of_fg A hA_fg
  -- Module-finite over `k` (single generator + integral).
  haveI hAfin : Module.Finite k A := Algebra.finite_adjoin_simple_of_isIntegral ha_int
  -- `A ⊆ L` is a domain; a finite-dim reduced domain over a field is a field.
  haveI hAdom : IsDomain A := inferInstance
  haveI hAint : Algebra.IsIntegral k A := Algebra.IsIntegral.of_finite k A
  haveI hAisField : IsField A := isField_of_isIntegral_of_isField' (Field.toIsField k)
  letI : Field A := hAisField.toField
  -- EssFiniteType from FG.
  haveI hAfT : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType _).mp hA_fg
  haveI : Algebra.EssFiniteType k A := Algebra.EssFiniteType.of_finiteType k A
  -- `Etale ⇒ FormallyUnramified`. Apply `iff_isSeparable` to the field `A`.
  haveI : Algebra.FormallyUnramified k A := inferInstance
  haveI hAisSep : Algebra.IsSeparable k A := Algebra.FormallyUnramified.isSeparable k A
  -- Transfer separability of `⟨a, ha_in_A⟩ ∈ A` to `a ∈ L` via minpoly equality.
  have hsep_aA : IsSeparable k (⟨a, ha_in_A⟩ : A) := Algebra.IsSeparable.isSeparable k _
  have hmp : minpoly k a = minpoly k (⟨a, ha_in_A⟩ : A) :=
    minpoly.algHom_eq A.val Subtype.val_injective ⟨a, ha_in_A⟩
  rw [IsSeparable, hmp]
  exact hsep_aA

variable (k R) in
/-- Any weakly étale algebra over a field is ind-étale. -/
theorem indEtale_field [WeaklyEtale k R] : IndEtale k R :=
  sorry

/-- If `K → L` is weakly étale and `L` is absolutely flat (e.g. a field), then `L ⊗[K] L`
is absolutely flat.

Special case of Stacks [092I] (weakly étale algebras over absolutely flat rings are absolutely
flat) applied to the base change `L → L ⊗[K] L`. -/
instance absolutelyFlat_tensor_self (K L : Type u) [CommRing K] [CommRing L] [Algebra K L]
    [Ring.AbsolutelyFlat L] [Algebra.WeaklyEtale K L] :
    Ring.AbsolutelyFlat (L ⊗[K] L) :=
  Ring.AbsolutelyFlat.of_flat_lmul' L (L ⊗[K] L)
    (Algebra.WeaklyEtale.flat_lmul' L (L ⊗[K] L))

variable (K L : Type u) [CommRing K] [CommRing L] [Algebra K L]

/-- The `L`-algebra evaluation `L[X] →ₐ[L] L ⊗[K] L` sending `X` to `1 ⊗ a`.
The `L`-algebra structure on `L ⊗[K] L` is the standard `Algebra.TensorProduct`
one, where `c ∈ L` acts as `c ⊗ 1`. Composed with multiplication
`μ : L ⊗[K] L → L` this is `Polynomial.aeval a`. -/
noncomputable def tensorEvalRight (a : L) : Polynomial L →ₐ[L] L ⊗[K] L :=
  Polynomial.aeval (1 ⊗ₜ[K] a)

@[simp]
lemma tensorEvalRight_X (a : L) :
    tensorEvalRight K L a Polynomial.X = (1 ⊗ₜ[K] a : L ⊗[K] L) := by
  simp [tensorEvalRight]

@[simp]
lemma tensorEvalRight_C (a c : L) :
    tensorEvalRight K L a (Polynomial.C c) = (c ⊗ₜ[K] 1 : L ⊗[K] L) := by
  simp [tensorEvalRight, Algebra.TensorProduct.algebraMap_apply]

/-- Composing `tensorEvalRight K L a : L[X] → L ⊗[K] L` with multiplication
`μ : L ⊗[K] L → L` recovers `Polynomial.aeval a`. -/
lemma lmul'_comp_tensorEvalRight (a : L) (p : Polynomial L) :
    Algebra.TensorProduct.lmul' (R := K) (S := L) (tensorEvalRight K L a p) =
      Polynomial.aeval a p := by
  induction p using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c _ => simp [tensorEvalRight]

/-- `tensorEvalRight K L a` sends `X - C a` to the diagonal `1 ⊗ a - a ⊗ 1`. -/
lemma tensorEvalRight_X_sub_C (a : L) :
    tensorEvalRight K L a (Polynomial.X - Polynomial.C a) =
      (1 ⊗ₜ[K] a - a ⊗ₜ[K] 1 : L ⊗[K] L) := by
  simp

end Algebra.WeaklyEtale
