/-
Copyright (c) 2026 The Proetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Smooth.Flat
import Proetale.Mathlib.RingTheory.Etale.HenselianPairCharpolyDescent

/-!
# Idempotent lift along `mB` for étale algebras over henselian local rings

Shared L3a carrier module for
`Proetale/Mathlib/RingTheory/Etale/HenselianPair.lean` and
`Proetale/Mathlib/RingTheory/Etale/HenselianIdempotentLift.lean`.

This file hosts the per-idempotent Hensel-lift statement
`Algebra.Etale.lift_idempotent_henselianPair` (Stacks 0DXB / blueprint L3a)
together with its non-`idempotent_lift_limit` prerequisites:

* `Algebra.Etale.maximalIdeal_map_le_jacobson_bot` — integral going-up
  containment `mA·B ⊆ jacobson B`.
* `Algebra.Etale.isUnit_of_isUnit_quotient_mk_maximalIdeal_map` — Nakayama
  upgrade lifting units from `B ⧸ mA·B` to `B`.
* `Algebra.Etale.maximalIdeal_map_iInf_pow_eq_bot` — Krull intersection
  `⨅ n, (mA·B)^n = ⊥`.
* `Algebra.Etale.exists_seq_lift_of_henselianPair` — step-wise Newton
  iteration producing a Cauchy sequence in `B`.
* `Algebra.Etale.idempotent_lift_limit` — limit identification of the
  Newton sequence applied to `Y² - Y`. Delegates Newton-Cauchy →
  idempotent root to
  `Algebra.Etale.descend_root_from_mAB_newton` (Stacks 09XL).
* `Algebra.Etale.lift_idempotent_henselianPair` — wrapper packaging the
  hypotheses for `idempotent_lift_limit` and producing an honest idempotent.

The module split breaks an import cycle: `HenselianIdempotentLift.lean`
needs `lift_idempotent_henselianPair` to close
`exists_completeOrthogonalIdempotents_lift_of_henselian`, but the L4
assembly `henselianRing_map_maximalIdeal` in `HenselianPair.lean`
consumes that same idempotent-lift theorem. Placing L3a here, below
both downstream consumers, lets both import it without cycle.
-/

open IsLocalRing Polynomial

universe u

namespace Algebra.Etale

/-! ### Helper lemmas for the henselian-pair idempotent lift

These mirror the structure of the blueprint chapter
`lem:henselianPair-jac` / `lem:henselianPair-is-henselian`. The
Stacks 0DXB root-finding step is dispatched to
`Algebra.Etale.descend_root_from_mAB_newton`
(in `HenselianPairCharpolyDescent.lean`), while the surrounding
glue is closed mechanically.
-/

/-- Standalone restatement of the `jac` field of
`Algebra.Etale.henselianRing_map_maximalIdeal`:
the extended maximal ideal `mB := m·B` is contained in the
Jacobson radical of `B`. Same integral-going-up argument as the
`jac` field. -/
lemma maximalIdeal_map_le_jacobson_bot
    (A B : Type*) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤
      Ideal.jacobson (⊥ : Ideal B) := by
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
  refine le_sInf fun J hJ => ?_
  have hJmax : J.IsMaximal := hJ
  rw [Ideal.map_le_iff_le_comap]
  have hcomap : (J.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
  rw [IsLocalRing.eq_maximalIdeal hcomap]

/-- **Nakayama upgrade.** Under the henselian-pair hypotheses,
units modulo `mB` lift to units in `B`. This is purely the
Jacobson-local-hom statement `isLocalHom_of_le_jacobson_bot`
applied to the `jac` field. -/
lemma isUnit_of_isUnit_quotient_mk_maximalIdeal_map
    (A B : Type*) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    {x : B}
    (hx : IsUnit (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) x)) :
    IsUnit x := by
  haveI : IsLocalHom
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B))) :=
    isLocalHom_of_le_jacobson_bot _
      (maximalIdeal_map_le_jacobson_bot A B)
  exact IsUnit.of_map (Ideal.Quotient.mk _) _ hx

/-- **L1 (mB-adic separation).** Krull's intersection theorem in the
henselian-pair setting: under `IsNoetherianRing A + Module.Finite A B`,
the ring `B` is itself Noetherian and the iter-054 helper
`maximalIdeal_map_le_jacobson_bot` gives `mB ⊆ jacobson B`. Applying
Mathlib's `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson` (the
ideal-versus-module Krull statement) yields
`⨅ n, (mB)^n = ⊥` as an equality of ideals. This is the Stage 3
prerequisite of the Stacks 0DXB Hensel lift — it asserts
$\mathfrak m B$-adic separation of $B$, which together with the
Newton-step Cauchy sequence (Stage 2) singles out the unique limit
root in $B$. -/
lemma maximalIdeal_map_iInf_pow_eq_bot
    (A B : Type*) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] :
    ⨅ n : ℕ, ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ n = ⊥ := by
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hjac : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤
      Ideal.jacobson (⊥ : Ideal B) :=
    maximalIdeal_map_le_jacobson_bot A B
  convert! Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
    (I := (IsLocalRing.maximalIdeal A).map (algebraMap A B)) (M := B) hjac
  ext i
  rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]

/-- **L2 (Newton iteration / Stage 2 of Stacks 0DXB).**
Step-wise Newton iteration in the henselian-pair setting: given
$f \in B[Y]$ with $f(a_0) \in mB$ and $f'(a_0)$ a unit in $B$
(obtained from the Nakayama-upgraded `h_unit_B` via
`isUnit_of_isUnit_quotient_mk_maximalIdeal_map`), construct a
sequence $\{a_n\}$ in $B$ with $a_0$ the starting point,
$f(a_n) \in (mB)^{n+1}$ and $a_{n+1} - a_n \in (mB)^{n+1}$.

The recipe: define $a_{n+1} := a_n - f(a_n)\cdot u_n^{-1}$ where
$u_n := f'(a_n)$. The standard Taylor expansion
$f(a-\delta) = f(a) - f'(a)\delta + \delta^2 g(a,\delta)$
plus the unit-propagation
$f'(a_n) - f'(a_0) \in mB \subseteq \mathrm{jac}\,B$ gives the
two invariants by induction. iter-056 isolates this as a typed
helper; iter-057+ closes the body via the explicit Newton recursion
or the Stacks 04GE residue-product decomposition fallback. -/
lemma exists_seq_lift_of_henselianPair
    (A B : Type*) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B]
    (f : Polynomial B) (a₀ : B)
    (h_eval : f.eval a₀ ∈
      (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (h_unit : IsUnit (f.derivative.eval a₀)) :
    ∃ a : ℕ → B, a 0 = a₀ ∧
      (∀ n, f.eval (a n) ∈
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ (n + 1)) ∧
      (∀ n, a (n + 1) - a n ∈
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ (n + 1)) := by
  set mB : Ideal B := (IsLocalRing.maximalIdeal A).map (algebraMap A B) with hmB_def
  -- Unit propagation along `mB`-small perturbations: if `f'(b)` is a unit and
  -- `b' - b ∈ mB`, then `f'(b')` is also a unit. The image of `f'(b')` agrees
  -- with `f'(b)` in `B / mB`, so by the in-file Nakayama upgrade the unit lifts.
  have hprop : ∀ b b' : B, IsUnit (f.derivative.eval b) → b' - b ∈ mB →
      IsUnit (f.derivative.eval b') := fun b b' hu hd => by
    refine isUnit_of_isUnit_quotient_mk_maximalIdeal_map A B
      (x := f.derivative.eval b') ?_
    have hcong : f.derivative.eval b' - f.derivative.eval b ∈ mB := by
      obtain ⟨z, hz⟩ := f.derivative.evalSubFactor b' b
      exact hz ▸ Ideal.mul_mem_left mB z hd
    rw [Ideal.Quotient.eq.mpr hcong]
    exact hu.map (Ideal.Quotient.mk mB)
  -- Newton-step Taylor identity: `f(b - δ) = k · δ²` where `δ := f(b) · u⁻¹`.
  -- Direct application of `Polynomial.binomExpansion` with the cancellation
  -- `f'(b) · δ = f(b)`.
  have hnewton : ∀ (b : B) (hu : IsUnit (f.derivative.eval b)),
      ∃ k : B, f.eval (b - f.eval b * ((hu.unit⁻¹ : Bˣ) : B)) =
               k * (f.eval b * ((hu.unit⁻¹ : Bˣ) : B)) ^ 2 := by
    intro b hu
    obtain ⟨k, hk⟩ := f.binomExpansion b (-(f.eval b * ((hu.unit⁻¹ : Bˣ) : B)))
    refine ⟨k, ?_⟩
    have hf'inv : f.derivative.eval b * ((hu.unit⁻¹ : Bˣ) : B) = 1 :=
      Units.mul_inv_of_eq hu.unit_spec
    have hsub : b - f.eval b * ((hu.unit⁻¹ : Bˣ) : B) =
                b + -(f.eval b * ((hu.unit⁻¹ : Bˣ) : B)) := by ring
    rw [hsub, hk]
    have hpos : f.derivative.eval b * (f.eval b * ((hu.unit⁻¹ : Bˣ) : B)) =
                f.eval b := by
      calc f.derivative.eval b * (f.eval b * ((hu.unit⁻¹ : Bˣ) : B))
          = f.eval b * (f.derivative.eval b * ((hu.unit⁻¹ : Bˣ) : B)) := by ring
        _ = f.eval b * 1 := by rw [hf'inv]
        _ = f.eval b := mul_one _
    have hderiv : f.derivative.eval b * -(f.eval b * ((hu.unit⁻¹ : Bˣ) : B)) =
                  -f.eval b := by rw [mul_neg, hpos]
    rw [hderiv]; ring
  -- Build the sequence-with-witness by `Nat.rec`; each state carries
  -- `(b, IsUnit f'(b), f(b) ∈ mB)`. The weak `f(b) ∈ mB` invariant
  -- suffices to define the step; the stronger `mB^(n+1)` invariant is
  -- established afterwards by induction.
  let stepFn : (Σ' b : B, IsUnit (f.derivative.eval b) ∧ f.eval b ∈ mB) →
      Σ' b : B, IsUnit (f.derivative.eval b) ∧ f.eval b ∈ mB := fun p =>
    let b := p.1
    let hu : IsUnit (f.derivative.eval b) := p.2.1
    let he : f.eval b ∈ mB := p.2.2
    let δ : B := f.eval b * ((hu.unit⁻¹ : Bˣ) : B)
    have hδmB : δ ∈ mB := Ideal.mul_mem_right _ mB he
    have hdiff : (b - δ) - b ∈ mB := by
      have heq : (b - δ) - b = -δ := by ring
      exact heq ▸ (Ideal.neg_mem_iff _).mpr hδmB
    have hu' : IsUnit (f.derivative.eval (b - δ)) := hprop b (b - δ) hu hdiff
    have he' : f.eval (b - δ) ∈ mB := by
      obtain ⟨k, hk⟩ := hnewton b hu
      rw [show f.eval (b - δ) = k * δ ^ 2 from hk]
      refine Ideal.mul_mem_left mB k ?_
      rw [pow_two]
      exact Ideal.mul_mem_left mB δ hδmB
    ⟨b - δ, hu', he'⟩
  let seq : ℕ → Σ' b : B, IsUnit (f.derivative.eval b) ∧ f.eval b ∈ mB :=
    fun n => Nat.rec ⟨a₀, h_unit, h_eval⟩ (fun _ s => stepFn s) n
  let a : ℕ → B := fun n => (seq n).1
  -- Strong invariant: `f.eval (a n) ∈ mB ^ (n + 1)`.
  -- Induction step uses `hnewton` to express `f.eval (a (n+1)) = k · δ_n²`,
  -- then `δ_n² ∈ mB^(2(n+1)) ⊆ mB^(n+2)`.
  have hf_strong : ∀ n, f.eval (a n) ∈ mB ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      change f.eval a₀ ∈ mB ^ 1
      rw [pow_one]
      exact h_eval
    | succ n ih =>
      change f.eval (stepFn (seq n)).1 ∈ mB ^ (n + 1 + 1)
      show f.eval ((seq n).1 - f.eval (seq n).1 *
            (((seq n).2.1.unit⁻¹ : Bˣ) : B)) ∈ mB ^ (n + 1 + 1)
      obtain ⟨k, hk⟩ := hnewton (seq n).1 (seq n).2.1
      rw [hk]
      have hδ_in : f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B) ∈
          mB ^ (n + 1) := Ideal.mul_mem_right _ _ ih
      have hδ_sq : (f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B)) ^ 2 ∈
          mB ^ (2 * (n + 1)) := by
        rw [pow_two, two_mul, pow_add]
        exact Ideal.mul_mem_mul hδ_in hδ_in
      have hle : mB ^ (2 * (n + 1)) ≤ mB ^ (n + 1 + 1) :=
        Ideal.pow_le_pow_right (by omega)
      exact Ideal.mul_mem_left (mB ^ (n + 1 + 1)) k (hle hδ_sq)
  refine ⟨a, rfl, hf_strong, ?_⟩
  intro n
  change (stepFn (seq n)).1 - (seq n).1 ∈ mB ^ (n + 1)
  show ((seq n).1 - f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B)) -
        (seq n).1 ∈ mB ^ (n + 1)
  have hδ_in : f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B) ∈
      mB ^ (n + 1) := Ideal.mul_mem_right _ _ (hf_strong n)
  have heq : ((seq n).1 - f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B)) -
              (seq n).1 = -(f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B)) := by
    ring
  rw [heq]
  exact (Ideal.neg_mem_iff _).mpr hδ_in

/-- **L3a sub-sub-helper — Limit identification for the residue
idempotent lift.**

iter-143 inline rewrite (Option (c)): applies the polynomial
`f := X^2 - X ∈ B[X]` and dispatches the Newton-Cauchy → root step
directly to the `[IsLocalRing B]`-free suffix endpoint
`Algebra.Etale.descend_root_from_mAB_newton`, which carries the
substantive Stacks 09XL Cayley–Hamilton + henselian-`A` content.

* `f.eval e₀ = e₀^2 - e₀ ∈ mB` directly from `_hf_eval`.
* `f.derivative = 2 X - 1`, so `f.derivative.eval e₀ = 2 e₀ - 1`,
  which is a unit in `B ⧸ mB` (hypothesis `_hf_unit`); the in-file
  Nakayama upgrade `isUnit_of_isUnit_quotient_mk_maximalIdeal_map`
  promotes it to a genuine unit in `B`.
* `f = X^2 - X` is monic (degree 2) via `Polynomial.monic_X_pow_sub`.
* The root `e ∈ B` produced by `descend_root_from_mAB_newton`
  satisfies `f.IsRoot e`, hence `e^2 - e = 0`, i.e. `e^2 = e`,
  together with `e - e₀ ∈ mB`. -/
private lemma idempotent_lift_limit
    (A B : Type*) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B]
    (e₀ : B)
    (_hf_eval : e₀ ^ 2 - e₀ ∈
      (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (_hf_unit : IsUnit (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B))
      (2 * e₀ - 1))) :
    ∃ e : B, e ^ 2 = e ∧
      e - e₀ ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
  set mB : Ideal B := (IsLocalRing.maximalIdeal A).map (algebraMap A B) with hmB_def
  -- Polynomial setup: `f := X^2 - X ∈ B[X]`.
  set f : Polynomial B := Polynomial.X ^ 2 - Polynomial.X with hf_def
  -- Evaluation identity: `f.eval e₀ = e₀^2 - e₀`.
  have hf_eval_eq : f.eval e₀ = e₀ ^ 2 - e₀ := by
    simp [hf_def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  -- Derivative identity: `f.derivative = 2 X - 1`.
  have hf_deriv_eq : f.derivative = 2 * Polynomial.X - 1 := by
    simp [hf_def, Polynomial.derivative_sub,
      Polynomial.derivative_X, sq, mul_comm]
    ring
  have hf_deriv_eval : f.derivative.eval e₀ = 2 * e₀ - 1 := by
    rw [hf_deriv_eq]
    simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one, Polynomial.eval_X]
  -- Promote the residue-unit hypothesis to a genuine unit in `B` via
  -- the in-file Nakayama upgrade.
  have h_unit_B : IsUnit (f.derivative.eval e₀) := by
    rw [hf_deriv_eval]
    exact isUnit_of_isUnit_quotient_mk_maximalIdeal_map A B _hf_unit
  -- Evaluation hypothesis in the form required by `exists_seq_lift_of_henselianPair`.
  have h_eval_B : f.eval e₀ ∈ mB := by
    rw [hf_eval_eq]
    exact _hf_eval
  -- Monicity of `f = X^2 - X`: degree of `X` is `< 2`, so apply
  -- `Polynomial.monic_X_pow_sub`.
  have hg : f.Monic := by
    rw [hf_def]
    exact Polynomial.monic_X_pow_sub
      (lt_of_le_of_lt Polynomial.degree_X_le (by decide))
  -- `B` is a finite, flat module over a local ring, hence free.
  haveI : Module.Free A B := Module.free_of_flat_of_isLocalRing
  -- Build the Newton-step Cauchy sequence via the in-file iter-057 helper.
  obtain ⟨a, ha0, ha_eval, ha_diff⟩ :=
    exists_seq_lift_of_henselianPair A B f e₀ h_eval_B h_unit_B
  -- iter-143 Option (c): inline dispatch to the substantive Stacks 09XL
  -- Cayley–Hamilton descent endpoint. The closeness conclusion is
  -- already `e - e₀ ∈ mB` (since `descend_root_from_mAB_newton`
  -- subtracts the original basepoint `e₀`, not `a 0`).
  obtain ⟨e, he_eval, he_diff⟩ :=
    descend_root_from_mAB_newton (A := A) (B := B) f hg e₀ h_unit_B a ha0
      ha_eval ha_diff
  refine ⟨e, ?_, he_diff⟩
  -- `f.IsRoot e` unfolds to `f.eval e = 0`; rewrite as `e^2 - e = 0`.
  have heval_e : f.eval e = e ^ 2 - e := by
    simp [hf_def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
  have hsq : e ^ 2 - e = 0 := by rw [← heval_e]; exact he_eval
  linear_combination hsq

/-- **L3a — Idempotent lift along `mB`.**

iter-061 wrapper: routes the substantive limit-identification step
through the named typed sub-sub-helper `idempotent_lift_limit`
above. The body verifies the two hypotheses required by that
sub-sub-helper (the residue square-zero invariant
`e₀^2 - e₀ ∈ mB` and the unit-residue invariant
`IsUnit (mk (2 e₀ - 1))`) directly from the idempotent witness
`_hidem` and the surjectivity of the quotient map, and packages
the resulting `e^2 = e` witness as `IsIdempotentElem e`.

Given an idempotent `ē` in the quotient ring `B ⧸ mB`, lift it to
an idempotent `e` in `B` with the same residue. -/
lemma lift_idempotent_henselianPair
    (A B : Type*) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B]
    (ē : B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (_hidem : IsIdempotentElem ē) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) e = ē := by
  -- Pick a preimage `e₀ ∈ B` of `ē`.
  obtain ⟨e₀, he₀⟩ := Ideal.Quotient.mk_surjective ē
  -- Verify `e₀^2 - e₀ ∈ mB` from `ē * ē = ē` (the idempotent witness).
  have hf_eval : e₀ ^ 2 - e₀ ∈
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hmap : Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B))
          (e₀ ^ 2 - e₀) =
        (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) e₀) *
          (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) e₀) -
        Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) e₀ := by
      rw [map_sub, sq, map_mul]
    have hid : ē * ē = ē := isIdempotentElem_iff.mp _hidem
    rw [hmap, he₀, hid, sub_self]
  -- Verify `2 e₀ - 1` is a unit in `B ⧸ mB`: its square equals `1`
  -- since `(2 e₀ - 1)^2 = 1 + 4 (e₀^2 - e₀)` and `e₀^2 - e₀ ∈ mB`.
  have hf_unit : IsUnit (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) (2 * e₀ - 1)) := by
    refine IsUnit.of_pow_eq_one (n := 2) ?_ two_ne_zero
    rw [← map_pow]
    have heq : (2 * e₀ - 1) ^ 2 = 1 + 4 * (e₀ ^ 2 - e₀) := by ring
    rw [heq, map_add, map_one]
    have h4 : Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B))
          (4 * (e₀ ^ 2 - e₀)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ 4 hf_eval
    rw [h4, add_zero]
  -- Invoke the sub-sub-helper for the substantive limit identification.
  obtain ⟨e, he_sq, he_diff⟩ :=
    idempotent_lift_limit (A := A) (B := B) e₀ hf_eval hf_unit
  refine ⟨e, ?_, ?_⟩
  · -- `IsIdempotentElem e` unfolds to `e * e = e`; use `he_sq : e^2 = e`.
    rw [isIdempotentElem_iff, ← sq]
    exact he_sq
  · -- `mk e = ē` reduces to `e - e₀ ∈ mB` via `he₀ : mk e₀ = ē`.
    rw [← he₀, Ideal.Quotient.eq]
    exact he_diff

end Algebra.Etale
