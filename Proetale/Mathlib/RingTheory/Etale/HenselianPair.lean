/-
Copyright (c) 2026 The Proetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Henselian pair for étale algebras over henselian local rings

For `A` a henselian local ring and `B` an étale `A`-algebra, the
pair `(B, m·B)` is a henselian ring in the sense of Mathlib's
`HenselianRing` class (which is equivalently the henselian-pair
predicate from Stacks 09XD). This is the Stacks 04GG / 0DXB
fragment that unblocks the §3-cluster of strictly-henselian
results in `Proetale/Mathlib/RingTheory/Etale/StrictlyHenselian.lean`
and the Hensel-idempotent-lift body of
`Proetale/Mathlib/RingTheory/Etale/HenselianIdempotentLift.lean`.

## Main result

* `Algebra.Etale.henselianRing_map_maximalIdeal`:
  `HenselianRing B ((maximalIdeal A).map (algebraMap A B))` for `A`
  henselian local and `B` étale over `A`.

See `blueprint/src/chapters/Proetale_Mathlib_RingTheory_Etale_HenselianPair.tex`
for the informal proof recipe (Jacobson containment via
Stacks 02FK + Hensel lift via Stacks 0DXB residue-product reduction).
-/

open IsLocalRing Polynomial

namespace Algebra.Etale

/-! ### Helper lemmas for the henselian-pair construction

These mirror the structure of the blueprint chapter
`lem:henselianPair-jac` / `lem:henselianPair-is-henselian`. They
are decomposed so that the residual sorry (the Stacks 0DXB
root-finding step) is isolated as a typed sub-claim with the
correct shape, while the surrounding glue is closed mechanically.
-/

/-- Standalone restatement of the `jac` field of
`Algebra.Etale.henselianRing_map_maximalIdeal`:
the extended maximal ideal `mB := m·B` is contained in the
Jacobson radical of `B`. Same integral-going-up argument as the
`jac` field. -/
private lemma maximalIdeal_map_le_jacobson_bot
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
private lemma isUnit_of_isUnit_quotient_mk_maximalIdeal_map
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

/-! **Note on L1 (mB-adic separation).** With `[IsNoetherianRing A]`
now in the signature, `Module.Finite A B` gives `IsNoetherianRing B`
via `IsNoetherianRing.of_finite`, so `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`
applied to `mB ⊆ jacobson B` closes the Krull-intersection step.
The substantive Newton/0DXB closure of
`exists_root_of_eval_mem_of_isUnit_derivative_quotient` below is
left to iter-057+. -/

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
private lemma maximalIdeal_map_iInf_pow_eq_bot
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
private lemma exists_seq_lift_of_henselianPair
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

iter-061 sub-sub-helper (typed sorry; closure deferred to iter-062+).
The substantive limit-identification step extracted from
`lift_idempotent_henselianPair`: given an element `e₀ ∈ B` whose
square is congruent to itself modulo `mB := mA · B` and whose
derivative residue `2 e₀ - 1` is a unit in `B ⧸ mB`, produce an
honest idempotent `e ∈ B` whose `mB`-residue equals that of `e₀`.

The plan signature mirrors the L3a body's two
hypothesis-verification outputs verbatim. The substantive proof
uses the iter-057 Cauchy-sequence helper
`exists_seq_lift_of_henselianPair` applied to `Y ^ 2 - Y` together
with limit identification: either via descent to `A` through the
multiplication-by-`e₀` characteristic polynomial and `A`'s
henselianness, or via the same multivariate Cayley–Hamilton machinery
isolated in `exists_root_in_finite_henselian_module` (the L3c-newton
sub-sub-helper from iter-060) specialised to the single-variable
polynomial `Y ^ 2 - Y`. -/
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
  -- Substantive step (deferred): the iter-057 helper
  -- `exists_seq_lift_of_henselianPair` applied to `Y ^ 2 - Y` produces a
  -- Cauchy sequence `(aₙ)` with `aₙ^2 - aₙ ∈ (mB)^{n+1}` and
  -- `aₙ₊₁ - aₙ ∈ (mB)^{n+1}`. Limit identification is the residual gap;
  -- candidate routes are (i) descent to `A` via the characteristic
  -- polynomial of multiplication-by-`e₀` plus `A`'s henselianness, or
  -- (ii) specialisation of `exists_root_in_finite_henselian_module` at
  -- `g := Y ^ 2 - Y` once the L3c-newton convergence is in place.
  sorry

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
private lemma lift_idempotent_henselianPair
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

/-- **L3c-helper — `mA·B ⊆ mB` in the local-finite case.**

iter-060 helper for `henselianLocalRing_of_finite_over_henselianLocal`.
A short, self-contained restatement of `maximalIdeal_map_le_jacobson_bot`
specialised to the `[IsLocalRing B]` hypothesis (without Noetherianness
on `A`), in which case `jacobson ⊥ = maximalIdeal B`. The proof is the
same integral going-up argument as in `jac`.

Note: this consumes only the finite + local hypotheses (no
Noetherianness on `A`), so it is available wherever
`henselianLocalRing_of_finite_over_henselianLocal` is. -/
private lemma maximalIdeal_map_le_maximalIdeal
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B] :
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤
      IsLocalRing.maximalIdeal B := by
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  rw [Ideal.map_le_iff_le_comap]
  have hcomap : ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  rw [IsLocalRing.eq_maximalIdeal hcomap]

/-- **L3c-newton helper (local Nakayama).** Local-case variant of
`isUnit_of_isUnit_quotient_mk_maximalIdeal_map`: under the
`[IsLocalRing B]` + `[Module.Finite A B]` hypotheses (without
Noetherianness on `A`), a unit modulo `mA·B` lifts to a unit in
`B`. Uses `maximalIdeal_map_le_maximalIdeal` plus the locality of
`B` to access the Jacobson containment. -/
private lemma isUnit_of_isUnit_quotient_mk_maximalIdeal_map_local
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    {x : B}
    (hx : IsUnit (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) x)) :
    IsUnit x := by
  have hjac : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤
      Ideal.jacobson (⊥ : Ideal B) := by
    refine le_trans (maximalIdeal_map_le_maximalIdeal A B) ?_
    intro y hy
    rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
    refine Submodule.mem_sInf.mpr fun J hJ => ?_
    have hJeq : J = IsLocalRing.maximalIdeal B :=
      IsLocalRing.eq_maximalIdeal hJ
    exact hJeq ▸ hy
  haveI : IsLocalHom (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B))) :=
    isLocalHom_of_le_jacobson_bot _ hjac
  exact IsUnit.of_map (Ideal.Quotient.mk _) _ hx

/-- **L3c-newton helper (nilpotency).** The image of `mB` in
`B ⧸ (mA·B)` is contained in the Jacobson radical, which is
nilpotent by Hopkins–Levitzki because `B ⧸ (mA·B)` is Artinian
(it is a finite module over the field `A ⧸ mA`). Hence
`∃ N, (mB)^N ⊆ mA·B`. -/
private lemma exists_maximalIdeal_pow_le_map_maximalIdeal
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B] :
    ∃ N : ℕ, (IsLocalRing.maximalIdeal B) ^ N ≤
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
  -- `mA·B` is a proper ideal (contained in the proper ideal `mB`).
  have hmAB_le_mB : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤
      IsLocalRing.maximalIdeal B := maximalIdeal_map_le_maximalIdeal A B
  have hne : ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ≠ ⊤ := by
    intro hcontra
    have hmB_top : IsLocalRing.maximalIdeal B = ⊤ :=
      top_le_iff.mp (hcontra ▸ hmAB_le_mB)
    exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top hmB_top
  -- `(mA·B).LiesOver mA`: comap of `mA·B` is a proper ideal containing `mA`,
  -- and `mA` is maximal, so equals `mA`.
  haveI : ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).LiesOver
      (IsLocalRing.maximalIdeal A) := by
    refine ⟨?_⟩
    have hle :
        IsLocalRing.maximalIdeal A ≤
          ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).under A := by
      intro a ha
      simp only [Ideal.under_def, Ideal.mem_comap]
      exact Ideal.mem_map_of_mem _ ha
    have hcomap_ne_top :
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).under A ≠ ⊤ := by
      intro h
      apply hne
      rw [Ideal.eq_top_iff_one] at h ⊢
      simpa [Ideal.under_def, Ideal.mem_comap] using h
    exact (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le hcomap_ne_top hle
  -- `Module.Finite (A ⧸ mA) (B ⧸ (mA·B))` via the `LiesOver` instance.
  haveI : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A)
      (B ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B))) := inferInstance
  -- `A ⧸ mA` is the residue field of `A`, hence Artinian.
  haveI : IsArtinianRing (A ⧸ IsLocalRing.maximalIdeal A) :=
    (inferInstance : IsArtinianRing (IsLocalRing.ResidueField A))
  -- Hence `B ⧸ (mA·B)` is Artinian (finite module over an Artinian ring).
  haveI : IsArtinianRing
      (B ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A B))) :=
    IsArtinianRing.of_finite (A ⧸ IsLocalRing.maximalIdeal A) _
  -- Apply `IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`.
  exact IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    ((IsLocalRing.maximalIdeal A).map (algebraMap A B))

/-- **L3c-newton helper (Newton sequence in `B`).** Local-case
analogue of `exists_seq_lift_of_henselianPair`: from a monic
polynomial `g ∈ B[X]` with `g(b₀) ∈ mB` and `g'(b₀)` a unit in `B`,
build the Newton sequence `b_{n+1} := b_n - g(b_n) · g'(b_n)⁻¹`
satisfying `g(b_n) ∈ mB^{n+1}` and `b_{n+1} - b_n ∈ mB^{n+1}`. The
unit-propagation step uses the local Nakayama variant
`isUnit_of_isUnit_quotient_mk_maximalIdeal_map_local`. -/
private lemma exists_seq_lift_of_finite_henselian_local
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    (f : Polynomial B) (a₀ : B)
    (h_eval : f.eval a₀ ∈ IsLocalRing.maximalIdeal B)
    (h_unit : IsUnit (f.derivative.eval a₀)) :
    ∃ a : ℕ → B, a 0 = a₀ ∧
      (∀ n, f.eval (a n) ∈ (IsLocalRing.maximalIdeal B) ^ (n + 1)) ∧
      (∀ n, a (n + 1) - a n ∈ (IsLocalRing.maximalIdeal B) ^ (n + 1)) := by
  set mB : Ideal B := IsLocalRing.maximalIdeal B with hmB_def
  -- Unit propagation along `mB`-small perturbations: since `B` is local
  -- and `mB` is the maximal ideal, an element whose residue equals a unit
  -- residue is itself a unit (`IsLocalRing.isUnit_of_mem_nonunits_one_sub` /
  -- `IsLocalRing.isUnit_iff_isUnit_residue`).
  have hprop : ∀ b b' : B, IsUnit (f.derivative.eval b) → b' - b ∈ mB →
      IsUnit (f.derivative.eval b') := fun b b' hu hd => by
    have hcong : f.derivative.eval b' - f.derivative.eval b ∈ mB := by
      obtain ⟨z, hz⟩ := f.derivative.evalSubFactor b' b
      exact hz ▸ Ideal.mul_mem_left mB z hd
    -- Pass through the residue field: `f'(b')` and `f'(b)` have the same
    -- image in `B ⧸ mB`; since `f'(b)` is a unit, its residue is a unit,
    -- hence so is the residue of `f'(b')`; pull back via locality of `B`.
    have hres :
        Ideal.Quotient.mk mB (f.derivative.eval b') =
          Ideal.Quotient.mk mB (f.derivative.eval b) := by
      rw [Ideal.Quotient.eq]; exact hcong
    have hunit_res : IsUnit (Ideal.Quotient.mk mB (f.derivative.eval b')) := by
      rw [hres]; exact hu.map _
    -- Use the fact `mB = jacobson ⊥` in the local ring `B`.
    haveI : IsLocalHom (Ideal.Quotient.mk mB) := by
      refine isLocalHom_of_le_jacobson_bot _ ?_
      intro x hx
      rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
      refine Submodule.mem_sInf.mpr fun J hJ => ?_
      have hJeq : J = IsLocalRing.maximalIdeal B :=
        IsLocalRing.eq_maximalIdeal hJ
      exact hJeq ▸ hx
    exact IsUnit.of_map (Ideal.Quotient.mk mB) _ hunit_res
  -- Newton-step Taylor identity (verbatim from `exists_seq_lift_of_henselianPair`).
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
  -- Build the sequence-with-witness via `Nat.rec`.
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

/-- **L3c-charpoly Newton sub-helper — `mA·B`-power filtration.**

iter-064 sorry-free helper: build the Newton sequence
`a_{n+1} := a_n - g(a_n) · g'(a_n)⁻¹` for the *strengthened*
hypothesis `f(a₀) ∈ mA·B` (rather than `mB`), with the resulting
invariants `f(a n) ∈ (mA·B)^{n+1}` and `a(n+1) - a n ∈ (mA·B)^{n+1}`.
This is the same construction as
`exists_seq_lift_of_finite_henselian_local` (iter-062, mB-filtered)
but with the `mA·B`-filtration throughout. The unit-propagation step
uses the local Nakayama variant
`isUnit_of_isUnit_quotient_mk_maximalIdeal_map_local` applied to the
quotient `B ⧸ mA·B`. -/
private lemma exists_seq_lift_of_finite_henselian_mAB
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    (f : Polynomial B) (a₀ : B)
    (h_eval : f.eval a₀ ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (h_unit : IsUnit (f.derivative.eval a₀)) :
    ∃ a : ℕ → B, a 0 = a₀ ∧
      (∀ n, f.eval (a n) ∈
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ (n + 1)) ∧
      (∀ n, a (n + 1) - a n ∈
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ (n + 1)) := by
  set mAB : Ideal B := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
    with hmAB_def
  -- Unit propagation along `mAB`-small perturbations via the local
  -- Nakayama helper `isUnit_of_isUnit_quotient_mk_maximalIdeal_map_local`.
  have hprop : ∀ b b' : B, IsUnit (f.derivative.eval b) → b' - b ∈ mAB →
      IsUnit (f.derivative.eval b') := fun b b' hu hd => by
    have hcong : f.derivative.eval b' - f.derivative.eval b ∈ mAB := by
      obtain ⟨z, hz⟩ := f.derivative.evalSubFactor b' b
      exact hz ▸ Ideal.mul_mem_left mAB z hd
    have hres :
        Ideal.Quotient.mk mAB (f.derivative.eval b') =
          Ideal.Quotient.mk mAB (f.derivative.eval b) := by
      rw [Ideal.Quotient.eq]; exact hcong
    have hunit_res :
        IsUnit (Ideal.Quotient.mk mAB (f.derivative.eval b')) := by
      rw [hres]; exact hu.map _
    exact isUnit_of_isUnit_quotient_mk_maximalIdeal_map_local A B hunit_res
  -- Newton-step Taylor identity (verbatim from `exists_seq_lift_of_henselianPair`).
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
  -- Build the sequence-with-witness via `Nat.rec`.
  let stepFn : (Σ' b : B, IsUnit (f.derivative.eval b) ∧ f.eval b ∈ mAB) →
      Σ' b : B, IsUnit (f.derivative.eval b) ∧ f.eval b ∈ mAB := fun p =>
    let b := p.1
    let hu : IsUnit (f.derivative.eval b) := p.2.1
    let he : f.eval b ∈ mAB := p.2.2
    let δ : B := f.eval b * ((hu.unit⁻¹ : Bˣ) : B)
    have hδmAB : δ ∈ mAB := Ideal.mul_mem_right _ mAB he
    have hdiff : (b - δ) - b ∈ mAB := by
      have heq : (b - δ) - b = -δ := by ring
      exact heq ▸ (Ideal.neg_mem_iff _).mpr hδmAB
    have hu' : IsUnit (f.derivative.eval (b - δ)) := hprop b (b - δ) hu hdiff
    have he' : f.eval (b - δ) ∈ mAB := by
      obtain ⟨k, hk⟩ := hnewton b hu
      rw [show f.eval (b - δ) = k * δ ^ 2 from hk]
      refine Ideal.mul_mem_left mAB k ?_
      rw [pow_two]
      exact Ideal.mul_mem_left mAB δ hδmAB
    ⟨b - δ, hu', he'⟩
  let seq : ℕ → Σ' b : B, IsUnit (f.derivative.eval b) ∧ f.eval b ∈ mAB :=
    fun n => Nat.rec ⟨a₀, h_unit, h_eval⟩ (fun _ s => stepFn s) n
  let a : ℕ → B := fun n => (seq n).1
  have hf_strong : ∀ n, f.eval (a n) ∈ mAB ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      change f.eval a₀ ∈ mAB ^ 1
      rw [pow_one]
      exact h_eval
    | succ n ih =>
      change f.eval (stepFn (seq n)).1 ∈ mAB ^ (n + 1 + 1)
      show f.eval ((seq n).1 - f.eval (seq n).1 *
            (((seq n).2.1.unit⁻¹ : Bˣ) : B)) ∈ mAB ^ (n + 1 + 1)
      obtain ⟨k, hk⟩ := hnewton (seq n).1 (seq n).2.1
      rw [hk]
      have hδ_in : f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B) ∈
          mAB ^ (n + 1) := Ideal.mul_mem_right _ _ ih
      have hδ_sq : (f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B)) ^ 2 ∈
          mAB ^ (2 * (n + 1)) := by
        rw [pow_two, two_mul, pow_add]
        exact Ideal.mul_mem_mul hδ_in hδ_in
      have hle : mAB ^ (2 * (n + 1)) ≤ mAB ^ (n + 1 + 1) :=
        Ideal.pow_le_pow_right (by omega)
      exact Ideal.mul_mem_left (mAB ^ (n + 1 + 1)) k (hle hδ_sq)
  refine ⟨a, rfl, hf_strong, ?_⟩
  intro n
  change (stepFn (seq n)).1 - (seq n).1 ∈ mAB ^ (n + 1)
  show ((seq n).1 - f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B)) -
        (seq n).1 ∈ mAB ^ (n + 1)
  have hδ_in : f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B) ∈
      mAB ^ (n + 1) := Ideal.mul_mem_right _ _ (hf_strong n)
  have heq : ((seq n).1 - f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B)) -
              (seq n).1 = -(f.eval (seq n).1 * (((seq n).2.1.unit⁻¹ : Bˣ) : B)) := by
    ring
  rw [heq]
  exact (Ideal.neg_mem_iff _).mpr hδ_in

/-- **Per-element Cayley–Hamilton coordinate annihilator
(iter-066 helper).**

For `δ ∈ mA·B := (maximalIdeal A).map (algebraMap A B)`, the
`A`-linear endomorphism `Algebra.lmul A B δ` (multiplication by `δ`
on the finite `A`-module `B`) sends `B` into `mA·B = mA • (⊤ : Submodule A B)`
by the ideal closure of `mA·B` under multiplication. The Matsumura
form of Cayley–Hamilton
(`LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero`)
then produces a monic polynomial `p ∈ A[X]` with `mA`-power-decaying
coefficients (specifically `p.coeff k ∈ mA ^ (p.natDegree - k)`) such
that `aeval δ p = 0` in `B`. The conversion from
`aeval (Algebra.lmul A B δ) p = 0` (in `End A B`) to `aeval δ p = 0`
(in `B`) uses `aeval_algHom_apply` plus `Algebra.lmul_injective`.

This is the iter-066 documented "Cheapest reverse signal" sub-helper
isolating the Cayley–Hamilton invocation from the substantive
per-coordinate Hensel composition step. Mathlib-PR-shape (~25 LOC,
no Noetherianness on `A`, no `[IsLocalRing B]`). -/
private lemma exists_charpoly_annihilator_of_mem_mAB
    (A B : Type*) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (δ : B) (hδ : δ ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) :
    ∃ p : Polynomial A, p.Monic ∧
      (∀ k, p.coeff k ∈ (IsLocalRing.maximalIdeal A) ^ (p.natDegree - k)) ∧
      Polynomial.aeval δ p = 0 := by
  set mA : Ideal A := IsLocalRing.maximalIdeal A with hmA_def
  -- Range hypothesis: `lmul(δ)` sends `B` into `mA • ⊤ = (mA).map (algebraMap A B)`.
  have hrange : LinearMap.range (Algebra.lmul A B δ : Module.End A B) ≤
      mA • (⊤ : Submodule A B) := by
    rintro y ⟨x, rfl⟩
    show δ * x ∈ mA • (⊤ : Submodule A B)
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_right x _ hδ
  obtain ⟨p, hmonic, _hdeg, hcoeff, haeval⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero
      (R := A) (M := B) (Algebra.lmul A B δ) mA hrange
  refine ⟨p, hmonic, hcoeff, ?_⟩
  -- Transport aeval-zero from `End A B` to `B` via injectivity of `lmul`.
  apply Algebra.lmul_injective (R := A) (A := B)
  rw [map_zero, ← Polynomial.aeval_algHom_apply (Algebra.lmul A B) δ p]
  exact haeval

/-- **Coherent per-coordinate Finsupp witness sequence for a Newton-Cauchy
chain (iter-066 helper).**

Given a fixed finite generating tuple `basis : Fin k → B` of `B` as an
`A`-module and a sequence `s : ℕ → B` starting at `b₀` with the
strengthened Newton-Cauchy invariant `s (n+1) - s n ∈ (mA·B) ^ (n+1)`,
produce a coherent sequence of coordinate witnesses `γ : ℕ → Fin k → A`
satisfying:
1. `γ 0 = 0` (consistent with `s 0 - b₀ = 0`);
2. `γ n i ∈ mA` for every `n, i`;
3. `s n - b₀ = ∑ i, γ n i • basis i` (the basis expansion of `s n - b₀`);
4. `γ (n+1) i - γ n i ∈ mA ^ (n+1)` (per-coordinate Cauchy structure
   inherited from the Newton invariant via `Ideal.map_pow`).

The construction is inductive: at each step, decompose
`s (n+1) - s n ∈ ((mA).map (algebraMap A B)) ^ (n+1) =
((mA^(n+1)).map (algebraMap A B))` via
`Submodule.mem_ideal_smul_span_iff_exists_sum` (after rewriting via
`Ideal.smul_top_eq_map` and `Ideal.map_pow` and using `hspan` to
identify `⊤` with `span A (range basis)`) to obtain a Finsupp witness
`δ : Fin k →₀ A` with each `δ i ∈ mA^(n+1)`, then set
`γ (n+1) i := γ n i + δ i`.

This resolves the documented "non-uniqueness of Finsupp witness" risk
(iter-065 task report L102–L110) via Route (a): fix `γ 0 = 0`
(canonical for `s 0 - b₀ = 0`), construct subsequent witnesses
inductively to make `γ (n+1) i - γ n i ∈ mA^(n+1)` literally hold. -/
private lemma exists_coherent_mAB_finsupp_witness_seq
    (A B : Type*) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B]
    (k : ℕ) (basis : Fin k → B)
    (hspan : Submodule.span A (Set.range basis) = ⊤)
    (s : ℕ → B) (b₀ : B) (hs0 : s 0 = b₀)
    (hsdiff : ∀ n, s (n + 1) - s n ∈
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ (n + 1)) :
    ∃ γ : ℕ → Fin k → A,
      γ 0 = (fun _ => 0) ∧
      (∀ n i, γ n i ∈ IsLocalRing.maximalIdeal A) ∧
      (∀ n, s n - b₀ = ∑ i, γ n i • basis i) ∧
      (∀ n i, γ (n + 1) i - γ n i ∈ (IsLocalRing.maximalIdeal A) ^ (n + 1)) := by
  classical
  set mA : Ideal A := IsLocalRing.maximalIdeal A with hmA_def
  -- Per-step Finsupp witness for `s (n+1) - s n ∈ (mA^(n+1)).map (algebraMap A B)`.
  have hstep : ∀ n, ∃ δ : Fin k → A, (∀ i, δ i ∈ mA ^ (n + 1)) ∧
      s (n + 1) - s n = ∑ i, δ i • basis i := by
    intro n
    have hmem : s (n + 1) - s n ∈ (mA ^ (n + 1)) • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
      exact hsdiff n
    rw [← hspan, Submodule.mem_ideal_smul_span_iff_exists_sum] at hmem
    obtain ⟨a, hamem, hasum⟩ := hmem
    refine ⟨fun i => a i, fun i => hamem i, ?_⟩
    rw [← hasum, Finsupp.sum_fintype]
    intro i; rw [zero_smul]
  choose δ hδmem hδsum using hstep
  -- Inductive construction: γ 0 := 0, γ (n+1) := γ n + δ n.
  let γ : ℕ → Fin k → A := fun n =>
    Nat.rec (motive := fun _ => Fin k → A) (fun _ => 0) (fun n acc => acc + δ n) n
  have hγ_zero : γ 0 = fun _ => 0 := rfl
  have hγ_succ : ∀ n i, γ (n + 1) i = γ n i + δ n i := fun n i => rfl
  -- Property 2: γ n i ∈ mA.
  have hγ_mem : ∀ n i, γ n i ∈ mA := by
    intro n
    induction n with
    | zero => intro i; exact mA.zero_mem
    | succ n ih =>
      intro i
      rw [hγ_succ]
      refine Ideal.add_mem _ (ih i) ?_
      have hle : mA ^ (n + 1) ≤ mA := by
        conv_rhs => rw [← pow_one mA]
        exact Ideal.pow_le_pow_right (by omega)
      exact hle (hδmem n i)
  -- Property 3: s n - b₀ = ∑ i, γ n i • basis i.
  have hγ_decomp : ∀ n, s n - b₀ = ∑ i, γ n i • basis i := by
    intro n
    induction n with
    | zero =>
      rw [hs0, sub_self, hγ_zero]
      simp [zero_smul]
    | succ n ih =>
      have heq : s (n + 1) - b₀ = (s (n + 1) - s n) + (s n - b₀) := by ring
      rw [heq, hδsum n, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hγ_succ, add_smul, add_comm]
  -- Property 4: γ (n+1) i - γ n i ∈ mA^(n+1).
  have hγ_diff : ∀ n i, γ (n + 1) i - γ n i ∈ mA ^ (n + 1) := by
    intro n i
    rw [hγ_succ]
    show γ n i + δ n i - γ n i ∈ mA ^ (n + 1)
    have : γ n i + δ n i - γ n i = δ n i := by ring
    rw [this]
    exact hδmem n i
  exact ⟨γ, hγ_zero, hγ_mem, hγ_decomp, hγ_diff⟩

/-- **Basis decomposition of elements of `mA·B`.** Mathlib-PR-shape
helper (iter-068). Given a finite `A`-spanning tuple `basis : Fin k → B`
of `B` (so `B = span_A (range basis)`), every element of `mA·B` admits a
decomposition `x = ∑ algebraMap A B (α i) * basis i` with each
coefficient `α i ∈ mA`.

Proof: directly via Mathlib's
`Submodule.mem_ideal_smul_span_iff_exists_sum` after bridging
`(mA).map (algebraMap A B) = mA • Submodule.span A (range basis)` via
`hspan` + `Ideal.smul_top_eq_map`. The Finsupp witness produced by the
ambient lemma is converted to a plain `Fin k → A` via
`Finsupp.sum_fintype` + `Algebra.smul_def`.

Used inside `exists_hensel_root_from_coherent_witness` to convert
`mA·B`-valued targets back into `A`-coefficient form against the
fixed spanning tuple. Also a clean carve-out as a Mathlib-PR
candidate: works for any `A`-algebra `B` with an `A`-spanning tuple
and any ideal `I ≤ mA`. -/
private lemma exists_mAB_decomposition_in_basis
    (A B : Type*) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B]
    (k : ℕ) (basis : Fin k → B)
    (hspan : Submodule.span A (Set.range basis) = ⊤)
    (x : B)
    (hx : x ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) :
    ∃ α : Fin k → A, (∀ i, α i ∈ IsLocalRing.maximalIdeal A) ∧
      x = ∑ i, algebraMap A B (α i) * basis i := by
  have hx_in : x ∈ (IsLocalRing.maximalIdeal A) •
      Submodule.span A (Set.range basis) := by
    rw [hspan, Ideal.smul_top_eq_map]; exact hx
  obtain ⟨a, ha_mem, ha_sum⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum
      (IsLocalRing.maximalIdeal A) basis x).mp hx_in
  refine ⟨a, ha_mem, ?_⟩
  have heq : (a.sum fun i c => c • basis i) = ∑ i, a i • basis i := by
    apply Finsupp.sum_fintype
    intro i
    exact zero_smul A _
  rw [← ha_sum, heq]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Algebra.smul_def]

/-- **Linear part of the multivariate basis expansion of `g.eval`.**
Mathlib-PR-shape helper (iter-068). Given a finite tuple
`basis : Fin k → B` and coefficients `α : Fin k → A` with each
`α i ∈ mA`, the difference between `g.eval (b₀ + ∑ algebraMap A B (α i)
* basis i)` and its linear approximation
`g.eval b₀ + ∑ algebraMap A B (α i) * (g.derivative.eval b₀ * basis i)`
lies in `(mA·B)^2`.

This isolates the linear Taylor expansion of `g` at `b₀` in the
direction `r := ∑ algebraMap A B (α i) * basis i`. The proof uses the
single-variable `Polynomial.binomExpansion`:
`g.eval (b₀ + r) = g.eval b₀ + g.derivative.eval b₀ * r + c * r^2`
for some `c : B`, distributes `g.derivative.eval b₀ * r` summand-wise
to match the linear term, then `r ∈ mA·B` gives `r^2 ∈ (mA·B)^2` via
`Ideal.pow_mem_pow`.

The hypothesis `hα_mem : ∀ i, α i ∈ mA` is only used to derive `r ∈
mA·B` so the tail `c * r^2` lies in `(mA·B)^2`. The identity itself is
purely algebraic. -/
private lemma basis_expansion_polynomial_eval
    (A B : Type*) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B]
    (g : Polynomial B) (b₀ : B)
    (k : ℕ) (basis : Fin k → B)
    (α : Fin k → A) (hα_mem : ∀ i, α i ∈ IsLocalRing.maximalIdeal A) :
    g.eval (b₀ + ∑ i, algebraMap A B (α i) * basis i) -
      (g.eval b₀ + ∑ i, algebraMap A B (α i) *
        (g.derivative.eval b₀ * basis i)) ∈
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ 2 := by
  set r : B := ∑ i, algebraMap A B (α i) * basis i with hr
  have hr_mem : r ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Ideal.mul_mem_right (basis i) _
      (Ideal.mem_map_of_mem _ (hα_mem i))
  obtain ⟨c, hc⟩ := g.binomExpansion b₀ r
  have hlin : g.derivative.eval b₀ * r =
      ∑ i, algebraMap A B (α i) * (g.derivative.eval b₀ * basis i) := by
    rw [hr, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have heq : g.eval (b₀ + r) -
      (g.eval b₀ + ∑ i, algebraMap A B (α i) *
        (g.derivative.eval b₀ * basis i)) = c * r ^ 2 := by
    rw [hc, ← hlin]; ring
  rw [heq]
  exact Ideal.mul_mem_left _ c (Ideal.pow_mem_pow hr_mem 2)

/-- **L3c-charpoly per-coordinate Hensel-manufacture + reassembly
sub-sub-sub-sub-sub-sub-sub-helper (iter-067 extraction).**

Given a coherent per-coordinate witness sequence `γ : ℕ → Fin k → A`
with `γ 0 = 0`, `γ n i ∈ mA`, `γ (n+1) i - γ n i ∈ mA^(n+1)` (strong
Cauchy), and the *transported* Newton-evaluation hypothesis
`g.eval (b₀ + ∑ algebraMap A B (γ n i) · basis i) ∈ (mA·B)^(n+1)`,
produce coefficients `α : Fin k → A` with each `α i ∈ mA` such that
`g.IsRoot (b₀ + ∑ algebraMap A B (α i) · basis i)`.

This sub-helper isolates the genuine substantive content of Steps
(d)–(e) of Route R1 (per-coordinate Hensel manufacture from `g`'s
basis expansion + Cayley–Hamilton annihilator + reassembly) from the
wrapper `descend_root_from_mAB_newton_charpoly_descent`. The wrapper
extracts `γ` (via `exists_coherent_mAB_finsupp_witness_seq`) and
verifies the transported `hg_eval` hypothesis mechanically from the
Newton sequence's `hsroot` and `hγ_decomp` via the `Algebra.smul_def`
conversion `r • b = algebraMap A B r * b`.

iter-068 progress: two PR-shape sorry-free helpers have landed
(`exists_mAB_decomposition_in_basis` and
`basis_expansion_polynomial_eval`) that package, respectively, the
basis-decomposition for `mA·B`-elements and the linear-Taylor identity
`g.eval (b₀ + r) - (g.eval b₀ + g'(b₀)·r) ∈ (mA·B)^2`. These
infrastructural pieces will be consumed by the iter-069+ closure to
build the per-coordinate Hensel polynomials.

The substantive residual (typed sorry; iter-069+) manufactures
per-coordinate single-variable polynomials `h_i ∈ A[X]` from the
basis expansion of `g ∈ B[X]` together with the Cayley–Hamilton
annihilators provided by `exists_charpoly_annihilator_of_mem_mAB`,
verifies the Hensel hypotheses (`h_i.eval 0 ∈ mA` and `h_i.derivative.eval 0`
a unit in `A ⧸ mA`, traceable to `h_unit` via the basis expansion of
`g.derivative`), and invokes `HenselianLocalRing.is_henselian` per
coordinate at starting point `0` to obtain each `α i ∈ A`. Reassembly
then verifies `g.IsRoot (b₀ + ∑ algebraMap A B (α i) * basis i)` via
the per-coordinate root conditions combined with `g`'s basis
expansion. -/
private lemma exists_hensel_root_from_coherent_witness
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    (g : Polynomial B) (hg : g.Monic) (b₀ : B)
    (h_unit : IsUnit (g.derivative.eval b₀))
    (k : ℕ) (basis : Fin k → B)
    (hspan : Submodule.span A (Set.range basis) = ⊤)
    (γ : ℕ → Fin k → A)
    (hγ_zero : γ 0 = fun _ => 0)
    (hγ_mem : ∀ n i, γ n i ∈ IsLocalRing.maximalIdeal A)
    (hγ_diff : ∀ n i, γ (n + 1) i - γ n i ∈
      (IsLocalRing.maximalIdeal A) ^ (n + 1))
    (hg_eval : ∀ n, g.eval (b₀ + ∑ i, algebraMap A B (γ n i) * basis i) ∈
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ (n + 1)) :
    ∃ α : Fin k → A, (∀ i, α i ∈ IsLocalRing.maximalIdeal A) ∧
      g.IsRoot (b₀ + ∑ i, algebraMap A B (α i) * basis i) := by
  -- Substantive per-coordinate Hensel manufacture + reassembly.
  -- iter-067 isolated this as a typed sub-helper carrying the Route R1
  -- Steps (d)–(e) substantive content.
  --
  -- iter-068 progress: two PR-shape sorry-free helpers landed above
  -- providing the foundational infrastructure for the closure:
  --
  --   * `basis_expansion_polynomial_eval`: for any `α : Fin k → A` with
  --     `α i ∈ mA`,
  --        g.eval (b₀ + ∑ algebraMap A B (α i) * basis i) =
  --          g.eval b₀ + ∑ algebraMap A B (α i) * (g'(b₀) * basis i) + T
  --     with `T ∈ (mA·B)^2`. Applied at `α := γ n` gives a linearised
  --     reduction of `g.eval (b₀ + ∑ γ n · basis)` mod `(mA·B)^2`.
  --
  --   * `exists_mAB_decomposition_in_basis`: any element of `mA·B`
  --     decomposes as `∑ algebraMap A B (β i) * basis i` with `β i ∈ mA`.
  --     Applied to `g.eval b₀` (which lies in `mA·B = (mA·B)^1` via
  --     `hg_eval 0` at the `γ 0 = 0` instance) gives concrete
  --     `A`-coefficients `β` such that `g.eval b₀ = ∑ alg(β i) * basis i`.
  --
  -- These together convert the residue `g.eval b₀` into `A`-coordinate
  -- form and isolate the linear-vs-quadratic structure of the
  -- multivariate Taylor expansion. The remaining residual is the genuine
  -- substantive content: combining these with `HenselianLocalRing.is_henselian`
  -- on `A` plus the Cayley–Hamilton annihilators
  -- `exists_charpoly_annihilator_of_mem_mAB` to manufacture per-coordinate
  -- `h_i ∈ A[X]` for which Hensel-on-A produces `α : Fin k → A`. Reassembly
  -- then uses `basis_expansion_polynomial_eval` iteratively (one level per
  -- power of `mA·B`) to confirm `g.IsRoot (b₀ + ∑ alg(α i) * basis i)`.
  --
  -- iter-069+ structural plan (proposed iter-069 sub-helper signature):
  --   `exists_per_coord_hensel_polynomial (A B) [...] (basis γ hg_eval) (i : Fin k)
  --      : ∃ h : Polynomial A, h.eval 0 ∈ mA ∧
  --          IsUnit (Ideal.Quotient.mk mA (h.derivative.eval 0)) ∧
  --          (∀ a : A, a ∈ mA → h.eval a = 0 → ∃ extension to (α : Fin k → A) closing g)`.
  -- The final third clause is the genuine substantive content.
  --
  -- Concrete structural step taken this iter: apply
  -- `exists_mAB_decomposition_in_basis` to `g.eval b₀ ∈ mA·B` (from
  -- `hg_eval 0` after `hγ_zero` simplification) to obtain `β : Fin k → A`
  -- such that `g.eval b₀ = ∑ algebraMap A B (β i) * basis i`. This is the
  -- starting Newton residue in `A`-coordinates that the iter-069+
  -- per-coordinate manufacture will consume.
  classical
  have hg₀_mem : g.eval b₀ ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
    have h0 := hg_eval 0
    simp only [hγ_zero, map_zero, zero_mul, Finset.sum_const_zero,
      add_zero, zero_add, pow_one] at h0
    exact h0
  obtain ⟨β, hβ_mem, hβ_eq⟩ :=
    exists_mAB_decomposition_in_basis A B k basis hspan (g.eval b₀) hg₀_mem
  -- The witness `β` encodes the initial Newton residue in `A`-coordinates.
  -- Track-and-consume in iter-069+ closure.
  let _ := hg; let _ := h_unit; let _ := hβ_mem; let _ := hβ_eq
  let _ := hγ_mem; let _ := hγ_diff; let _ := hg_eval
  sorry

/-- **L3c-charpoly per-coordinate root-coefficient sub-sub-sub-sub-sub-sub-helper.**

iter-065 extraction (typed sorry). Given a fixed finite generating
tuple `(b_i : Fin k → B)` of `B` as an `A`-module and a Newton-Cauchy
sequence `(s_n)` in `B` with the strengthened `mA·B`-power invariants,
produce coefficients `α : Fin k → A` with each `α i ∈ mA` such that
the reassembled element `b₀ + ∑ algebraMap A B (α i) · b i` is an
honest root of `g` in `B`.

This isolates the substantive per-coordinate Hensel descent +
reassembly step (Steps 4–6 of the Route R1 blueprint recipe) from
the structural wrapper: the wrapper handles the finite-generating-
tuple extraction (Step 1) and the closeness verification (Step 6b)
mechanically; this sub-helper carries the genuine Cayley–Hamilton
+ per-coordinate `HenselianLocalRing.is_henselian` machinery
(Steps 2–6a) entirely in `A`-coordinates. -/
private lemma descend_root_from_mAB_newton_charpoly_descent
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    (g : Polynomial B) (hg : g.Monic) (b₀ : B)
    (h_unit : IsUnit (g.derivative.eval b₀))
    (k : ℕ) (basis : Fin k → B)
    (hspan : Submodule.span A (Set.range basis) = ⊤)
    (s : ℕ → B) (hs0 : s 0 = b₀)
    (hsroot : ∀ n, g.eval (s n) ∈
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ (n + 1))
    (hsdiff : ∀ n, s (n + 1) - s n ∈
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ (n + 1)) :
    ∃ α : Fin k → A,
      (∀ i, α i ∈ IsLocalRing.maximalIdeal A) ∧
      g.IsRoot (b₀ + ∑ i, algebraMap A B (α i) * basis i) := by
  -- Substantive per-coordinate Cayley–Hamilton + henselian-A descent
  -- + reassembly (iter-065 extraction; iter-066 partial wiring). The
  -- Newton sequence `s` plus the strengthened `mA·B`-filtration and
  -- the fixed generating tuple `basis` provide exactly the input
  -- consumed by Steps 2–6a of Route R1 in the blueprint
  -- (`lem:henselianPair-l3c-charpoly-substantive-descent`).
  --
  -- iter-066 progress: Steps (a)–(c) data now built sorry-free via
  -- two new in-file helpers:
  --
  --   * `exists_coherent_mAB_finsupp_witness_seq` (iter-066) — provides
  --     the coherent per-coordinate Finsupp witness sequence
  --     `γ : ℕ → Fin k → A` with `γ 0 = 0`, `γ n i ∈ mA`,
  --     `s n - b₀ = ∑ γ n i • basis i`, and the per-coordinate Cauchy
  --     invariant `γ (n+1) i - γ n i ∈ mA^(n+1)`. Resolves the
  --     iter-065 "non-uniqueness of Finsupp witness" risk via
  --     inductive construction (Route (a)).
  --   * `exists_charpoly_annihilator_of_mem_mAB` (iter-066) — provides
  --     the per-element Cayley–Hamilton annihilator: for any
  --     `δ ∈ mA·B`, a monic `p ∈ A[X]` with `mA`-power-decaying
  --     coefficients and `aeval δ p = 0`. Direct Matsumura
  --     Cayley–Hamilton (`LinearMap.exists_monic_and_…_aeval_eq_zero`).
  --
  -- Residual (iter-067+): Steps (d)–(e) — the genuine substantive
  -- non-mechanical content. Use the basis expansion of `g ∈ B[X]`
  -- together with the Cayley–Hamilton annihilators of each `(s n - b₀)`
  -- to manufacture per-coordinate single-variable polynomials
  -- `h_i ∈ A[X]` whose mod-`mA` reductions admit `γ_{0,i} = 0` as a
  -- simple root (with derivative residue a unit, traceable to
  -- `h_unit : IsUnit (g.derivative.eval b₀)` via the basis expansion
  -- of `g.derivative`). Apply `HenselianLocalRing.is_henselian` on
  -- `A` per coordinate to obtain `α_i ∈ A` with `α_i - 0 ∈ mA` and
  -- `h_i.eval α_i = 0`. Reassemble
  -- `b := b₀ + ∑ algebraMap A B (α_i) • basis i`; verify
  -- `g.IsRoot b` via the per-coordinate root conditions combined
  -- with the basis expansion of `g.eval (b - b₀)` and the
  -- Cayley–Hamilton annihilator identity. Once this composition
  -- step is closed (iter-067 target), the present sorry vanishes.
  classical
  -- Step (a)+(b): coherent per-coordinate Finsupp witness sequence
  -- (sorry-free, iter-066 helper).
  obtain ⟨γ, hγ_zero, hγ_mem, hγ_decomp, hγ_diff⟩ :=
    exists_coherent_mAB_finsupp_witness_seq A B k basis hspan s b₀ hs0 hsdiff
  -- Step (c): per-element Cayley–Hamilton annihilator
  -- (sorry-free, iter-066 helper). For each `n`, `s n - b₀ ∈ mA·B`
  -- (via the basis expansion `hγ_decomp n` and `hγ_mem n`); apply
  -- `exists_charpoly_annihilator_of_mem_mAB` to obtain the
  -- annihilating polynomial `p_n ∈ A[X]`. This data is consumed
  -- inside Step (d)'s per-coordinate Hensel manufacture (iter-067+).
  have hsn_b₀_mem : ∀ n, s n - b₀ ∈
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
    intro n
    rw [hγ_decomp n]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right (basis i) _ (Ideal.mem_map_of_mem _ (hγ_mem n i))
  have _hcharpoly : ∀ n, ∃ p : Polynomial A, p.Monic ∧
      (∀ j, p.coeff j ∈ (IsLocalRing.maximalIdeal A) ^ (p.natDegree - j)) ∧
      Polynomial.aeval (s n - b₀) p = 0 := fun n =>
    exists_charpoly_annihilator_of_mem_mAB A B (s n - b₀) (hsn_b₀_mem n)
  -- Steps (d)–(e) — substantive Hensel composition + reassembly
  -- routed through the iter-067 sub-sub-sub-sub-sub-sub-sub-helper
  -- `exists_hensel_root_from_coherent_witness` (typed sorry). The
  -- wrapper verifies the transported `hg_eval` hypothesis from
  -- `hsroot` and `hγ_decomp` via the `Algebra.smul_def` conversion
  -- `r • b = algebraMap A B r * b`; the substantive Hensel-on-`A`
  -- manufacture + reassembly content is fully isolated in the
  -- sub-helper.
  refine exists_hensel_root_from_coherent_witness A B g hg b₀ h_unit k basis
    hspan γ hγ_zero hγ_mem hγ_diff ?_
  intro n
  have hsum : (∑ i, γ n i • basis i : B) =
      ∑ i, algebraMap A B (γ n i) * basis i :=
    Finset.sum_congr rfl (fun i _ => by rw [Algebra.smul_def])
  have heq : (b₀ + ∑ i, algebraMap A B (γ n i) * basis i : B) = s n := by
    rw [← hsum, ← hγ_decomp n]; ring
  rw [heq]
  exact hsroot n

/-- **L3c-charpoly per-coordinate convergence sub-helper.** The substantive
per-coordinate descent step (iter-064 extraction; iter-065
Acceptable-full close as a thin wrapper around
`descend_root_from_mAB_newton_charpoly_descent`).

Given a Newton-Cauchy sequence `s : ℕ → B` (with `s 0 = b₀`,
`g(s n) ∈ (mA·B)^{n+1}`, `s(n+1) - s n ∈ (mA·B)^{n+1}`), produce a
root `b ∈ B` of `g` with `b - b₀ ∈ mA·B`.

iter-065 closure: the wrapper extracts a finite generating tuple
`(b_i : Fin k → B)` of `B` as an `A`-module (via
`Module.Finite.fg_top` + `Submodule.fg_iff_exists_fin_generating_family`),
applies the sub-sub-sub-sub-sub-sub-helper
`descend_root_from_mAB_newton_charpoly_descent` to obtain explicit
`A`-coefficients `α_i ∈ mA`, reassembles
`b := b₀ + ∑ algebraMap A B α_i · b_i`, and verifies the closeness
`b - b₀ ∈ mA·B` summand-by-summand using
`Ideal.mem_map_of_mem` and `Ideal.mul_mem_right`. The substantive
Cayley–Hamilton + per-coordinate Hensel-on-`A` content is fully
isolated in the sub-helper. -/
private lemma descend_root_from_mAB_newton
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    (g : Polynomial B) (hg : g.Monic) (b₀ : B)
    (h_unit : IsUnit (g.derivative.eval b₀))
    (s : ℕ → B) (hs0 : s 0 = b₀)
    (hsroot : ∀ n, g.eval (s n) ∈
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ (n + 1))
    (hsdiff : ∀ n, s (n + 1) - s n ∈
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ (n + 1)) :
    ∃ b : B, g.IsRoot b ∧
      b - b₀ ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
  -- Step 1: extract a finite generating tuple of `B` as an `A`-module.
  obtain ⟨k, basis, hspan⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (Module.Finite.fg_top (R := A) (M := B))
  -- Step 2: apply the substantive sub-helper carrying the
  -- Cayley–Hamilton + per-coordinate Hensel-on-`A` descent.
  obtain ⟨α, hα_mem, hroot⟩ :=
    descend_root_from_mAB_newton_charpoly_descent
      A B g hg b₀ h_unit k basis hspan s hs0 hsroot hsdiff
  -- Step 3: reassemble and verify closeness summand-by-summand.
  refine ⟨b₀ + ∑ i, algebraMap A B (α i) * basis i, hroot, ?_⟩
  have heq : (b₀ + ∑ i, algebraMap A B (α i) * basis i) - b₀ =
      ∑ i, algebraMap A B (α i) * basis i := by ring
  rw [heq]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Ideal.mul_mem_right (basis i) _ (Ideal.mem_map_of_mem _ (hα_mem i))

/-- **L3c-charpoly sub-sub-sub-sub-helper.** The multivariate Hensel
descent step for the henselian-pair construction in the local-finite
case (iter-063 extraction; iter-064 Acceptable-full close as a thin
wrapper around `exists_seq_lift_of_finite_henselian_mAB` +
`descend_root_from_mAB_newton`).

Given a monic polynomial `g ∈ B[X]` and a point `b₀ ∈ B` satisfying
the *strengthened* hypothesis `g(b₀) ∈ mA·B` (not merely `mB`) plus
`g'(b₀)` a unit in `B`, produce a root `b ∈ B` of `g` with the
strengthened closeness `b - b₀ ∈ mA·B`.

iter-064 closure: the body constructs the Newton sequence in `B` with
`mA·B`-power invariants via `exists_seq_lift_of_finite_henselian_mAB`,
then delegates the substantive per-coordinate convergence step
(Cayley–Hamilton + henselian-A) to the typed sub-helper
`descend_root_from_mAB_newton`. -/
private lemma descend_root_of_eval_mem_mAB
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    (g : Polynomial B) (hg : g.Monic) (b₀ : B)
    (h_eval : g.eval b₀ ∈
      (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (h_unit : IsUnit (g.derivative.eval b₀)) :
    ∃ b : B, g.IsRoot b ∧
      b - b₀ ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
  obtain ⟨s, hs0, hsroot, hsdiff⟩ :=
    exists_seq_lift_of_finite_henselian_mAB A B g b₀ h_eval h_unit
  exact descend_root_from_mAB_newton A B g hg b₀ h_unit s hs0 hsroot hsdiff

/-- **L3c-newton sub-sub-helper — Descent of a Cauchy sequence to a
root via Cayley–Hamilton.**

iter-063 closure (Acceptable-full): the body reduces to the
sub-sub-sub-sub-helper `descend_root_of_eval_mem_mAB` (typed sorry)
by passing to a tail index of the given Newton-Cauchy sequence where
the `g`-evaluation lies in `mA·B` (via
`exists_maximalIdeal_pow_le_map_maximalIdeal`). The substantive
multivariate Hensel descent is fully isolated in
`descend_root_of_eval_mem_mAB`.

The wrapper performs four mechanical steps:
1. Telescope `_hsdiff` to obtain `s n - b₀ ∈ mB` for every `n`.
2. Choose `n = N` (with `mB^N ⊆ mA·B` from
   `exists_maximalIdeal_pow_le_map_maximalIdeal`); then
   `g(s N) ∈ mB^{N+1} ⊆ mB^N ⊆ mA·B`.
3. Verify `g'(s N)` is a unit by `mB`-residue equality with `g'(b₀)`
   plus locality of `B` (via `isLocalHom_of_le_jacobson_bot` applied
   to the residue map `B → B/mB`).
4. Apply `descend_root_of_eval_mem_mAB` at `(g, s N)` to obtain a
   root `b ∈ B` with `b - s N ∈ mA·B`; combine with `s N - b₀ ∈ mB`
   and `mA·B ⊆ mB` (via `maximalIdeal_map_le_maximalIdeal`) to give
   `b - b₀ ∈ mB`. -/
private lemma descend_root_via_charpoly
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    (g : Polynomial B) (hg : g.Monic) (b₀ : B)
    (h_eval : g.eval b₀ ∈ IsLocalRing.maximalIdeal B)
    (h_unit : IsUnit (g.derivative.eval b₀))
    (s : ℕ → B) (hs0 : s 0 = b₀)
    (_hsf : ∀ n, g.eval (s n) ∈ (IsLocalRing.maximalIdeal B) ^ (n + 1))
    (_hsdiff : ∀ n, s (n + 1) - s n ∈ (IsLocalRing.maximalIdeal B) ^ (n + 1)) :
    ∃ b : B, g.IsRoot b ∧ b - b₀ ∈ IsLocalRing.maximalIdeal B := by
  set mB : Ideal B := IsLocalRing.maximalIdeal B with hmB_def
  set mAB : Ideal B := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
    with hmAB_def
  -- `h_eval` is implied by `_hsf 0` together with `hs0`; included in the
  -- frozen signature for symmetry with the consumer wrapper.
  let _ := h_eval
  -- Step 1: telescope the Newton-Cauchy differences to obtain
  -- `s n - b₀ ∈ mB` for every `n`.
  have hdiff_b₀ : ∀ n, s n - b₀ ∈ mB := by
    intro n
    induction n with
    | zero => rw [hs0, sub_self]; exact Ideal.zero_mem mB
    | succ n ih =>
      have hstep : s (n + 1) - s n ∈ mB := by
        have hpow : mB ^ (n + 1) ≤ mB ^ 1 :=
          Ideal.pow_le_pow_right (by omega)
        rw [pow_one] at hpow
        exact hpow (_hsdiff n)
      have heq : s (n + 1) - b₀ = (s (n + 1) - s n) + (s n - b₀) := by ring
      rw [heq]; exact Ideal.add_mem mB hstep ih
  -- Step 2: choose `n = N` with `mB^N ⊆ mA·B`; then `g(s N) ∈ mA·B`.
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map_maximalIdeal A B
  have h_eval_N : g.eval (s N) ∈ mAB := by
    have hpow_le : mB ^ (N + 1) ≤ mB ^ N := Ideal.pow_le_pow_right (by omega)
    exact hN (hpow_le (_hsf N))
  -- Step 3: `g'(s N)` is a unit by residue equality with `g'(b₀)` and
  -- locality of `B`.
  have h_unit_N : IsUnit (g.derivative.eval (s N)) := by
    have hcong :
        g.derivative.eval (s N) - g.derivative.eval b₀ ∈ mB := by
      obtain ⟨z, hz⟩ := g.derivative.evalSubFactor (s N) b₀
      exact hz ▸ Ideal.mul_mem_left mB z (hdiff_b₀ N)
    have hres :
        Ideal.Quotient.mk mB (g.derivative.eval (s N)) =
          Ideal.Quotient.mk mB (g.derivative.eval b₀) := by
      rw [Ideal.Quotient.eq]; exact hcong
    have hunit_res :
        IsUnit (Ideal.Quotient.mk mB (g.derivative.eval (s N))) := by
      rw [hres]; exact h_unit.map _
    haveI : IsLocalHom (Ideal.Quotient.mk mB) := by
      refine isLocalHom_of_le_jacobson_bot _ ?_
      intro x hx
      rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
      refine Submodule.mem_sInf.mpr fun J hJ => ?_
      have hJeq : J = IsLocalRing.maximalIdeal B :=
        IsLocalRing.eq_maximalIdeal hJ
      exact hJeq ▸ hx
    exact IsUnit.of_map (Ideal.Quotient.mk mB) _ hunit_res
  -- Step 4: apply the substantive sub-sub-sub-sub-helper at `(g, s N)`.
  obtain ⟨b, hb_root, hb_diff⟩ :=
    descend_root_of_eval_mem_mAB A B g hg (s N) h_eval_N h_unit_N
  refine ⟨b, hb_root, ?_⟩
  have heq : b - b₀ = (b - s N) + (s N - b₀) := by ring
  rw [heq]
  refine Ideal.add_mem mB ?_ (hdiff_b₀ N)
  exact maximalIdeal_map_le_maximalIdeal A B hb_diff

/-- **L3c sub-sub-helper — Newton-iteration root in a finite local
algebra over a henselian local ring.**

iter-062 closure (Acceptable-full): wires the local Newton sequence
helper `exists_seq_lift_of_finite_henselian_local` (sorry-free) plus
the nilpotency helper `exists_maximalIdeal_pow_le_map_maximalIdeal`
(sorry-free) into the substantive descent step
`descend_root_via_charpoly` (typed sorry). Once the descent helper
lands the present lemma becomes sorry-free.

Closure routes through:
- `mA·B ⊆ mB` (the helper `maximalIdeal_map_le_maximalIdeal` above);
- `B/(mA·B)` is a finite-dimensional `A/mA`-vector space, hence
  Artinian as a ring, so `mB/(mA·B)` is nilpotent: `∃ N`,
  `mB^N ⊆ mA·B` (sorry-free via
  `exists_maximalIdeal_pow_le_map_maximalIdeal`);
- the Newton recursion in `B` (sorry-free via
  `exists_seq_lift_of_finite_henselian_local`) produces
  `b_n` with `g(b_n) ∈ mB^{n+1}` and `b_{n+1} - b_n ∈ mB^{n+1}`;
- the `mB`-power filtration is converted to a `mA·B`-power filtration
  via the nilpotency, providing the Cauchy sequence consumed by
  `descend_root_via_charpoly`;
- limit identification by descent to `A` via the characteristic
  polynomial of multiplication-by-`b_0` (substantive sorry isolated
  in `descend_root_via_charpoly`). -/
private lemma exists_root_in_finite_henselian_module
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B]
    (g : Polynomial B) (hg : g.Monic) (b₀ : B)
    (h_eval : g.eval b₀ ∈ IsLocalRing.maximalIdeal B)
    (h_unit : IsUnit (g.derivative.eval b₀)) :
    ∃ b : B, g.IsRoot b ∧ b - b₀ ∈ IsLocalRing.maximalIdeal B := by
  -- Newton sequence in `B`: `g.eval (a n) ∈ mB^{n+1}`, `a(n+1) - a n ∈ mB^{n+1}`.
  obtain ⟨a, ha0, hf_strong, hdiff_strong⟩ :=
    exists_seq_lift_of_finite_henselian_local A B g b₀ h_eval h_unit
  -- Descent via Cayley–Hamilton + henselianness of `A` (substantive sorry,
  -- isolated in `descend_root_via_charpoly`). The Newton sequence carries
  -- both the `mB`-power decay of `g.eval (a n)` and the `mB`-power Cauchy
  -- property of `(a n)`; the nilpotency `∃ N, mB^N ≤ mA·B` (available via
  -- `exists_maximalIdeal_pow_le_map_maximalIdeal`) is consumed inside the
  -- descent helper to convert the `mB`-adic Cauchy structure to a
  -- `mA`-adic Cauchy structure when needed.
  exact descend_root_via_charpoly A B g hg b₀ h_eval h_unit a ha0
    hf_strong hdiff_strong

/-- **L3c — Finite extension of a henselian local ring is henselian local.**

Stacks Tag 04GH specialised to the local case (`[IsLocalRing B]`).
The L3b product decomposition is bypassed by the `[IsLocalRing B]`
hypothesis. iter-060 closure routes the substantive Newton-
convergence step through the named typed sub-sub-helper
`exists_root_in_finite_henselian_module`. -/
private lemma henselianLocalRing_of_finite_over_henselianLocal
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [IsLocalRing B] :
    HenselianLocalRing B where
  is_henselian f hf b₀ h_eval h_unit :=
    exists_root_in_finite_henselian_module A B f hf b₀ h_eval h_unit

/-- **L2/L3 (combined) — Stacks 0DXB Hensel lift in the
henselian-pair setting.**

The substantive Newton-iteration / residue-product step. Stated
in the exact shape consumed by the `is_henselian` field of
`HenselianRing B mB`, this isolates the actual `sorry` to a
single named lemma whose signature matches the structural field
verbatim.

iter-059 structural decomposition (Acceptable-partial): Stage 3
convergence is now decomposed into the two named typed sub-helpers
`lift_idempotent_henselianPair` (L3a) and
`henselianLocalRing_of_finite_over_henselianLocal` (L3c) above.
The main body wires both via `have`-introduction so that closing
either sub-helper directly tightens the main body's residual
obligation. The remaining sorry encodes the *assembly* of the
Stacks 04GE residue-product decomposition — building the residue
product structure on `B ⧸ mB` (via the identification
`k ⊗_A B ≃ₐ[k] B ⧸ mB` plus `Algebra.Etale.baseChange` and
`Algebra.Etale.iff_exists_algEquiv_prod`) and gluing the per-factor
Hensel roots via `CompleteOrthogonalIdempotents.bijective_pi`. The
two sub-helpers above isolate the *substantive* Mathlib gaps
identified by the iter-058 plan pre-flight; iter-060+ closes them
plus the assembly.

Recommended routes (see blueprint):
- **Route 1 (direct Newton).** Define `a_{n+1} := a_n - f(a_n) · f'(a_n)⁻¹`
  inside `B` using the Nakayama-upgraded unit
  `isUnit_of_isUnit_quotient_mk_maximalIdeal_map` for `f'(a_0)`.
  The Cauchy property gives `a_n - a_m ∈ (mB)^{min(n,m)}`. The
  convergence step requires `IsPrecomplete (mB) B`, which is the
  gap (henselian local rings need not be adic-complete).
- **Route 3 (Stacks 04GE) — recommended.** Decompose `B ≃ ∏ B_i`
  into a finite product of henselian local rings (Stacks 04GE,
  itself substantive), Hensel-lift in each factor via
  `HenselianLocalRing.is_henselian`, glue. -/
private lemma exists_root_of_eval_mem_of_isUnit_derivative_quotient
    (A B : Type*) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B]
    (f : Polynomial B) (hf : f.Monic) (a₀ : B)
    (h_eval : f.eval a₀ ∈
      (IsLocalRing.maximalIdeal A).map (algebraMap A B))
    (h_unit : IsUnit (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B))
      (f.derivative.eval a₀))) :
    ∃ a : B, f.IsRoot a ∧
      a - a₀ ∈ (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
  -- Nakayama-upgraded unit: iter-054 helper
  -- `isUnit_of_isUnit_quotient_mk_maximalIdeal_map` lifts the
  -- unit-mod-mB hypothesis to a genuine unit in `B`.
  have h_unit_B : IsUnit (f.derivative.eval a₀) :=
    isUnit_of_isUnit_quotient_mk_maximalIdeal_map A B h_unit
  -- L1 (iter-056): `mB`-adic separation of `B` via Krull intersection
  -- (`IsNoetherianRing A + Module.Finite A B ⇒ IsNoetherianRing B`,
  -- plus `maximalIdeal_map_le_jacobson_bot`).
  have h_sep : ⨅ n : ℕ,
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) ^ n = ⊥ :=
    maximalIdeal_map_iInf_pow_eq_bot A B
  -- L2 (iter-056 typed-sorry handoff): the Newton-step Cauchy sequence.
  obtain ⟨a, ha0, hfn, hdiff⟩ :=
    exists_seq_lift_of_henselianPair A B f a₀ h_eval h_unit_B
  -- Stage 3 (iter-059 target via Route (ii) Stacks 04GE): convergence
  -- of the L2 Cauchy sequence `a` to a root of `f` in `B`.
  -- iter-059 structural decomposition: wire the two named typed
  -- sub-helpers `lift_idempotent_henselianPair` (L3a) and
  -- `henselianLocalRing_of_finite_over_henselianLocal` (L3c) via
  -- `have` so that closing either sub-helper directly advances the
  -- assembly below. The `_h_lift_idem` witness lifts orthogonal
  -- idempotents in `B ⧸ mB` to a complete orthogonal family in `B`
  -- (applied per `e_i ∈ ∏ k_i` from
  -- `Algebra.Etale.iff_exists_algEquiv_prod`); the `_h_henselian_local`
  -- witness is applied per factor `B_i := ẽ_i • B` once the
  -- decomposition is in place. The residual sorry encodes the
  -- *assembly* of:
  --   (1) the residue-product identification
  --       `B ⧸ mB ≃ₐ[A ⧸ maximalIdeal A] ∀ i, k_i`
  --       (via `k ⊗_A B ≃ B ⧸ mB` + `Algebra.Etale.baseChange` +
  --        `Algebra.Etale.iff_exists_algEquiv_prod`);
  --   (2) the L3b product decomposition
  --       `B ≃ₐ[A] ∀ i, B_i` (via
  --       `CompleteOrthogonalIdempotents.bijective_pi`);
  --   (3) per-factor application of `HenselianLocalRing.is_henselian`
  --       to the image of `f` in each `B_i`;
  --   (4) reassembly of the per-factor roots into `a ∈ B` with
  --       `f.IsRoot a` and `a - a₀ ∈ mB`.
  -- Stage 1 (`h_sep`) + Stage 2 (`hfn`, `hdiff`) remain available
  -- below to discharge the convergence argument inside step (3) /
  -- per-factor closure.
  have _h_lift_idem :=
    lift_idempotent_henselianPair (A := A) (B := B)
  have _h_henselian_local :=
    @henselianLocalRing_of_finite_over_henselianLocal A B
  sorry

/-- **Stacks 04GG / 09XK; henselian-pair fragment.**

For `A` a henselian local ring and `B` a **finite** étale
`A`-algebra, the pair `(B, m·B)` is a henselian ring: the
extension `m·B` of the maximal ideal of `A` is contained in the
Jacobson radical of `B`, and Hensel's lemma holds for monic
polynomials over `B` at roots mod `m·B`.

This is the abstract endpoint that the four open §3-cluster
sorries (`StrictlyHenselian.lean` L682 / L1767 / L1814 +
`HenselianIdempotentLift.lean` body L160) will consume in
iter-055+ wiring; each consumer must establish
`Module.Finite A B'` for its localized / fibre-restricted `B'`
before applying this instance. -/
instance henselianRing_map_maximalIdeal
    (A B : Type*) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B] :
    HenselianRing B ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) where
  jac := by
    -- Blueprint: `lem:henselianPair-jac` (integral going-up).
    -- For every maximal `J ⊂ B`, the contraction `J ∩ A` is maximal in
    -- the local ring `A` (going-up via integrality from `Module.Finite`),
    -- hence equals `maximalIdeal A`; the map-comap adjunction then gives
    -- `(maximalIdeal A).map (algebraMap A B) ≤ J`.
    haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
    refine le_sInf fun J hJ => ?_
    have hJmax : J.IsMaximal := hJ
    rw [Ideal.map_le_iff_le_comap]
    have hcomap : (J.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
    rw [IsLocalRing.eq_maximalIdeal hcomap]
  is_henselian := by
    -- Reduced to the substantive named helper
    -- `exists_root_of_eval_mem_of_isUnit_derivative_quotient` above;
    -- the structural glue (Jacobson containment, Nakayama unit
    -- upgrade) is closed sorry-free in the helpers
    -- `maximalIdeal_map_le_jacobson_bot` and
    -- `isUnit_of_isUnit_quotient_mk_maximalIdeal_map`. The actual
    -- root-finding step (Stacks 0DXB Newton iteration / 04GE
    -- product decomposition) is isolated to that named helper.
    -- Blueprint: `lem:henselianPair-is-henselian`.
    intro f hf a₀ h_eval h_unit
    exact exists_root_of_eval_mem_of_isUnit_derivative_quotient
      A B f hf a₀ h_eval h_unit

end Algebra.Etale
