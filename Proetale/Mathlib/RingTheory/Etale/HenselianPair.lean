/-
Copyright (c) 2026 The Proetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Unramified.LocalRing
import Proetale.Mathlib.RingTheory.Etale.HenselianIdempotentLift
import Proetale.Mathlib.RingTheory.Etale.HenselianPairCharpolyDescent
import Proetale.Mathlib.RingTheory.Etale.HenselianPairLift

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

universe u

namespace Algebra.Etale

/-! ### Helper lemmas for the henselian-pair construction

The Stacks 0DXB Hensel-lift prerequisites
(`maximalIdeal_map_le_jacobson_bot`,
`isUnit_of_isUnit_quotient_mk_maximalIdeal_map`,
`maximalIdeal_map_iInf_pow_eq_bot`,
`exists_seq_lift_of_henselianPair`,
`idempotent_lift_limit`, `lift_idempotent_henselianPair`) live in
`Proetale/Mathlib/RingTheory/Etale/HenselianPairLift.lean` so that
`HenselianIdempotentLift.lean` can consume `lift_idempotent_henselianPair`
without importing this file (which itself uses the cop-lift
statement to assemble `henselianRing_map_maximalIdeal`).

The §A.2 determinantal unit-bridge `mult_det_isUnit_of_isUnit_mod_maximal`
and the L3c charpoly-descent chain
(`maximalIdeal_map_le_maximalIdeal` … `exists_root_in_finite_henselian_module`,
including all per-coordinate Hensel polynomial intermediate helpers) now
live in `Proetale/Mathlib/RingTheory/Etale/HenselianPairCharpolyDescent.lean`
so that both `HenselianPair.lean` and `HenselianPairLift.lean` can consume
the chain without an import cycle.
-/

/-- **L3b — Stacks 04GE / 0DXB; finite over henselian local decomposes.**

For `A` a Noetherian henselian local ring and `B` a finite étale
`A`-algebra, `B` decomposes as a finite product of finite local
`A`-algebras `Bi i`, each of which is finite over `A`.

Lean carrier pinned by the blueprint chapter
`lem:henselianPair-l3b-product-decomposition`. Route-(D) closure of
the `is_henselian` field on
`Algebra.Etale.henselianRing_map_maximalIdeal` consumes this lemma
as Step 2 of the 5-step amendment paragraph
(chapter L455–L525).

The proof routes through the L3a banked carrier
`Algebra.Etale.exists_completeOrthogonalIdempotents_lift_of_henselian`
(producing a complete orthogonal idempotent family
`eLift : I → B` lifting the residue idempotents of `B / mA·B`)
combined with the Mathlib lemma
`CompleteOrthogonalIdempotents.bijective_pi` (giving the bijection
`B ≃+* ∀ i, B ⧸ Ideal.span {1 - eLift i}`). The per-factor locality
`IsLocalRing (Bi i)` is a substantive sub-claim — under the
present iter-120 scaffold, locality is banked as a typed sub-sorry
pending the residue-field identification
`Bi i / mA · Bi i ≃ kI i` (chapter L352–L364).

Universe constraint `Type u` is inherited from the L3a banked
carrier signature. -/
theorem product_decomposition_of_henselian
    (A B : Type u) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B] :
    ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
      (Bi : I → Type u) (_ : ∀ i, CommRing (Bi i))
      (_ : ∀ i, Algebra A (Bi i))
      (_ : ∀ i, Module.Finite A (Bi i))
      (_ : ∀ i, IsLocalRing (Bi i)),
      Nonempty (B ≃ₐ[A] ∀ i, Bi i) := by
  classical
  -- Step 1 (L3a banked): complete orthogonal idempotent family in `B`
  -- lifting the canonical residue idempotents of `B / mA·B ≃ ∀ i, kI i`.
  obtain ⟨I, hIfin, hIdec, kI, hKfield, hKalg, eqv, eLift, hCOP, hLift⟩ :=
    exists_completeOrthogonalIdempotents_lift_of_henselian A B
  -- Per-factor ring `Bi i := B ⧸ ⟨1 - eLift i⟩`.
  refine ⟨I, hIfin, hIdec,
    fun i => B ⧸ (Ideal.span ({1 - eLift i} : Set B)),
    fun _ => inferInstance,
    fun _ => inferInstance,
    fun _ => inferInstance,
    ?_, ?_⟩
  · -- Per-factor locality: substantive sub-claim.
    -- Chapter L352–L386: argument structure.
    --
    -- Let `Ji := ⟨1 - eLift i⟩`, `Bi := B ⧸ Ji`, and
    -- `mAi := (maximalIdeal A).map (algebraMap A Bi)`. We prove:
    -- (a) `mAi ⊆ Jacobson(Bi)` (via integrality going-up + `A` local);
    -- (b) `mAi` is maximal (via the residue iso `Bi / mAi ≃ kI i`,
    --     packaged as a typed sub-step below);
    -- (c) every maximal ideal of `Bi` equals `mAi`, by (a) + (b).
    intro i
    -- Notation.
    set Ji : Ideal B := Ideal.span ({1 - eLift i} : Set B) with hJi_def
    -- The map `mA → Bi` factors through `B`, so `Bi` is integral over
    -- `A`. (`Algebra.IsIntegral.quotient` is an instance once
    -- `Algebra.IsIntegral A B` is in scope, which holds since `B` is
    -- `Module.Finite A B`.)
    haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite (R := A) (B := B)
    haveI : Algebra.IsIntegral A (B ⧸ Ji) := inferInstance
    -- Step (a). Jacobson containment.
    have hmAi_jac :
        (IsLocalRing.maximalIdeal A).map (algebraMap A (B ⧸ Ji)) ≤
          Ideal.jacobson (⊥ : Ideal (B ⧸ Ji)) := by
      rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
      refine le_sInf fun J hJ => ?_
      have hJmax : J.IsMaximal := hJ
      rw [Ideal.map_le_iff_le_comap]
      have hcomap : (J.comap (algebraMap A (B ⧸ Ji))).IsMaximal :=
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
      rw [IsLocalRing.eq_maximalIdeal hcomap]
    -- Step (b). Maximality of `mAi`. The slick route — instead of
    -- threading the full DoubleQuot chain — is to directly exhibit a
    -- surjective ring hom `φ : B →+* kI i` whose kernel is
    -- `Ji ⊔ mA·B`, then descend to `(B ⧸ Ji) ⧸ mAi ≃ kI i`.
    --
    -- The map: `φ := evalRingHom i ∘ eqv ∘ includeRight`, where
    -- `includeRight : B →ₐ[A] k ⊗ B`, `eqv : k ⊗ B ≃ ∀ j, kI j`,
    -- and `evalRingHom i : (∀ j, kI j) →+* kI i`. The kernel
    -- computation hinges on `hLift` (i.e.
    -- `eqv (includeRight (eLift i)) = Pi.single i 1`) so that
    -- `1 - eLift i` ↦ `1 - Pi.single i 1`, which after
    -- `evalRingHom i` is `0`.
    --
    -- The full chain — surjectivity + the kernel equality
    -- `ker φ = Ji ⊔ mA·B` — is banked as a typed sub-step pending
    -- iter-123 closure. The headline residue iso is what the
    -- chapter L361–L386 paragraph computes.
    have hresidue_iso :
        Nonempty
          ((B ⧸ Ji) ⧸ ((IsLocalRing.maximalIdeal A).map (algebraMap A (B ⧸ Ji)))
            ≃+* kI i) := by
      -- Notation.
      set mA : Ideal A := IsLocalRing.maximalIdeal A with hmA_def
      set mAB : Ideal B := mA.map (algebraMap A B) with hmAB_def
      -- The extended ideal `mA.map (algebraMap A (B ⧸ Ji))` equals
      -- `mAB.map (Quotient.mk Ji)` since `algebraMap A (B ⧸ Ji)`
      -- factors through `B` via the quotient map.
      have hmAi_eq : mA.map (algebraMap A (B ⧸ Ji)) =
          mAB.map (Ideal.Quotient.mk Ji) := by
        rw [hmAB_def, Ideal.map_map]; rfl
      rw [hmAi_eq]
      refine ⟨(DoubleQuot.quotQuotEquivQuotSup Ji mAB).trans ?_⟩
      -- Now reduce `B ⧸ (Ji ⊔ mAB) ≃+* kI i` to a kernel computation
      -- for the surjective ring hom `φ : B →+* kI i`.
      let incR : B →+* TensorProduct A (IsLocalRing.ResidueField A) B :=
        (Algebra.TensorProduct.includeRight :
          B →ₐ[A] TensorProduct A (IsLocalRing.ResidueField A) B).toRingHom
      let eqvR : TensorProduct A (IsLocalRing.ResidueField A) B →+* (∀ j, kI j) :=
        eqv.toRingEquiv.toRingHom
      let evi : (∀ j, kI j) →+* kI i := Pi.evalRingHom kI i
      let φ : B →+* kI i := evi.comp (eqvR.comp incR)
      -- Surjectivity of `φ`.
      have hincR_surj : Function.Surjective incR :=
        Algebra.TensorProduct.includeRight_surjective B
          Ideal.Quotient.mk_surjective
      have heqvR_surj : Function.Surjective eqvR := eqv.surjective
      have hevi_surj : Function.Surjective evi := fun y =>
        ⟨Pi.single i y, Pi.single_eq_same i y⟩
      have hφ_surj : Function.Surjective φ :=
        hevi_surj.comp (heqvR_surj.comp hincR_surj)
      -- The kernel of `incR` equals `mAB`, via the algebra iso
      -- `(B ⧸ mAB) ≃ₐ[k] (A ⧸ mA) ⊗_A B`.
      have h_incR_eq : ∀ b : B, incR b =
          (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B mA)
            ((Ideal.Quotient.mk mAB) b) := fun b => by
        rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]; rfl
      have h_ker_incR_eq : RingHom.ker incR = mAB := by
        ext b
        simp only [RingHom.mem_ker, h_incR_eq]
        refine ⟨fun hxy => ?_, fun hb => ?_⟩
        · have h1 : (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B mA)
              ((Ideal.Quotient.mk mAB) b) =
              (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B mA) 0 := by
            rw [map_zero]; exact hxy
          have h2 : (Ideal.Quotient.mk mAB) b = 0 :=
            (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B mA).injective h1
          exact (Ideal.Quotient.eq_zero_iff_mem).mp h2
        · rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hb]; exact map_zero _
      -- Forward inclusion `Ji ⊔ mAB ≤ ker φ`.
      have h_eqv_eLift : eqvR (incR (eLift i)) = Pi.single i 1 := hLift i
      have h_eqv_1sube : eqvR (incR (1 - eLift i)) =
          (1 : ∀ j, kI j) - Pi.single i 1 := by
        rw [map_sub, map_sub, map_one, map_one, h_eqv_eLift]
      have h_1subEli_ker : (1 - eLift i) ∈ RingHom.ker φ := by
        show evi (eqvR (incR (1 - eLift i))) = 0
        rw [h_eqv_1sube, map_sub, map_one,
          show evi (Pi.single i (1 : kI i)) = 1 from Pi.single_eq_same i 1, sub_self]
      have hJi_ker : Ji ≤ RingHom.ker φ := by
        rw [hJi_def, Ideal.span_le, Set.singleton_subset_iff]
        exact h_1subEli_ker
      have hmAB_ker : mAB ≤ RingHom.ker φ := by
        intro b hb
        have hb' : incR b = 0 := by
          have : b ∈ RingHom.ker incR := h_ker_incR_eq.symm ▸ hb
          exact this
        show evi (eqvR (incR b)) = 0
        rw [hb', map_zero, map_zero]
      have hKi_ker : Ji ⊔ mAB ≤ RingHom.ker φ := sup_le hJi_ker hmAB_ker
      -- Reverse inclusion `ker φ ≤ Ji ⊔ mAB`. If `φ b = 0` then
      -- `eqvR (incR b) = eqvR (incR b) * (1 - Pi.single i 1)` componentwise,
      -- and via `hLift i` this factors through `(1 - eLift i)` modulo
      -- `ker incR = mAB`, giving `b ∈ Ji + mAB`.
      have hker_le : RingHom.ker φ ≤ Ji ⊔ mAB := by
        intro b hb
        have hb_zero : (eqvR (incR b)) i = 0 := hb
        -- Componentwise: `eqvR (incR b) * Pi.single i 1 = 0`.
        have h_mul_single : eqvR (incR b) * Pi.single i 1 = 0 := by
          ext j
          simp only [Pi.mul_apply, Pi.zero_apply]
          by_cases hij : j = i
          · rw [hij, Pi.single_eq_same, mul_one]; exact hb_zero
          · rw [Pi.single_eq_of_ne hij, mul_zero]
        -- Hence `eqvR (incR b) = eqvR (incR b) * (1 - Pi.single i 1)`.
        have hc_factored : eqvR (incR b) =
            eqvR (incR b) * ((1 : ∀ j, kI j) - Pi.single i 1) := by
          rw [mul_sub, mul_one, h_mul_single, sub_zero]
        have hc_factored' : eqvR (incR b) = eqvR (incR (b * (1 - eLift i))) := by
          rw [hc_factored, ← h_eqv_1sube, ← map_mul eqvR, ← map_mul incR]
        have hincR_eq : incR b = incR (b * (1 - eLift i)) :=
          eqv.toRingEquiv.injective hc_factored'
        have hdiff_ker : b - b * (1 - eLift i) ∈ RingHom.ker incR := by
          show incR (b - b * (1 - eLift i)) = 0
          rw [map_sub, hincR_eq, sub_self]
        have hdiff_mAB : b - b * (1 - eLift i) ∈ mAB :=
          h_ker_incR_eq ▸ hdiff_ker
        have hbsum : b = b * (1 - eLift i) + (b - b * (1 - eLift i)) := by ring
        rw [hbsum]
        refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right hdiff_mAB)
        rw [hJi_def]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
      have h_ker_eq : RingHom.ker φ = Ji ⊔ mAB := le_antisymm hker_le hKi_ker
      exact (Ideal.quotEquivOfEq h_ker_eq.symm).trans
        (RingHom.quotientKerEquivOfSurjective hφ_surj)
    have hmAi_max :
        ((IsLocalRing.maximalIdeal A).map (algebraMap A (B ⧸ Ji))).IsMaximal := by
      refine Ideal.Quotient.maximal_of_isField _ ?_
      obtain ⟨φ⟩ := hresidue_iso
      exact φ.toMulEquiv.isField (Field.toIsField _)
    -- Step (c). Combine.
    refine IsLocalRing.of_unique_max_ideal
      ⟨(IsLocalRing.maximalIdeal A).map (algebraMap A (B ⧸ Ji)),
        hmAi_max, ?_⟩
    intro J hJmax
    have hJ : J.IsMaximal := hJmax
    have hJac_le : Ideal.jacobson (⊥ : Ideal (B ⧸ Ji)) ≤ J := by
      rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
      exact sInf_le hJ
    exact (hmAi_max.eq_of_le hJ.ne_top (hmAi_jac.trans hJac_le)).symm
  · -- Step 2: the `B ≃ₐ[A] ∀ i, Bi i` from `bijective_pi`.
    -- The underlying ring hom is
    --   Pi.ringHom fun i => Ideal.Quotient.mk (Ideal.span {1 - eLift i}),
    -- which is the same map as `algebraMap A (∀ i, Bi i)` precomposed
    -- with `algebraMap A B`, so the `commutes` condition is `rfl`.
    refine ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _ hCOP.bijective_pi) ?_⟩
    intro _a
    rfl

/-- **L3c — Finite extension of a henselian local ring is henselian local.**

Stacks Tag 04GH specialised to the local case (`[IsLocalRing B]`).
The L3b product decomposition is bypassed by the `[IsLocalRing B]`
hypothesis. iter-060 closure routes the substantive Newton-
convergence step through the named typed sub-sub-helper
`exists_root_in_finite_henselian_module`. -/
private lemma henselianLocalRing_of_finite_over_henselianLocal
    (A B : Type*) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [IsLocalRing B] :
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
    (A B : Type u) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B]
    [Module.Free A B]
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
  classical
  -- Step 2 (L3b — `product_decomposition_of_henselian`): factor `B` as
  -- a finite product of finite local `A`-algebras.
  obtain ⟨I, hIfin, hIdec, Bi, hCRi, hAlgi, hFini, hLocali, ⟨Φ⟩⟩ :=
    product_decomposition_of_henselian (A := A) (B := B)
  -- iter-124 final-assembly scaffold (Floor target Q=1.0).
  --
  -- The route-(D) closure plan (chapter L546–L586 Steps 3–5):
  -- (3) push `f`, `a₀` along `Φ` per factor;
  -- (4) apply L3c `henselianLocalRing_of_finite_over_henselianLocal`
  --     per factor to obtain `αᵢ ∈ Bᵢ` with `fᵢ.IsRoot αᵢ ∧
  --     αᵢ - a₀ᵢ ∈ mA·Bᵢ`;
  -- (5) reassemble `α := Φ.symm (fun i => αᵢ)` and verify
  --     `f.IsRoot α ∧ α - a₀ ∈ mA·B`.
  --
  -- The remaining substantive obligation isolated to a single typed
  -- sub-sorry below is the per-factor residue-field identification
  -- `IsLocalRing.maximalIdeal (Bᵢ) = (mA).map (algebraMap A Bᵢ)`,
  -- i.e. the Ceiling target `bi_residue_field_iso_of_henselian`.
  -- Granting it, the per-factor Hensel lift yields `αᵢ - a₀ᵢ`
  -- inside `mA·Bᵢ`, and the reassembly via `Φ.symm` plus the
  -- `Pi.single` componentwise decomposition transports the bound to
  -- `mA·B`.
  -- Per-factor flatness (étale ⇒ flat for B; transport via Φ; retract).
  haveI hFlat : ∀ i, Module.Flat A (Bi i) := by
    haveI hFlatProd : Module.Flat A (∀ i, Bi i) :=
      Module.Flat.of_linearEquiv Φ.symm.toLinearEquiv
    intro i
    refine Module.Flat.of_retract
      (R := A) (M := ∀ j, Bi j) (N := Bi i)
      (LinearMap.single A Bi i) (LinearMap.proj i) ?_
    exact LinearMap.proj_comp_single_same A Bi i
  -- Per-factor freeness (flat + local + Noetherian + finite ⇒ free).
  haveI hFree : ∀ i, Module.Free A (Bi i) := fun _ =>
    Module.free_of_flat_of_isLocalRing
  -- Per-factor HenselianLocalRing (L3c).
  haveI hHen : ∀ i, HenselianLocalRing (Bi i) := fun i =>
    henselianLocalRing_of_finite_over_henselianLocal A (Bi i)
  -- The per-factor projection `πᵢ : B →+* Bᵢ` (i-th evaluation
  -- composed with `Φ` viewed as a ring hom). It is an `A`-algebra hom
  -- because both factors are, hence intertwines `algebraMap A B` and
  -- `algebraMap A (Bᵢ)` (proved as `hπi_alg` below).
  let πi : ∀ i, B →+* Bi i := fun i =>
    (Pi.evalRingHom (fun j => Bi j) i).comp (Φ : B →+* ∀ j, Bi j)
  -- `πi i` intertwines the algebra maps from A.
  have hπi_alg : ∀ i, (πi i).comp (algebraMap A B) = algebraMap A (Bi i) := by
    intro i
    ext a
    show (Pi.evalRingHom (fun j => Bi j) i)
      ((Φ : B →+* ∀ j, Bi j) (algebraMap A B a)) = algebraMap A (Bi i) a
    have h1 : (Φ : B →+* ∀ j, Bi j) (algebraMap A B a) =
        algebraMap A (∀ j, Bi j) a := by
      simp [Φ.commutes a]
    rw [h1]
    exact Pi.algebraMap_apply I Bi a i
  -- Sub-claim (Ceiling target `bi_residue_field_iso_of_henselian`):
  -- per-factor residue-field identification.
  -- For each `i`, `(Bᵢ)/(mA·Bᵢ) ≃+* kᵢ` is a field, hence
  -- `IsLocalRing.maximalIdeal (Bᵢ) = (mA).map (algebraMap A Bᵢ)`.
  -- The proof follows the same residue-iso construction as the
  -- `hresidue_iso` block inside `product_decomposition_of_henselian`
  -- (chapter L361–L386).
  -- Transport `FormallyEtale A B` to per-factor `FormallyEtale A (Bᵢ)`
  -- via `Φ` and `Algebra.FormallyEtale.pi_iff`.
  haveI : Algebra.FormallyEtale A (∀ j, Bi j) :=
    Algebra.FormallyEtale.of_equiv Φ
  haveI hFEtBi : ∀ k, Algebra.FormallyEtale A (Bi k) :=
    (Algebra.FormallyEtale.pi_iff Bi).mp inferInstance
  have hMaxEq : ∀ i, IsLocalRing.maximalIdeal (Bi i) =
      (IsLocalRing.maximalIdeal A).map (algebraMap A (Bi i)) := by
    intro i
    -- Specialise FormallyEtale → FormallyUnramified per factor.
    haveI : Algebra.FormallyUnramified A (Bi i) :=
      (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mp
        (hFEtBi i)).1
    -- `algebraMap A (Bᵢ)` is a local hom (image of `mA` ⊆ `mBᵢ`).
    haveI : IsLocalHom (algebraMap A (Bi i)) := ⟨by
      intro a ha
      by_contra hna
      have ha_mA : a ∈ IsLocalRing.maximalIdeal A := by
        rw [IsLocalRing.mem_maximalIdeal]
        exact hna
      have h1 : algebraMap A (Bi i) a ∈
          (IsLocalRing.maximalIdeal A).map (algebraMap A (Bi i)) :=
        Ideal.mem_map_of_mem _ ha_mA
      have h2 : algebraMap A (Bi i) a ∈ IsLocalRing.maximalIdeal (Bi i) :=
        maximalIdeal_map_le_maximalIdeal A (Bi i) h1
      rw [IsLocalRing.mem_maximalIdeal] at h2
      exact h2 ha⟩
    -- `Bᵢ` is essentially of finite type over `A` (from `Module.Finite`).
    haveI : Algebra.EssFiniteType A (Bi i) :=
      Algebra.EssFiniteType.of_finiteType A (Bi i)
    -- Hence `(Bᵢ)/(mA·Bᵢ)` is a field
    -- (`Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal`).
    have hField : IsField
        ((Bi i) ⧸ Ideal.map (algebraMap A (Bi i))
          (IsLocalRing.maximalIdeal A)) :=
      Algebra.FormallyUnramified.isField_quotient_map_maximalIdeal
    -- So `mA·Bᵢ` is a maximal ideal of `Bᵢ`. Since `Bᵢ` is local with
    -- unique maximal ideal `maximalIdeal (Bᵢ)`, the two coincide.
    have hMax : ((IsLocalRing.maximalIdeal A).map (algebraMap A (Bi i))).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ hField
    exact (IsLocalRing.eq_maximalIdeal hMax).symm
  -- Per-factor data: `fᵢ := f.map πᵢ`, `a₀ᵢ := πᵢ a₀`.
  let fi : ∀ i, Polynomial (Bi i) := fun i => f.map (πi i)
  let a0i : ∀ i, Bi i := fun i => πi i a₀
  -- Monicity of `fᵢ`.
  have hfi_monic : ∀ i, (fi i).Monic := fun i => hf.map (πi i)
  -- Evaluation `fᵢ.eval a₀ᵢ ∈ max(Bᵢ)` from `f.eval a₀ ∈ mA·B`.
  have hfi_eval : ∀ i, (fi i).eval (a0i i) ∈
      IsLocalRing.maximalIdeal (Bi i) := by
    intro i
    rw [hMaxEq i]
    show (f.map (πi i)).eval (πi i a₀) ∈ _
    rw [Polynomial.eval_map_apply]
    have hmem : (πi i) (f.eval a₀) ∈
        ((IsLocalRing.maximalIdeal A).map (algebraMap A B)).map (πi i) :=
      Ideal.mem_map_of_mem _ h_eval
    rwa [Ideal.map_map, hπi_alg i] at hmem
  -- Derivative: `(fᵢ).derivative.eval a₀ᵢ = πᵢ (f.derivative.eval a₀)`,
  -- which is a unit since `πᵢ` is a ring hom and the original is a unit.
  have hfi_unit : ∀ i,
      IsUnit ((fi i).derivative.eval (a0i i)) := by
    intro i
    have h1 : (fi i).derivative.eval (a0i i) = (πi i) (f.derivative.eval a₀) := by
      show ((f.map (πi i)).derivative).eval (πi i a₀) = _
      rw [Polynomial.derivative_map, Polynomial.eval_map_apply]
    rw [h1]
    exact h_unit_B.map (πi i)
  -- Per-factor Hensel application.
  have hRoot_i : ∀ i, ∃ α : Bi i, (fi i).IsRoot α ∧
      α - a0i i ∈ IsLocalRing.maximalIdeal (Bi i) := fun i =>
    HenselianLocalRing.is_henselian (fi i) (hfi_monic i) (a0i i)
      (hfi_eval i) (hfi_unit i)
  choose αi hαi_root hαi_diff using hRoot_i
  -- Reassemble: `α := Φ.symm (fun i => αᵢ)`.
  refine ⟨Φ.symm (fun i => αi i), ?_, ?_⟩
  · -- Verify `f.IsRoot α`, i.e. `f.eval α = 0`.
    show f.eval (Φ.symm (fun i => αi i)) = 0
    -- Strategy: apply `Φ` to both sides; the i-th component vanishes
    -- because it equals `eval αᵢ fᵢ = 0`.
    apply Φ.injective
    rw [map_zero]
    -- Φ (eval (Φ.symm c) f) = eval c (f.map Φ), by Polynomial.eval_map_apply.
    have hΦ_eval :
        (Φ : B →+* ∀ j, Bi j) (f.eval (Φ.symm (fun i => αi i))) =
        Polynomial.eval (fun i => αi i)
          (f.map (Φ : B →+* ∀ j, Bi j)) := by
      have hkey := (Polynomial.eval_map_apply (p := f)
        (Φ : B →+* ∀ j, Bi j) (Φ.symm (fun i => αi i))).symm
      rw [show (Φ : B →+* ∀ j, Bi j) (Φ.symm (fun i => αi i)) =
        (fun i => αi i) from Φ.apply_symm_apply _] at hkey
      exact hkey
    show (Φ : B →+* ∀ j, Bi j) (f.eval (Φ.symm (fun i => αi i))) = 0
    rw [hΦ_eval]
    -- Now show every component of `eval (fun j => αj) (f.map Φ)` is 0.
    funext i
    show (Pi.evalRingHom (fun j => Bi j) i)
      (Polynomial.eval (fun j => αi j)
        (f.map (Φ : B →+* ∀ j, Bi j))) = 0
    have hcomp := (Polynomial.eval_map_apply
      (p := f.map (Φ : B →+* ∀ j, Bi j))
      (Pi.evalRingHom (fun j => Bi j) i) (fun j => αi j))
    -- hcomp : eval ((Pi.evalRingHom _ i) (fun j => αj))
    --          (map (Pi.evalRingHom _ i) (map Φ f))
    --       = (Pi.evalRingHom _ i) (eval (fun j => αj) (map Φ f))
    show _ = (0 : Bi i)
    rw [← hcomp, Polynomial.map_map]
    show Polynomial.eval (αi i) (f.map (πi i)) = 0
    exact hαi_root i
  · -- Verify `α - a₀ ∈ mA·B`. Push to the product, reassemble via
    -- `Pi.single` decomposition.
    -- Φ (α - a₀) = (fun i => αᵢ - a₀ᵢ) componentwise, and each
    -- coordinate lies in `mA·Bᵢ` (by `hαi_diff` and `hMaxEq`).
    have hdiff_comp : ∀ i, αi i - a0i i ∈
        (IsLocalRing.maximalIdeal A).map (algebraMap A (Bi i)) := by
      intro i
      rw [← hMaxEq i]
      exact hαi_diff i
    -- Build the product-side element `Φ (α - a₀)` and recognise it as
    -- `(fun i => αᵢ - a₀ᵢ)`.
    have hΦsub : (Φ : B →+* ∀ j, Bi j) (Φ.symm (fun i => αi i) - a₀) =
        (fun i => αi i - a0i i) := by
      rw [map_sub]
      funext i
      show ((Φ : B →+* ∀ j, Bi j) (Φ.symm (fun j => αi j))) i -
          ((Φ : B →+* ∀ j, Bi j) a₀) i = αi i - a0i i
      have hφs : (Φ : B →+* ∀ j, Bi j) (Φ.symm (fun j => αi j)) =
          (fun j => αi j) := Φ.apply_symm_apply _
      rw [hφs]
      rfl
    -- It suffices to show `Φ (α - a₀) ∈ (mA).map (algebraMap A (∀ j, Bj))`.
    -- For then by transporting along Φ.symm we get the bound in `B`.
    suffices h : (Φ : B →+* ∀ j, Bi j) (Φ.symm (fun i => αi i) - a₀) ∈
        (IsLocalRing.maximalIdeal A).map (algebraMap A (∀ j, Bi j)) by
      -- Transport via Φ.symm.
      have h2 : (Φ.symm : (∀ j, Bi j) →+* B)
          ((Φ : B →+* ∀ j, Bi j) (Φ.symm (fun i => αi i) - a₀)) ∈
          ((IsLocalRing.maximalIdeal A).map (algebraMap A (∀ j, Bi j))).map
            (Φ.symm : (∀ j, Bi j) →+* B) :=
        Ideal.mem_map_of_mem _ h
      have hsymm_alg : (Φ.symm : (∀ j, Bi j) →+* B).comp
          (algebraMap A (∀ j, Bi j)) = algebraMap A B := by
        ext a
        show Φ.symm (algebraMap A (∀ j, Bi j) a) = algebraMap A B a
        rw [show algebraMap A (∀ j, Bi j) a = Φ (algebraMap A B a) from
          (Φ.commutes a).symm, Φ.symm_apply_apply]
      rw [Ideal.map_map, hsymm_alg] at h2
      have hcoerce : (Φ.symm : (∀ j, Bi j) →+* B)
          ((Φ : B →+* ∀ j, Bi j) (Φ.symm (fun i => αi i) - a₀)) =
          (Φ.symm (fun i => αi i) - a₀) := Φ.symm_apply_apply _
      rwa [hcoerce] at h2
    -- Now show: `(fun i => αᵢ - a₀ᵢ) ∈ mA·(∀ j, Bj)` via Pi.single.
    rw [hΦsub]
    -- Decompose as a finite sum of `Pi.single i (αᵢ - a₀ᵢ)`.
    have hsum : (fun i => αi i - a0i i) =
        ∑ i : I, Pi.single i (αi i - a0i i) := by
      funext j
      simp [Finset.sum_pi_single]
    rw [hsum]
    refine Ideal.sum_mem _ fun i _ => ?_
    -- Show `Pi.single i (αᵢ - a₀ᵢ) ∈ mA·(∀ j, Bj)`.
    -- Use Submodule.span_induction on `αi i - a0i i` in the ideal
    -- `(IsLocalRing.maximalIdeal A).map (algebraMap A (Bi i))`,
    -- treated as `Submodule.span (Bi i) (algebraMap A (Bi i) '' mA)`.
    have hαi_in := hdiff_comp i
    have hideal_eq :
        (IsLocalRing.maximalIdeal A).map (algebraMap A (Bi i)) =
        Ideal.span ((algebraMap A (Bi i)) ''
          (IsLocalRing.maximalIdeal A : Set A)) := by
      conv_lhs => rw [← Ideal.span_eq (IsLocalRing.maximalIdeal A)]
      exact Ideal.map_span _ _
    rw [hideal_eq] at hαi_in
    refine Submodule.span_induction
      (p := fun x _ => Pi.single i x ∈
        (IsLocalRing.maximalIdeal A).map (algebraMap A (∀ j, Bi j)))
      ?_ ?_ ?_ ?_ hαi_in
    · rintro x ⟨c, hc, rfl⟩
      -- `Pi.single i (algebraMap A (Bᵢ) c) = algebraMap A (∀j, Bj) c * Pi.single i 1`,
      have heq : Pi.single i ((algebraMap A (Bi i)) c) =
          algebraMap A (∀ j, Bi j) c * Pi.single i 1 := by
        funext j
        by_cases hij : j = i
        · subst hij
          simp [Pi.single_eq_same, Pi.algebraMap_apply]
        · rw [Pi.single_eq_of_ne hij, Pi.mul_apply, Pi.single_eq_of_ne hij,
            mul_zero]
      rw [heq]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc)
    · simp
    · intro x y _ _ hx hy
      have : Pi.single i (x + y) = Pi.single i x + Pi.single i y := by
        funext j
        by_cases hij : j = i
        · subst hij; simp [Pi.single_eq_same]
        · simp [Pi.single_eq_of_ne hij]
      rw [this]
      exact Ideal.add_mem _ hx hy
    · intro c x _ hx
      have hsmul : Pi.single i (c • x) = Pi.single i c * Pi.single i x := by
        funext j
        by_cases hij : j = i
        · subst hij; simp [Pi.single_eq_same, smul_eq_mul]
        · simp [Pi.single_eq_of_ne hij]
      rw [hsmul]
      exact Ideal.mul_mem_left _ _ hx

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
    (A B : Type u) [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A]
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
    -- iter-072 refactor: derive `Module.Free A B` locally from the étale +
    -- finite + local hypotheses (`Algebra.Etale → Module.Flat` via the
    -- `Smooth.flat` instance, then `Module.free_of_flat_of_isLocalRing`).
    -- This is consumed by `descend_root_from_mAB_newton`'s
    -- `Module.Free.chooseBasis` invocation deeper in the call chain, while
    -- keeping the headline's public typeclass surface unchanged.
    haveI : Module.Free A B := Module.free_of_flat_of_isLocalRing
    exact exists_root_of_eval_mem_of_isUnit_derivative_quotient
      A B f hf a₀ h_eval h_unit

end Algebra.Etale
