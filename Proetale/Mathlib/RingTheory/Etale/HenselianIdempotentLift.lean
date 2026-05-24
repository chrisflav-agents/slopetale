/-
Copyright (c) 2026 The Proetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.TensorProduct.Basic

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
    (A B : Type u) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] :
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
  -- ===== Step 2 (Hensel-idempotent lift; Mathlib-PR target, Stacks 0DXB). =====
  --
  -- The substantive remaining content factors through one missing
  -- piece of Mathlib infrastructure: the **Stacks 04GG / 0DXB henselian-pair
  -- statement** that `(B, mB)` is a henselian ring whenever `A` is henselian
  -- local and `B` is étale over `A`. Once that is available, the lift of
  -- each `Pi.single i 1` idempotent follows by applying
  -- `HenselianRing.is_henselian` to the monic polynomial `f := X² - X ∈ B[X]`
  -- at the naive root `e₀ i`:
  --
  -- * `f.eval (e₀ i) = (e₀ i)² - e₀ i ∈ mB`, because the image
  --   `inj (e₀ i) = eqv.symm (Pi.single i 1)` is an idempotent in
  --   `k ⊗_A B`, so its square equals itself there, and the kernel of
  --   `inj` is `mB`.
  -- * `f.derivative.eval (e₀ i) = 2·e₀ i - 1` is a unit mod `mB`: under
  --   `eqv ∘ inj`, it maps to `2·Pi.single i 1 - 1 ∈ ∀ j, kI j`, whose
  --   `i`-coordinate is `1` and whose `j`-coordinate for `j ≠ i` is `-1` —
  --   both units in the respective residue fields `kI j`, so the
  --   product is a unit.
  --
  -- Pairwise orthogonality and completeness of the resulting `eLift`
  -- collection then follow from the Jacobson-radical containment
  -- `mB ⊆ Ring.jacobson B` (which is part of the `HenselianRing`
  -- predicate): each `eLift i * eLift j` (for `i ≠ j`) is an idempotent
  -- in `B` whose image in `B/mB` is `0`, hence (being an idempotent in
  -- the Jacobson radical) is `0`; and `∑ i, eLift i` is an idempotent
  -- whose image in `B/mB` is `1`, hence (being an idempotent that is a
  -- unit) is `1`.
  --
  -- The single Mathlib-PR gap is therefore the assertion
  -- `HenselianRing B mB`. Once this is in place, the deduction outlined
  -- above goes through. We bundle the whole remaining `∃ eLift, …` step
  -- as a single typed sorry pending that infrastructure; iter-050+
  -- targets either (i) introducing a `HenselianPair` predicate in
  -- `Proetale/Mathlib/RingTheory/HenselianPair/Defs.lean` and proving
  -- `(B, mB)` is a henselian pair, or (ii) directly bundling
  -- `HenselianRing B mB` from the étale + henselian-local hypotheses.
  --
  -- The naive lifts `e₀ : I → B` and the surjectivity witness
  -- `hinj_surj` constructed above are kept in scope: they form the
  -- starting data for the Hensel-lift step and will be reused verbatim
  -- once the missing predicate lands.
  --
  -- Suppress unused-variable warnings on the locally-bound setup data
  -- (`hm_def`, `hmB_def`, `e₀`, `he₀`) — they document the proof
  -- structure for the next iteration.
  have _hm_def := hm_def
  have _hmB_def := hmB_def
  have _e₀ := e₀
  have _he₀ := he₀
  sorry

end Algebra.Etale
