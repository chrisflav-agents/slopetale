/-
Copyright (c) 2026 The slopetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Proetale.Algebra.WeaklyEtale

/-!
# Finite product of weakly-étale algebras

If `B i` is a weakly étale `A`-algebra for each `i` in a finite indexing type,
then `∀ i, B i` is a weakly étale `A`-algebra.
-/

universe u v

open scoped TensorProduct

/-- A finite product of flat modules is flat.

TODO: upstream candidate; could live in `Mathlib/RingTheory/Flat/Pi.lean`. -/
private lemma Module.Flat.finitePi
    {R : Type*} [CommSemiring R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  classical
  cases nonempty_fintype ι
  exact .of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι M).symm

/-- A projection from a finite product of commutative rings is flat as a ring map. -/
private lemma _root_.Pi.evalRingHom_flat
    {ι : Type*} [DecidableEq ι] (B : ι → Type*) [∀ i, CommRing (B i)] (i : ι) :
    (_root_.Pi.evalRingHom B i).Flat := by
  letI : Algebra (∀ j, B j) (B i) := (_root_.Pi.evalRingHom B i).toAlgebra
  have he : IsIdempotentElem (_root_.Pi.single i 1 : ∀ j, B j) := by
    show (_root_.Pi.single i 1 : ∀ j, B j) * (_root_.Pi.single i 1 : ∀ j, B j) = _
    rw [← _root_.Pi.single_mul]; simp
  have hker : RingHom.ker (_root_.Pi.evalRingHom B i)
      = Ideal.span {1 - _root_.Pi.single i 1} := _root_.RingHom.ker_evalRingHom B i
  have hsurj : Function.Surjective (_root_.Pi.evalRingHom B i) :=
    Function.surjective_eval i
  have hker' : RingHom.ker (algebraMap (∀ j, B j) (B i)) =
      Ideal.span {1 - _root_.Pi.single i 1} := hker
  have hsurj' : Function.Surjective (algebraMap (∀ j, B j) (B i)) := hsurj
  haveI : IsLocalization.Away (_root_.Pi.single i 1 : ∀ j, B j) (B i) :=
    IsLocalization.away_of_isIdempotentElem he hker' hsurj'
  show Module.Flat (∀ j, B j) (B i)
  exact IsLocalization.flat (B i) (Submonoid.powers (_root_.Pi.single i 1 : ∀ j, B j))

namespace Algebra

/-- A finite product of weakly-étale algebras over `A` is weakly-étale. -/
instance WeaklyEtale.pi {A : Type u} [CommRing A]
    {ι : Type v} [Finite ι] {B : ι → Type*}
    [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    [∀ i, Algebra.WeaklyEtale A (B i)] :
    Algebra.WeaklyEtale A (∀ i, B i) := by
  classical
  cases nonempty_fintype ι
  refine ⟨Module.Flat.finitePi, ?_⟩
  -- Goal: `(lmul' A (∀ i, B i)).Flat`.
  -- Strategy: show this is equivalent to `Module.Flat (S ⊗ S) S` with S = ∀ i, B i, via the
  -- `lmul'`-Algebra instance, which by finite-Pi decomposition reduces to per-k flatness of
  -- `B k` over `S ⊗ S`. The latter is established via `(lmul' B_k) ∘ (map proj_k proj_k)`.
  let S := ∀ i, B i
  -- Install per-k algebra structures via `proj_k ∘ lmul'` — this matches the Pi-Module
  -- structure on `∀ k, B k` componentwise, ensuring all Module instances align.
  letI algSS_Bk : ∀ k, Algebra (S ⊗[A] S) (B k) := fun k =>
    ((_root_.Pi.evalAlgHom A B k).toRingHom.comp
      (Algebra.TensorProduct.lmul' A (S := S)).toRingHom).toAlgebra
  haveI flatBk : ∀ k, Module.Flat (S ⊗[A] S) (B k) := by
    intro k
    -- algSS_Bk k's algebraMap equals (lmul' B_k).comp (map proj_k proj_k) by naturality.
    have hf : (_root_.Pi.evalAlgHom A B k).toRingHom.Flat := _root_.Pi.evalRingHom_flat B k
    have h1 : (Algebra.TensorProduct.map (_root_.Pi.evalAlgHom A B k)
        (_root_.Pi.evalAlgHom A B k)).toRingHom.Flat :=
      Algebra.TensorProduct.flat_map hf hf
    have h2 : (Algebra.TensorProduct.lmul' A (S := B k)).toRingHom.Flat :=
      Algebra.WeaklyEtale.flat_lmul' A (B k)
    have hcomp_flat : ((Algebra.TensorProduct.lmul' A (S := B k)).toRingHom.comp
        (Algebra.TensorProduct.map (_root_.Pi.evalAlgHom A B k)
          (_root_.Pi.evalAlgHom A B k)).toRingHom).Flat := RingHom.Flat.comp h1 h2
    -- The natural composition `proj_k ∘ lmul' A S` equals `lmul' A (B k) ∘ map proj_k proj_k`.
    have hnat_alg : (_root_.Pi.evalAlgHom A B k).comp
          (Algebra.TensorProduct.lmul' A (S := S)) =
        (Algebra.TensorProduct.lmul' A (S := B k)).comp
          (Algebra.TensorProduct.map (_root_.Pi.evalAlgHom A B k)
            (_root_.Pi.evalAlgHom A B k)) := by
      apply Algebra.TensorProduct.ext
      · ext x
        change (_root_.Pi.evalAlgHom A B k) (Algebra.TensorProduct.lmul' A (x ⊗ₜ[A] 1)) =
            Algebra.TensorProduct.lmul' A (S := B k)
              (Algebra.TensorProduct.map (_root_.Pi.evalAlgHom A B k)
                (_root_.Pi.evalAlgHom A B k) (x ⊗ₜ[A] 1))
        rw [Algebra.TensorProduct.lmul'_apply_tmul,
            Algebra.TensorProduct.map_tmul,
            Algebra.TensorProduct.lmul'_apply_tmul,
            map_one, mul_one, mul_one]
      · ext x
        change (_root_.Pi.evalAlgHom A B k) (Algebra.TensorProduct.lmul' A (1 ⊗ₜ[A] x)) =
            Algebra.TensorProduct.lmul' A (S := B k)
              (Algebra.TensorProduct.map (_root_.Pi.evalAlgHom A B k)
                (_root_.Pi.evalAlgHom A B k) (1 ⊗ₜ[A] x))
        rw [Algebra.TensorProduct.lmul'_apply_tmul,
            Algebra.TensorProduct.map_tmul,
            Algebra.TensorProduct.lmul'_apply_tmul,
            map_one, one_mul, one_mul]
    have heq : ((_root_.Pi.evalAlgHom A B k).toRingHom.comp
          (Algebra.TensorProduct.lmul' A (S := S)).toRingHom) =
        ((Algebra.TensorProduct.lmul' A (S := B k)).toRingHom.comp
          (Algebra.TensorProduct.map (_root_.Pi.evalAlgHom A B k)
            (_root_.Pi.evalAlgHom A B k)).toRingHom) := by
      have := congr_arg AlgHom.toRingHom hnat_alg
      simpa using this
    -- `(algSS_Bk k).algebraMap` is `proj_k.comp (lmul' A S)`.
    show Module.Flat (S ⊗[A] S) (B k)
    show RingHom.Flat ((_root_.Pi.evalAlgHom A B k).toRingHom.comp
      (Algebra.TensorProduct.lmul' A (S := S)).toRingHom)
    rw [heq]
    exact hcomp_flat
  -- Apply finite-Pi flat.
  have piFlat : Module.Flat (S ⊗[A] S) (∀ k, B k) := Module.Flat.finitePi
  -- The Pi.module structure on `∀ k, B k` (from `algSS_Bk`s) coincides with the lmul'-Module
  -- structure on `S`: both give `(t • f) k = (proj_k ∘ lmul' A) t * f k`.
  show ((Algebra.TensorProduct.lmul' A (S := S)).toRingHom).Flat
  show Module.Flat (S ⊗[A] S) S
  exact piFlat

end Algebra
