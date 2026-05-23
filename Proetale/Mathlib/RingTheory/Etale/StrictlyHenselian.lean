/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Proetale.Mathlib.RingTheory.Henselian

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
    -- The Hensel-lift step requires the substantial result "HenselianLocalRing
    -- has the lifting property for sections of étale algebras", which is the
    -- forward direction of `HenselianLocalRing.TFAE`'s clause about étale lifts.
    -- This is not currently formalized in Mathlib (the project-local
    -- `henselian_if_exists_section` proves only the converse). Left as a typed
    -- sorry pending this infrastructure.
    sorry

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
