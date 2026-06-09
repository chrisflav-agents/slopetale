/-
Copyright (c) 2026 The Proetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Proetale.Mathlib.RingTheory.Etale.HenselianIdempotentLift
import Proetale.Mathlib.RingTheory.Etale.HenselianPair

/-!
# Localisation of étale algebras at maximals above a Henselian local base

For `A` a Noetherian local Henselian ring and `B` a module-finite étale
`A`-algebra, every maximal ideal `n ⊂ B` lying above the maximal of `A`
yields a localisation `B_n` that is finite **and** étale over `A`. This
is the at-the-fibre form of Stacks 04GG, formalised via Route (A) —
lifting the residue-product isolating idempotent through the
henselian-pair idempotent lift `etale-henselian-cop-lift`.

## Main results

* `Algebra.Etale.residue_product_decomposition` — Stacks 00U7
  applied to `k ⊗_A B`: a finite product decomposition of the
  residue base change into finite separable extensions of
  `k := IsLocalRing.ResidueField A`.
* `Algebra.Etale.exists_isolating_idempotent_at_maxIdeal` — Stacks 0DXB
  fragment: the residue-product idempotent isolating `n`'s factor lifts
  to a true idempotent `e ∈ B` with the spectral-isolation property.
* `Algebra.Etale.localisation_finite_at_maximal` — Stacks 04GG: the
  localisation `B_n` is module-finite over `A`.
* `Algebra.Etale.localisation_etale_at_maximal` — Stacks 04GG: the
  localisation `B_n` is étale over `A`.

See `blueprint/src/chapters/Proetale_Mathlib_RingTheory_Etale_LocalisationFiniteAtMaximal.tex`
for the informal proof recipe.
-/

open IsLocalRing TensorProduct

namespace Algebra.Etale

universe u

/-- **Étale residue product decomposition** (Stacks 00U7 applied to
the special fibre).

For `A` local and `B` a module-finite étale `A`-algebra, the base
change `k ⊗_A B` to the residue field `k := IsLocalRing.ResidueField A`
decomposes as a finite product of finite separable extensions of `k`.
This packages `Algebra.Etale.iff_exists_algEquiv_prod` applied to
`k ⊗_A B`, recording the index set, the family of factor fields, and
the explicit algebra isomorphism. -/
theorem residue_product_decomposition
    (A B : Type u) [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Algebra.Etale A B] :
    ∃ (I : Type u) (_ : Finite I) (kI : I → Type u)
      (_ : ∀ i, Field (kI i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField A) (kI i))
      (_ : TensorProduct A (IsLocalRing.ResidueField A) B
              ≃ₐ[IsLocalRing.ResidueField A] ∀ i, kI i),
      ∀ i, Module.Finite (IsLocalRing.ResidueField A) (kI i) ∧
           Algebra.IsSeparable (IsLocalRing.ResidueField A) (kI i) := by
  -- The base change `k ⊗_A B` is étale over `k := ResidueField A` by stability
  -- of étaleness under base change. Then the étale-over-field structure
  -- theorem `Algebra.Etale.iff_exists_algEquiv_prod` (Stacks 00U7) supplies
  -- the requested finite-product decomposition.
  haveI : Algebra.Etale (IsLocalRing.ResidueField A)
      (TensorProduct A (IsLocalRing.ResidueField A) B) :=
    Algebra.Etale.baseChange A B (IsLocalRing.ResidueField A)
  exact (Algebra.Etale.iff_exists_algEquiv_prod
    (K := IsLocalRing.ResidueField A)
    (A := TensorProduct A (IsLocalRing.ResidueField A) B)).mp inferInstance

/-- **Existence of an isolating idempotent at the chosen maximal**
(chapter L93–L116; `lem:etale-isolating-idempotent-fibre`).

Let `A` be Noetherian local Henselian, `B` module-finite étale
over `A`, and let `n ⊂ B` be a maximal ideal lying above the
maximal ideal `mA` of `A`. Suppose given a residue-product
decomposition `φ : k ⊗_A B ≃ₐ[k] ∀ i ∈ I, kI i` (as produced by
`Algebra.Etale.residue_product_decomposition`). Then there exists
an index `iₙ : I` and an idempotent `e ∈ B` such that:

(1) the image of `e` in `k ⊗_A B` is `φ.symm (Pi.single iₙ 1)`
    (the canonical orthogonal idempotent of the `iₙ`-component);
(2) `n` is the unique maximal of `B` above `mA` not containing `e`
    (spectral isolation).

This is the at-the-fibre application of the henselian-pair
idempotent lift `etale-henselian-cop-lift`: the index `iₙ` is the
unique residue-product coordinate where the image of `n` does not
vanish, and `e` lifts the corresponding orthogonal idempotent
`ē_{iₙ}` of `∀ j, kI j` through the henselian-pair structure on
`(B, mA·B)`. -/
theorem exists_isolating_idempotent_at_maxIdeal
    (A B : Type u) [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal] [n.LiesOver (IsLocalRing.maximalIdeal A)]
    (I : Type u) [Finite I] [DecidableEq I] (kI : I → Type u) [∀ i, Field (kI i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (kI i)]
    (φ : TensorProduct A (IsLocalRing.ResidueField A) B
           ≃ₐ[IsLocalRing.ResidueField A] ∀ i, kI i) :
    ∃ (iₙ : I) (e : B),
      IsIdempotentElem e ∧
      -- (1) Residue match: the image of `e` in `k ⊗_A B` matches the
      -- canonical orthogonal idempotent of the `iₙ`-component.
      -- The `iₙ` is the unique index whose residue-product
      -- coordinate corresponds to `n` (the chapter L106–L113
      -- pins this uniqueness; encoded implicitly by combining
      -- this conjunct with conjunct (2)).
      (Algebra.TensorProduct.includeRight (R := A)
          (A := IsLocalRing.ResidueField A) (B := B) e) =
        φ.symm (Pi.single iₙ 1) ∧
      -- (2) Spectral isolation: among maximals of `B` above `m_A`,
      -- the unique one not containing `e` is `n`.
      (∀ (m : Ideal B) [m.IsMaximal] [m.LiesOver (IsLocalRing.maximalIdeal A)],
        (e ∉ m ↔ m = n)) := by
  classical
  haveI : Fintype I := Fintype.ofFinite I
  -- ===== Step 1: construct the residue surjection =====
  -- Form the surjective ring hom `g : B → ∀ i, kI i` factoring through
  -- `k ⊗_A B`, with kernel `mA · B`. The maximal `n` lies above `mA`,
  -- hence contains `mA · B = ker g`, so its image under `g` is a maximal
  -- of `∀ i, kI i`. Maximals of a finite product of fields are kernels of
  -- coordinate projections (`PrimeSpectrum.exists_comap_evalRingHom_eq`).
  -- The index `iₙ` is then read off.
  set incR : B →ₐ[A] TensorProduct A (IsLocalRing.ResidueField A) B :=
    Algebra.TensorProduct.includeRight with hincR_def
  have hincR_surj : Function.Surjective incR :=
    Algebra.TensorProduct.includeRight_surjective B
      (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal A))
  set g : B →+* (∀ i, kI i) :=
    (φ.toAlgHom.toRingHom).comp incR.toRingHom with hg_def
  have hg_surj : Function.Surjective g :=
    φ.surjective.comp hincR_surj
  -- `mA · B ⊆ n` from `n.LiesOver mA`.
  have hmAB_le_n : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ n := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, ← Ideal.mem_of_liesOver (P := n)
      (p := IsLocalRing.maximalIdeal A)]
    exact ha
  -- Helper: ker g = mA·B.
  have hkerg : RingHom.ker g =
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
    have hker_incR : RingHom.ker incR.toRingHom =
        (IsLocalRing.maximalIdeal A).map (algebraMap A B) := by
      ext b
      set h_eqv :=
        Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := A) B
          (IsLocalRing.maximalIdeal A) with hh_eqv_def
      have hmk : h_eqv (Ideal.Quotient.mk _ b) = 1 ⊗ₜ[A] b := rfl
      constructor
      · intro hb
        have hb' : (Algebra.TensorProduct.includeRight : B →ₐ[A] _) b = 0 := hb
        have h0 : (1 ⊗ₜ[A] b : (A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] B) = 0 := hb'
        rw [← hmk] at h0
        have hmk_zero : Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) b = 0 :=
          h_eqv.injective (by rw [h0, map_zero])
        exact (Ideal.Quotient.eq_zero_iff_mem).mp hmk_zero
      · intro hb
        have hmk_zero : Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) b = 0 :=
          (Ideal.Quotient.eq_zero_iff_mem).mpr hb
        have h0 : (1 ⊗ₜ[A] b : (A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] B) = 0 := by
          rw [← hmk, hmk_zero, map_zero]
        show (Algebra.TensorProduct.includeRight : B →ₐ[A] _) b = 0
        exact h0
    rw [hg_def, RingHom.ker_eq_comap_bot, ← Ideal.comap_comap]
    have hφ_bot : ((⊥ : Ideal (∀ i, kI i)).comap φ.toAlgHom.toRingHom) =
        (⊥ : Ideal (TensorProduct A (IsLocalRing.ResidueField A) B)) := by
      ext x
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      exact ⟨fun h => φ.injective (by rw [map_zero]; exact h),
        fun h => by rw [h, map_zero]⟩
    rw [hφ_bot, ← RingHom.ker_eq_comap_bot, hker_incR]
  -- Helper: maximal `M` of `B` above `mA` is `ker ((eval iM).comp g)` for some `iM`.
  have hMaxIdx : ∀ (M : Ideal B) [M.IsMaximal] [M.LiesOver (IsLocalRing.maximalIdeal A)],
      ∃ iM : I, M = RingHom.ker ((Pi.evalRingHom kI iM).comp g) := by
    intro M hM hM_over
    have hM_above : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ M := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, ← Ideal.mem_of_liesOver (P := M)
        (p := IsLocalRing.maximalIdeal A)]
      exact ha
    have hMN_prime : (Ideal.map g M).IsPrime :=
      Ideal.map_isPrime_of_surjective hg_surj (by rw [hkerg]; exact hM_above)
    obtain ⟨iM, qM, hqM⟩ :=
      PrimeSpectrum.exists_comap_evalRingHom_eq (R := kI)
        ⟨Ideal.map g M, hMN_prime⟩
    -- Since `kI iM` is a field, qM.asIdeal = ⊥.
    have hqM_bot : qM.asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top qM.asIdeal).resolve_right
        (fun h => qM.isPrime.ne_top h)
    -- From hqM: PrimeSpectrum.comap (eval iM) qM = ⟨Ideal.map g M, _⟩.
    have hqM_eq : qM.asIdeal.comap (Pi.evalRingHom kI iM) = Ideal.map g M :=
      congrArg PrimeSpectrum.asIdeal hqM
    rw [hqM_bot] at hqM_eq
    refine ⟨iM, ?_⟩
    -- Chain: M = comap g (map g M) = comap g (comap eval ⊥) = ker ((eval).comp g).
    have h_ker_eq :
        RingHom.ker ((Pi.evalRingHom kI iM).comp g) =
          Ideal.comap g (Ideal.comap (Pi.evalRingHom kI iM) ⊥) := by
      rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_comap]
    rw [h_ker_eq, hqM_eq, Ideal.comap_map_of_surjective _ hg_surj]
    refine (sup_eq_left.mpr ?_).symm
    rw [show (Ideal.comap g (⊥ : Ideal (∀ i, kI i)) : Ideal B) = RingHom.ker g
        from rfl, hkerg]
    exact hM_above
  -- Extract iₙ from the helper.
  obtain ⟨iₙ, hn_eq⟩ := hMaxIdx n
  refine ⟨iₙ, ?_⟩
  -- ===== Step 2: the residue idempotent ē := φ.symm (Pi.single iₙ 1) =====
  set ē : TensorProduct A (IsLocalRing.ResidueField A) B :=
    φ.symm (Pi.single iₙ (1 : kI iₙ)) with hē_def
  -- ē is idempotent in `k ⊗_A B`.
  have hē_idem : ē * ē = ē := by
    rw [hē_def]
    rw [show (φ.symm (Pi.single iₙ 1) : _) * φ.symm (Pi.single iₙ 1) =
          φ.symm (Pi.single iₙ 1 * Pi.single iₙ 1) from by
        rw [map_mul]]
    congr 1
    ext j
    by_cases hj : j = iₙ
    · subst hj; simp
    · simp [hj]
  -- ===== Step 3: lift ē to an idempotent e ∈ B with includeRight e = ē =====
  -- Substantive subclaim banked here: lifting an idempotent of `k ⊗_A B`
  -- to an idempotent of `B`. The structural route (chapter L138–L195) uses
  -- the henselian-pair structure on `(B, mA·B)` and Hensel's lemma applied
  -- to `X² - X`. Pending the full `HenselianRing B (mA·B)` infrastructure
  -- (gated on route-(D) closure of `is_henselian`), the lift is banked
  -- as a single sub-existential, then `Classical.choose`d. The sub-
  -- existential has the genuine intended content (residue match), so the
  -- final theorem's type signature retains its semantic content.
  have h_lift_exists :
      ∃ e : B, IsIdempotentElem e ∧
        (Algebra.TensorProduct.includeRight
            (R := A) (A := IsLocalRing.ResidueField A) (B := B) e) = ē := by
    -- iter-125 Lane 1: lift `ē` via the public companion
    -- `exists_completeOrthogonalIdempotents_lift_of_henselian`. The
    -- public lemma produces its own residue-decomposition `eqv'` and
    -- a lifted family `eLift : I' → B` with
    -- `incR (eLift j) = eqv'.symm (Pi.single j 1)`. Transport `ē` along
    -- `eqv'` and identify its support `S ⊆ I'`; in a finite product of
    -- fields, `eqv' ē` is the indicator of `S`, so summing `eLift` over
    -- `S` produces the desired idempotent.
    -- (The private same-namespace helper `lift_idempotent_henselianPair`
    -- specialised to the `B ↠ k ⊗_A B` map would be a more direct
    -- route, but it is module-scoped to `HenselianPair.lean`.)
    obtain ⟨I', _hI'fin, _hI'dec, kI', _hKfield', _hKalg', eqv', eLift,
        hCOI, hLift⟩ :=
      Algebra.Etale.exists_completeOrthogonalIdempotents_lift_of_henselian A B
    -- Components of `g := eqv' ē` are idempotents in fields, hence 0 or 1.
    set g : ∀ j, kI' j := eqv' ē with hg_def
    have hg_idem : g * g = g := by
      show eqv' ē * eqv' ē = eqv' ē
      rw [← map_mul, hē_idem]
    have hg_comp : ∀ j, g j = 0 ∨ g j = 1 := by
      intro j
      have hidem_j : IsIdempotentElem (g j) := by
        have := congr_fun hg_idem j
        exact this
      exact IsIdempotentElem.iff_eq_zero_or_one.mp hidem_j
    -- Support set `S` of `g`.
    set S : Finset I' :=
      (Finset.univ : Finset I').filter (fun j => g j = 1) with hS_def
    -- Reconstitute `g` as the sum of `Pi.single j 1` over `S`.
    have hg_support : g = ∑ j ∈ S, Pi.single j (1 : kI' j) := by
      ext j
      rw [Finset.sum_apply]
      by_cases hgj : g j = 1
      · have hjS : j ∈ S := by simp [hS_def, hgj]
        rw [Finset.sum_eq_single j _ (fun h => absurd hjS h)]
        · rw [Pi.single_eq_same, hgj]
        · intro b _ hbj
          exact Pi.single_eq_of_ne hbj.symm 1
      · have hgj0 : g j = 0 := (hg_comp j).resolve_right hgj
        rw [hgj0]
        refine (Finset.sum_eq_zero ?_).symm
        intro b hb
        have hbj : b ≠ j := fun h => by
          subst h
          simp [hS_def, hgj0] at hb
        exact Pi.single_eq_of_ne (M := kI') hbj.symm 1
    refine ⟨∑ j ∈ S, eLift j, ?_, ?_⟩
    · -- IsIdempotentElem: sum of orthogonal idempotents is idempotent.
      exact hCOI.toOrthogonalIdempotents.isIdempotentElem_sum
    · -- `incR (∑ eLift j) = ē` via `eqv'`'s injectivity and the
      -- `Pi.single`-support identification of `g = eqv' ē`.
      apply eqv'.injective
      simp only [map_sum]
      have hsum_eq : ∑ j ∈ S,
            eqv' ((Algebra.TensorProduct.includeRight
              (R := A) (A := IsLocalRing.ResidueField A) (B := B)) (eLift j)) =
          ∑ j ∈ S, Pi.single j (1 : kI' j) :=
        Finset.sum_congr rfl (fun j _ => hLift j)
      rw [hsum_eq, ← hg_support]
  obtain ⟨e, he_idem, he_match⟩ := h_lift_exists
  refine ⟨e, he_idem, he_match, ?_⟩
  -- ===== Step 4: spectral isolation =====
  -- For a maximal `m ⊂ B` above `mA`: `e ∉ m ↔ m = n`.
  -- We have `g e = φ (incR e) = φ (φ.symm (Pi.single iₙ 1)) = Pi.single iₙ 1`.
  -- For each `m` we have `m = ker ((eval iₘ).comp g)` via `hMaxIdx`. Then
  --   `e ∈ m ↔ (eval iₘ) (g e) = 0 ↔ (Pi.single iₙ 1) iₘ = 0 ↔ iₘ ≠ iₙ`,
  -- so `e ∉ m ↔ iₘ = iₙ`. For the residue match, `iₘ = iₙ → m = n` via the
  -- same kernel characterization. Conversely if `m = n` then `e ∉ m` from
  -- `(Pi.single iₙ 1) iₙ = 1 ≠ 0`.
  -- Compute g e (residue match transported through φ).
  have hge : g e = Pi.single iₙ (1 : kI iₙ) := by
    show φ.toAlgHom.toRingHom (incR.toRingHom e) = Pi.single iₙ 1
    show φ.toAlgHom (incR e) = Pi.single iₙ 1
    rw [he_match]
    exact φ.apply_symm_apply _
  intro m hm hm_over
  obtain ⟨iₘ, hm_eq⟩ := hMaxIdx m
  constructor
  · intro he_notin_m
    -- e ∉ m ↔ (eval iₘ)(g e) ≠ 0.
    have heval_ne : (Pi.evalRingHom kI iₘ) (g e) ≠ 0 := by
      intro h
      apply he_notin_m
      rw [hm_eq]
      exact h
    rw [hge] at heval_ne
    have hidx : iₘ = iₙ := by
      by_contra hne
      apply heval_ne
      show (Pi.single iₙ (1 : kI iₙ)) iₘ = 0
      exact Pi.single_eq_of_ne (M := kI) hne (1 : kI iₙ)
    rw [hm_eq, hidx, ← hn_eq]
  · intro hmn
    subst hmn
    intro he_in_n
    have hzero : (Pi.evalRingHom kI iₙ) (g e) = 0 := by
      rw [hn_eq] at he_in_n
      exact he_in_n
    rw [hge] at hzero
    have hzero' : (Pi.single iₙ (1 : kI iₙ)) iₙ = 0 := hzero
    rw [Pi.single_eq_same] at hzero'
    exact one_ne_zero hzero'

/-- **Step 1 of `localisation_finite_at_maximal`'s proof, packaged.**
Given a maximal `n ⊂ B` lying above the maximal of a local ring `A`,
and an idempotent `e ∈ B` with the spectral-isolation property
(`e ∉ m ↔ m = n` for every maximal `m` of `B` above `mA`), the
localisation `Localization.Away e` is a localisation of `B` at the
prime complement of `n`.

The key chain: since `B` is module-finite over `A` (hence integral),
every maximal of `B` lies above `mA`, so the spectral isolation
applies to every maximal of `B`. For `b ∉ n`, the ideal
`(b, 1 - e) ⊆ B` cannot be contained in any maximal (else that
maximal would not contain `e`, forcing it to equal `n` and hence
`b ∈ n`); so `b · c + (1 - e) · d = 1` for some `c, d ∈ B`.
Multiplying by `e` and using `e (1 - e) = 0` yields
`b · (e · c) = e`, i.e. `b ∣ e`. By
`IsLocalization.Away.algebraMap_isUnit_iff`, `b` is a unit in
`Localization.Away e`. Then `IsLocalization.of_le` upgrades the
`IsLocalization (Submonoid.powers e)` structure on
`Localization.Away e` to `IsLocalization n.primeCompl`. -/
private theorem localizationAway_isLocalizationAtPrime
    {A : Type*} [CommRing A] [IsLocalRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Module.Finite A B]
    (n : Ideal B) [n.IsMaximal] [n.LiesOver (IsLocalRing.maximalIdeal A)]
    (e : B) (he_idem : IsIdempotentElem e)
    (he_iso : ∀ (m : Ideal B) [m.IsMaximal]
        [m.LiesOver (IsLocalRing.maximalIdeal A)], (e ∉ m ↔ m = n)) :
    IsLocalization n.primeCompl (Localization.Away e) := by
  classical
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  -- Every maximal of `B` lies above the maximal of `A`.
  have hLiesOver : ∀ (m : Ideal B) [m.IsMaximal],
      m.LiesOver (IsLocalRing.maximalIdeal A) := by
    intro m _
    refine ⟨?_⟩
    have hmax : (Ideal.under A m).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    rw [Ideal.under_def]
    exact ((IsLocalRing.isMaximal_iff A).mp hmax).symm
  -- Spectral isolation at `n` gives `e ∉ n`.
  have he_notin_n : e ∉ n := (he_iso n).mpr rfl
  -- Powers of `e` are not in `n`.
  have hnPrime : n.IsPrime := Ideal.IsMaximal.isPrime ‹n.IsMaximal›
  have he_powers_le : Submonoid.powers e ≤ n.primeCompl := by
    rintro x ⟨k, rfl⟩
    rw [Ideal.mem_primeCompl_iff]
    exact fun hek_in => he_notin_n (hnPrime.mem_of_pow_mem k hek_in)
  -- `e * (1 - e) = 0` from idempotency.
  have he_sq : e * (1 - e) = 0 := by
    have hee : e * e = e := he_idem
    rw [mul_sub, mul_one, hee, sub_self]
  -- Upgrade `Submonoid.powers e ≤ n.primeCompl` to a full localisation.
  apply IsLocalization.of_le (Submonoid.powers e) n.primeCompl he_powers_le
  intro b hb
  rw [Ideal.mem_primeCompl_iff] at hb
  rw [IsLocalization.Away.algebraMap_isUnit_iff (x := e)]
  refine ⟨1, ?_⟩
  -- Goal: `b ∣ e ^ 1`. We show `b ∣ e`.
  rw [pow_one]
  -- Show `(b, 1 - e) = ⊤`.
  have hcoprime : (1 : B) ∈ Ideal.span ({b, 1 - e} : Set B) := by
    by_contra h1_notin
    have h_ne_top : Ideal.span ({b, 1 - e} : Set B) ≠ ⊤ := fun heq => by
      rw [heq] at h1_notin
      exact h1_notin trivial
    obtain ⟨m, hm_max, hm_ge⟩ := Ideal.exists_le_maximal _ h_ne_top
    haveI hm_max' : m.IsMaximal := hm_max
    haveI : m.LiesOver (IsLocalRing.maximalIdeal A) := hLiesOver m
    have hb_in : b ∈ m := hm_ge (Ideal.subset_span (by simp))
    have h1e_in : (1 - e) ∈ m := hm_ge (Ideal.subset_span (by simp))
    have he_notin_m : e ∉ m := by
      intro he_in_m
      apply hm_max'.ne_top
      rw [Ideal.eq_top_iff_one]
      have hsum : (1 : B) = e + (1 - e) := by ring
      rw [hsum]
      exact m.add_mem he_in_m h1e_in
    have hmn : m = n := (he_iso m).mp he_notin_m
    rw [hmn] at hb_in
    exact hb hb_in
  obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.mp hcoprime
  -- `b * (e * c) = e`, hence `b ∣ e`.
  refine ⟨e * c, ?_⟩
  linear_combination -e * hcd + d * he_sq

/-- **Finiteness of the localisation at a maximal** (Stacks 04GG,
at-the-fibre form).

For `A` Noetherian local Henselian, `B` module-finite étale over `A`,
and `n ⊂ B` a maximal above the maximal of `A`, the localisation
`B_n` is finite as an `A`-module.

Proof recipe (chapter Step 1 + Step 2): identify `B_n` with `B[1/e]`
for the isolating idempotent `e` from
`Algebra.Etale.exists_isolating_idempotent_at_maxIdeal`, then descend
finiteness from the special fibre
`k ⊗_A B[1/e] ≃ k_{i(n)}` (a single finite separable extension of
`k`) via the at-the-fibre version of Stacks 04GG. -/
theorem localisation_finite_at_maximal
    (A B : Type u) [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal] [n.LiesOver (IsLocalRing.maximalIdeal A)] :
    Module.Finite A (Localization.AtPrime n) := by
  classical
  -- Step 0: invoke the residue-product decomposition (declaration 1).
  obtain ⟨I, _hIfin, kI, _hKfield, _hKalg, φ, _hsep⟩ :=
    residue_product_decomposition A B
  haveI : Finite I := _hIfin
  haveI : Fintype I := Fintype.ofFinite I
  haveI : DecidableEq I := Classical.decEq I
  -- Step 1: invoke declaration 2 to obtain the isolating idempotent `e`.
  obtain ⟨_iₙ, e, he_idem, _he_match, he_iso⟩ :=
    exists_isolating_idempotent_at_maxIdeal A B n I kI φ
  -- Step 2 (chapter Step 1): identify `Localization.Away e` with
  -- `Localization.AtPrime n` over `A` via the iter-123 helper.
  haveI : IsLocalization n.primeCompl (Localization.Away e) :=
    localizationAway_isLocalizationAtPrime n e he_idem he_iso
  -- Build the `A`-algebra equivalence `Localization.Away e ≃ₐ[A] Localization.AtPrime n`
  -- and transport `Module.Finite A _` along it.
  let φ_eqv : Localization.Away e ≃ₐ[A] Localization.AtPrime n :=
    (IsLocalization.algEquiv n.primeCompl (Localization.Away e)
      (Localization.AtPrime n)).restrictScalars A
  -- Step 3: reduce to `Module.Finite A (Localization.Away e)` via the equivalence.
  suffices h : Module.Finite A (Localization.Away e) by
    exact Module.Finite.equiv φ_eqv.toLinearEquiv
  -- Step 4 (chapter Step 2 — Stacks 04GG at-the-fibre descent):
  -- `B[1/e]` is module-finite over `A` because
  --   (a) `B[1/e]` is finitely-presented flat over `A` (étale `A → B`
  --       composed with the localization-at-idempotent `B → B[1/e]`), and
  --   (b) the special fibre `ResidueField A ⊗[A] Localization.Away e`
  --       is finite-dimensional over `ResidueField A` — concretely it
  --       identifies with the `iₙ`-component `kI iₙ` of the residue-product
  --       decomposition via `_he_match` and the localization-at-idempotent
  --       computation `(∀ i, kI i)[1/ Pi.single iₙ 1] ≃ kI iₙ` from
  --       `Proetale/Mathlib/RingTheory/Localization/AtIdempotent.lean`.
  --
  -- iter-126 Lane 1: a much simpler closure than the chapter recipe. The
  -- isolating idempotent `e` becomes a unit (in fact `= 1`) inside
  -- `Localization.Away e`, hence `B → Localization.Away e` is **surjective**
  -- with kernel `Ideal.span {1 - e}` — this is the content of the Mathlib
  -- carrier `IsLocalization.Away.quotient_of_isIdempotentElem`. The
  -- quotient `B ⧸ Ideal.span {1 - e}` is module-finite over `A` (image of
  -- `B` under the A-linear surjective quotient map), and the algebra
  -- equivalence between two `IsLocalization.Away e` carriers transports
  -- `Module.Finite A` across. The chapter's Stacks 04GG descent route
  -- (FiniteResidue.lean) is unnecessary because we already have
  -- `Module.Finite A B`; the localization shrinks the module, not
  -- grows it.
  haveI : IsLocalization.Away (R := B) e (B ⧸ Ideal.span {1 - e}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem he_idem
  let aeqv : Localization.Away e ≃ₐ[B] B ⧸ Ideal.span {1 - e} :=
    IsLocalization.algEquiv (Submonoid.powers e) _ _
  haveI : Module.Finite A (B ⧸ Ideal.span ({1 - e} : Set B)) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ A (Ideal.span ({1 - e} : Set B))).toLinearMap
      Ideal.Quotient.mk_surjective
  exact Module.Finite.equiv (aeqv.restrictScalars A).symm.toLinearEquiv

/-- **Étaleness of the localisation at a maximal** (Stacks 04GG,
at-the-fibre form: étaleness half).

Under the same hypotheses as
`Algebra.Etale.localisation_finite_at_maximal`, the localisation
`B_n` is étale over `A`.

Proof recipe (chapter §"Étaleness preservation"): the identification
`B_n ≃ B[1/e]` from the isolating idempotent reduces étaleness to
the composition `A → B → B[1/e]`. The factor `B → B[1/e]` is étale
via `Algebra.Etale.of_isLocalizationAway`, and `B → B[1/e]` composed
with the étale `A → B` is étale by `Algebra.Etale.comp`. -/
theorem localisation_etale_at_maximal
    (A B : Type u) [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] [Algebra.Etale A B]
    (n : Ideal B) [n.IsMaximal] [n.LiesOver (IsLocalRing.maximalIdeal A)] :
    Algebra.Etale A (Localization.AtPrime n) := by
  classical
  -- Strategy (chapter §"Étaleness preservation"): the identification
  -- `B[1/e] ≃ B_n` (Step 1 of `localisation_finite_at_maximal`'s proof)
  -- reduces étaleness to the composite chain `A → B → B[1/e]`, where:
  --   * `A → B` is étale by hypothesis;
  --   * `B → B[1/e]` is `IsLocalization.Away e`, étale by
  --     `Algebra.Etale.of_isLocalizationAway`;
  --   * the composite is étale by `Algebra.Etale.comp`;
  --   * étaleness transfers across the `B[1/e] ≃ B_n` algebra
  --     isomorphism via `Algebra.Etale.of_equiv`.
  -- Steps:
  --   (1) Get the residue-product decomposition and the isolating
  --       idempotent `e` from declarations 1 and 2.
  --   (2) Apply `localizationAway_isLocalizationAtPrime` to obtain
  --       `IsLocalization n.primeCompl (Localization.Away e)`.
  --   (3) Both `Localization.Away e` and `Localization.AtPrime n` are
  --       localisations of `B` at `n.primeCompl`; build the `B`-algebra
  --       isomorphism via `IsLocalization.algEquiv`, then `restrictScalars`
  --       to get an `A`-algebra equivalence.
  --   (4) Étaleness of `A → Localization.Away e` follows from composition
  --       `A → B → Localization.Away e`. Transfer along the equivalence.
  obtain ⟨I, _hIfin, kI, _hKfield, _hKalg, φ, _hsep⟩ :=
    residue_product_decomposition A B
  haveI : Fintype I := Fintype.ofFinite I
  haveI : DecidableEq I := Classical.decEq I
  obtain ⟨_iₙ, e, he_idem, _he_match, he_iso⟩ :=
    exists_isolating_idempotent_at_maxIdeal A B n I kI φ
  haveI : IsLocalization n.primeCompl (Localization.Away e) :=
    localizationAway_isLocalizationAtPrime n e he_idem he_iso
  -- `Localization.Away e` is étale over `B`, hence over `A` by composition.
  haveI : Algebra.Etale B (Localization.Away e) :=
    Algebra.Etale.of_isLocalizationAway e
  haveI : Algebra.Etale A (Localization.Away e) :=
    Algebra.Etale.comp A B (Localization.Away e)
  -- Transfer along the `B`-algebra equivalence between two localisations
  -- at `n.primeCompl`, then restrict scalars to `A`.
  exact Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv n.primeCompl (Localization.Away e)
        (Localization.AtPrime n)).restrictScalars A)

end Algebra.Etale
