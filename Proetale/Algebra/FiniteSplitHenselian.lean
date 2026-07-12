/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Finite algebras over local rings with the étale section property split

Let `A` be a local ring such that every étale `A`-algebra `B` admitting a prime over the
maximal ideal of `A` has a retraction `B →+* A`. This is condition (1) of Stacks 04GG, in the
form produced by `AlgebraicGeometry.Scheme.Etale.exists_retraction_of_etale_of_exists_prime`.
We show that then every module-finite `A`-algebra `S` is a finite product of local rings
(Stacks 04GG, (1) ⇒ (10)): the maximal spectrum of `S` is finite and the canonical map
`S → ∏_{𝔪} S_𝔪` into the product of the localizations at the maximal ideals is bijective.

## Outline

1. Since `S` is integral over `A`, every maximal ideal of `S` lies over the maximal ideal `𝔪_A`
   (`IsLocalRing.comap_algebraMap_eq_maximalIdeal`). Since `S` is quasi-finite over `A`, there
   are only finitely many primes over `𝔪_A`, so `MaximalSpectrum S` is finite
   (`IsLocalRing.finite_maximalSpectrum_of_module_finite`).
2. For each maximal ideal `q` of `S` we produce an idempotent `ε ∉ q` contained in every other
   maximal ideal (`IsLocalRing.exists_isIdempotentElem_notMem_forall_mem_of_forall_retraction`).
   This is the heart of the argument: `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`
   (Stacks 00UJ) produces an étale `A`-algebra `R'`, a prime `P` over `𝔪_A` with trivial residue
   extension and an idempotent `e ∈ R' ⊗[A] S` such that there is a unique prime of `R' ⊗[A] S`
   over `P` avoiding `e`, and this prime contracts to `q` in `S`. After replacing `R'` by a
   localization `R'_g` in which `P` is the *only* prime over `𝔪_A` (prime avoidance), the
   retraction `ρ : R'_g →+* A` provided by the hypothesis necessarily satisfies
   `ρ⁻¹(𝔪_A) = P_g`. Pushing `e` forward along `r' ⊗ s ↦ algebraMap A S (ρ r') * s` yields the
   desired idempotent `ε = χ e`: for a maximal ideal `q''` of `S`, the prime `q''.comap χ` of
   `R' ⊗[A] S` lies over `P` and contracts to `q''` in `S`, so the uniqueness clause (together
   with injectivity of contraction on the fiber over `P`, which follows from the triviality of
   the residue extension `κ(P)/κ(𝔪_A)`) shows `ε ∈ q'' ↔ q'' ≠ q`.
3. The family `ε_q` is orthogonalized to a complete family of orthogonal idempotents
   (`MaximalSpectrum.exists_completeOrthogonalIdempotents`), using that an idempotent contained
   in every maximal ideal is zero.
4. `CompleteOrthogonalIdempotents.bijective_pi` gives `S ≅ ∏_q S ⧸ (1 - e_q)`, and each factor
   `S ⧸ (1 - e_q)` is the localization of `S` at `q`
   (`IsIdempotentElem.isLocalization_quotient_span_one_sub`).
-/

universe u

open TensorProduct IsLocalRing

section Idempotents

/-- If `x` is an idempotent of `S` which avoids the maximal ideal `m` but is contained in every
other maximal ideal, then `S ⧸ (1 - x)` is the localization of `S` at `m`. -/
theorem IsIdempotentElem.isLocalization_quotient_span_one_sub {S : Type*} [CommRing S] {x : S}
    (hx : IsIdempotentElem x) (m : MaximalSpectrum S) (hnot : x ∉ m.asIdeal)
    (hmem : ∀ M : Ideal S, M.IsMaximal → M ≠ m.asIdeal → x ∈ M) :
    IsLocalization m.asIdeal.primeCompl (S ⧸ Ideal.span {1 - x}) := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    have hy' : y ∉ m.asIdeal := hy
    rw [Ideal.Quotient.algebraMap_eq]
    by_contra hunit
    obtain ⟨M', hM', hle⟩ := Ideal.exists_le_maximal _
      (Ideal.span_singleton_eq_top.not.mpr hunit)
    have hyM : y ∈ M'.comap (Ideal.Quotient.mk (Ideal.span {1 - x})) :=
      Ideal.mem_comap.mpr (hle (Ideal.mem_span_singleton_self _))
    have hM : (M'.comap (Ideal.Quotient.mk (Ideal.span {1 - x}))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have hsub : (1 : S) - x ∈ M'.comap (Ideal.Quotient.mk (Ideal.span {1 - x})) := by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
      exact M'.zero_mem
    by_cases hMm : M'.comap (Ideal.Quotient.mk (Ideal.span {1 - x})) = m.asIdeal
    · exact hy' (hMm ▸ hyM)
    · have hxM := hmem _ hM hMm
      have h1 : (1 : S) ∈ M'.comap (Ideal.Quotient.mk (Ideal.span {1 - x})) := by
        have := (M'.comap (Ideal.Quotient.mk (Ideal.span {1 - x}))).add_mem hsub hxM
        rwa [show (1 : S) - x + x = 1 by ring] at this
      exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  · intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨(y, 1), by simp [Ideal.Quotient.algebraMap_eq]⟩
  · intro a b hab
    have hab' : a - b ∈ Ideal.span {1 - x} := by
      rwa [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq] at hab
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hab'
    refine ⟨⟨x, hnot⟩, ?_⟩
    have h0 : x * a - x * b = 0 := by
      rw [← mul_sub, hc, ← mul_assoc, hx.mul_one_sub_self, zero_mul]
    exact sub_eq_zero.mp h0

/-- A family of idempotents indexed by the maximal spectrum, where the idempotent at `m` avoids
`m` and lies in every other maximal ideal, can be orthogonalized to a complete family of
orthogonal idempotents with the same avoidance properties. -/
theorem MaximalSpectrum.exists_completeOrthogonalIdempotents
    {S : Type*} [CommRing S] [Fintype (MaximalSpectrum S)]
    (ε : MaximalSpectrum S → S) (hidem : ∀ m, IsIdempotentElem (ε m))
    (hnot : ∀ m, ε m ∉ m.asIdeal)
    (hmem : ∀ m m' : MaximalSpectrum S, m' ≠ m → ε m ∈ m'.asIdeal) :
    ∃ e : MaximalSpectrum S → S, CompleteOrthogonalIdempotents e ∧
      (∀ m, e m ∉ m.asIdeal) ∧
      ∀ m m' : MaximalSpectrum S, m' ≠ m → e m ∈ m'.asIdeal := by
  classical
  set e : MaximalSpectrum S → S :=
    fun m => ε m * ∏ m' ∈ Finset.univ.erase m, (1 - ε m') with he_def
  have hprod_idem : ∀ m : MaximalSpectrum S,
      IsIdempotentElem (∏ m' ∈ Finset.univ.erase m, (1 - ε m')) := fun m =>
    Finset.prod_induction _ _ (fun _ _ ha hb => ha.mul hb) IsIdempotentElem.one
      (fun m' _ => (hidem m').one_sub)
  have hidem' : ∀ m, IsIdempotentElem (e m) := fun m => (hidem m).mul (hprod_idem m)
  have hnot' : ∀ m, e m ∉ m.asIdeal := by
    intro m hm
    rcases m.isMaximal.isPrime.mem_or_mem hm with h | h
    · exact hnot m h
    · obtain ⟨m', hm', hmem'⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      have hεm' : ε m' ∈ m.asIdeal := hmem m' m (Finset.mem_erase.mp hm').1.symm
      have h1 : (1 : S) ∈ m.asIdeal := by
        have := m.asIdeal.add_mem hmem' hεm'
        rwa [show (1 : S) - ε m' + ε m' = 1 by ring] at this
      exact m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hmem2 : ∀ m m' : MaximalSpectrum S, m' ≠ m → e m ∈ m'.asIdeal := fun m m' h =>
    Ideal.mul_mem_right _ _ (hmem m m' h)
  have hortho : ∀ m n : MaximalSpectrum S, m ≠ n → e m * e n = 0 := by
    intro m n hmn
    have hn : n ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hmn.symm, Finset.mem_univ n⟩
    obtain ⟨X, hX⟩ : ∃ X, ∏ m' ∈ Finset.univ.erase m, (1 - ε m') = (1 - ε n) * X :=
      ⟨_, (Finset.mul_prod_erase _ _ hn).symm⟩
    have h0 : (1 - ε n) * ε n = 0 := (hidem n).one_sub_mul_self
    calc e m * e n
        = ε m * ((1 - ε n) * X) * (ε n * ∏ m' ∈ Finset.univ.erase n, (1 - ε m')) := by
          simp only [he_def]
          rw [hX]
      _ = ((1 - ε n) * ε n) * (ε m * X * ∏ m' ∈ Finset.univ.erase n, (1 - ε m')) := by ring
      _ = 0 := by rw [h0, zero_mul]
  have ho : OrthogonalIdempotents e := ⟨hidem', fun i j h => hortho i j h⟩
  -- membership of `1 - ∑ e m` in every maximal ideal
  have hsum : ∀ m₀ : MaximalSpectrum S, 1 - ∑ m, e m ∈ m₀.asIdeal := by
    intro m₀
    have h1 : 1 - e m₀ ∈ m₀.asIdeal := by
      have hne : Ideal.Quotient.mk m₀.asIdeal (e m₀) ≠ 0 := fun h =>
        hnot' m₀ (Ideal.Quotient.eq_zero_iff_mem.mp h)
      have hidq : IsIdempotentElem (Ideal.Quotient.mk m₀.asIdeal (e m₀)) :=
        (hidem' m₀).map _
      have hone : Ideal.Quotient.mk m₀.asIdeal (e m₀) = 1 :=
        (IsIdempotentElem.iff_eq_zero_or_one.mp hidq).resolve_left hne
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, hone, sub_self]
    have h2 : ∑ m ∈ Finset.univ.erase m₀, e m ∈ m₀.asIdeal :=
      Ideal.sum_mem _ fun m hm => hmem2 m m₀ (Finset.mem_erase.mp hm).1.symm
    have h3 : ∑ m, e m = e m₀ + ∑ m ∈ Finset.univ.erase m₀, e m :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ m₀)).symm
    have : 1 - ∑ m, e m = (1 - e m₀) - ∑ m ∈ Finset.univ.erase m₀, e m := by
      rw [h3]; ring
    rw [this]
    exact Ideal.sub_mem _ h1 h2
  -- the sum is a unit, hence `1` by idempotency
  have hu : IsUnit (∑ m, e m) := by
    by_contra hu
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_eq_top.not.mpr hu)
    have hsM : ∑ m, e m ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h1M : 1 - ∑ m, e m ∈ M := hsum ⟨M, hM⟩
    have h1 : (1 : S) ∈ M := by
      have := M.add_mem h1M hsM
      rwa [show (1 : S) - ∑ m, e m + ∑ m, e m = 1 by ring] at this
    exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hcomplete : ∑ m, e m = 1 := hu.mul_left_cancel (by
    rw [mul_one]
    exact ho.isIdempotentElem_sum)
  exact ⟨e, ⟨ho, hcomplete⟩, hnot', hmem2⟩

end Idempotents

section LocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Every maximal ideal of an integral algebra over a local ring lies over the maximal ideal. -/
theorem IsLocalRing.comap_algebraMap_eq_maximalIdeal (S : Type*) [CommRing S] [Algebra A S]
    [Algebra.IsIntegral A S] (q : Ideal S) [q.IsMaximal] :
    q.comap (algebraMap A S) = maximalIdeal A :=
  eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q)

/-- A module-finite algebra over a local ring has only finitely many maximal ideals. -/
theorem IsLocalRing.finite_maximalSpectrum_of_module_finite
    (S : Type*) [CommRing S] [Algebra A S] [Module.Finite A S] :
    Finite (MaximalSpectrum S) := by
  have h : ((maximalIdeal A).primesOver S).Finite :=
    Algebra.QuasiFinite.finite_primesOver (R := A) (maximalIdeal A)
  haveI := h.to_subtype
  refine Finite.of_injective (fun m : MaximalSpectrum S =>
    (⟨m.asIdeal, inferInstance,
      ⟨(comap_algebraMap_eq_maximalIdeal S m.asIdeal).symm⟩⟩ :
      (maximalIdeal A).primesOver S)) ?_
  intro m₁ m₂ h12
  exact MaximalSpectrum.ext (congrArg Subtype.val h12)

/-- Key step for Stacks 04GG, (1) ⇒ (10): if every étale `A`-algebra with a prime over the
maximal ideal admits a retraction, then for every maximal ideal `q` of a module-finite
`A`-algebra `S` there is an idempotent `ε ∉ q` lying in every other maximal ideal of `S`. -/
theorem IsLocalRing.exists_isIdempotentElem_notMem_forall_mem_of_forall_retraction
    (hsec : ∀ (B : Type u) [CommRing B] [Algebra A B], Algebra.Etale A B →
      (∃ q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) →
      ∃ f : B →+* A, f.comp (algebraMap A B) = RingHom.id A)
    (S : Type u) [CommRing S] [Algebra A S] [Module.Finite A S]
    (q : Ideal S) [q.IsMaximal] :
    ∃ ε : S, IsIdempotentElem ε ∧ ε ∉ q ∧
      ∀ q' : Ideal S, q'.IsMaximal → q' ≠ q → ε ∈ q' := by
  classical
  haveI : q.LiesOver (maximalIdeal A) := ⟨(comap_algebraMap_eq_maximalIdeal S q).symm⟩
  obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hres, -, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (R := A) (S := S)
      (maximalIdeal A) q
  -- Step 1: isolate `P` among the (finitely many) primes of `R'` over the maximal ideal.
  obtain ⟨g, hgP, hg⟩ :=
    Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver (maximalIdeal A) P
  set Rg := Localization.Away g with hRgdef
  haveI : Algebra.Etale R' Rg := Algebra.Etale.of_isLocalizationAway g
  haveI : Algebra.Etale A Rg := Algebra.Etale.comp A R' Rg
  have hdisj : Disjoint (Submonoid.powers g : Set R') (P : Set R') :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hgP
  set Pg : Ideal Rg := P.map (algebraMap R' Rg) with hPgdef
  haveI hPg_prime : Pg.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Rg P ‹_› hdisj
  have hPg_under : Pg.comap (algebraMap R' Rg) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Rg ‹_› hdisj
  have halg : algebraMap A Rg = (algebraMap R' Rg).comp (algebraMap A R') :=
    IsScalarTower.algebraMap_eq A R' Rg
  have hP_under : P.comap (algebraMap A R') = maximalIdeal A := (P.over_def _).symm
  have hPg_over : Pg.comap (algebraMap A Rg) = maximalIdeal A := by
    rw [halg, ← Ideal.comap_comap, hPg_under, hP_under]
  -- `Pg` is the unique prime of `Rg` over the maximal ideal.
  have huniqg : ∀ Q : Ideal Rg, Q.IsPrime → Q.comap (algebraMap A Rg) = maximalIdeal A →
      Q = Pg := by
    intro Q hQ hQm
    have hp_prime : (Q.comap (algebraMap R' Rg)).IsPrime := hQ.comap _
    have hp_over : (Q.comap (algebraMap R' Rg)).comap (algebraMap A R') = maximalIdeal A := by
      rw [Ideal.comap_comap, ← halg, hQm]
    have hgp : g ∉ Q.comap (algebraMap R' Rg) := fun hmem =>
      hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.Away.algebraMap_isUnit g))
    have hpq : Q.comap (algebraMap R' Rg) = P := by
      by_contra hne
      exact hgp (hg _ hp_prime hne ⟨hp_over.symm⟩)
    conv_lhs => rw [← IsLocalization.map_under (Submonoid.powers g) Rg Q]
    rw [show Q.under R' = P from hpq, hPgdef]
  -- Step 2: apply the retraction hypothesis.
  obtain ⟨ρ, hρ⟩ := hsec Rg ‹Algebra.Etale A Rg› ⟨Pg, hPg_prime, hPg_over⟩
  have hρ_apply : ∀ a : A, ρ (algebraMap A Rg a) = a := fun a => RingHom.congr_fun hρ a
  have hpρ : (maximalIdeal A).comap ρ = Pg := by
    refine huniqg _ (Ideal.IsPrime.comap ρ) ?_
    rw [Ideal.comap_comap, hρ, Ideal.comap_id]
  -- Step 3: push the idempotent forward along `r' ⊗ s ↦ algebraMap A S (ρ r') * s`.
  set ρA : Rg →ₐ[A] A :=
    { toRingHom := ρ, commutes' := fun a => by simpa using hρ_apply a } with hρAdef
  have hρA_apply : ∀ y : Rg, ρA y = ρ y := fun _ => rfl
  set χ : R' ⊗[A] S →ₐ[A] S :=
    (Algebra.TensorProduct.lift ((Algebra.ofId A S).comp ρA) (AlgHom.id A S)
      fun _ _ => Commute.all _ _).comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A R' Rg) (AlgHom.id A S)) with hχdef
  have hχ_tmul : ∀ (r : R') (s : S),
      χ (r ⊗ₜ[A] s) = algebraMap A S (ρ (algebraMap R' Rg r)) * s := by
    intro r s
    simp [hχdef, hρA_apply, Algebra.ofId_apply]
  have hχ_right : χ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
      = RingHom.id S := by
    ext s
    simpa using hχ_tmul 1 s
  have hχ_left : χ.toRingHom.comp (algebraMap R' (R' ⊗[A] S)) =
      ((algebraMap A S).comp ρ).comp (algebraMap R' Rg) := by
    ext r
    simpa [Algebra.TensorProduct.algebraMap_apply] using hχ_tmul r 1
  -- Step 4: for a maximal ideal `q''` of `S`, the prime `q''.comap χ` lies over `P`.
  have hunder : ∀ q'' : Ideal S, q''.IsMaximal →
      (q''.comap χ.toRingHom).comap (algebraMap R' (R' ⊗[A] S)) = P := by
    intro q'' hq''
    haveI := hq''
    calc (q''.comap χ.toRingHom).comap (algebraMap R' (R' ⊗[A] S))
        = q''.comap (χ.toRingHom.comp (algebraMap R' (R' ⊗[A] S))) := Ideal.comap_comap _ _
      _ = q''.comap (((algebraMap A S).comp ρ).comp (algebraMap R' Rg)) := by rw [hχ_left]
      _ = ((q''.comap (algebraMap A S)).comap ρ).comap (algebraMap R' Rg) := by
          simp only [Ideal.comap_comap]
      _ = P := by rw [comap_algebraMap_eq_maximalIdeal S q'', hpρ, hPg_under]
  -- Step 5: conclude using the uniqueness clause and residue field triviality.
  refine ⟨χ e, he.map χ, ?_, ?_⟩
  · haveI hQprime : (q.comap χ.toRingHom).IsPrime := Ideal.IsPrime.comap _
    haveI hQlies : (q.comap χ.toRingHom).LiesOver P := ⟨(hunder q ‹_›).symm⟩
    have hQ : q.comap χ.toRingHom = P' :=
      Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hres _ _ (by
        rw [Ideal.comap_comap, hχ_right, Ideal.comap_id, hP'q])
    intro hmem
    exact heP' (hQ ▸ Ideal.mem_comap.mpr hmem)
  · intro q' hq' hne
    haveI := hq'
    by_contra hmem
    haveI : (q'.comap χ.toRingHom).IsPrime := Ideal.IsPrime.comap _
    have h2 : q'.comap χ.toRingHom = P' :=
      huniq _ inferInstance ⟨(hunder q' hq').symm⟩ fun h => hmem (Ideal.mem_comap.mp h)
    have : q' = P'.comap Algebra.TensorProduct.includeRight.toRingHom := by
      rw [← h2, Ideal.comap_comap, hχ_right, Ideal.comap_id]
    exact hne (this.trans hP'q)

/-- **Stacks 04GG, (1) ⇒ (10)**: if every étale `A`-algebra with a prime over the maximal
ideal admits a retraction (which holds e.g. by
`AlgebraicGeometry.Scheme.Etale.exists_retraction_of_etale_of_exists_prime`), then every
module-finite `A`-algebra `S` has finitely many maximal ideals and the canonical map
`S → ∏_{𝔪} S_𝔪` into the product of the localizations at the maximal ideals is bijective,
i.e. `S` is a finite product of local rings. -/
theorem IsLocalRing.finite_maximalSpectrum_and_bijective_pi_localization_of_forall_retraction
    (hsec : ∀ (B : Type u) [CommRing B] [Algebra A B], Algebra.Etale A B →
      (∃ q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = IsLocalRing.maximalIdeal A) →
      ∃ f : B →+* A, f.comp (algebraMap A B) = RingHom.id A)
    (S : Type u) [CommRing S] [Algebra A S] [Module.Finite A S] :
    Finite (MaximalSpectrum S) ∧
    Function.Bijective (Pi.ringHom
      (fun m : MaximalSpectrum S => algebraMap S (Localization.AtPrime m.asIdeal))) := by
  classical
  have hfin : Finite (MaximalSpectrum S) := finite_maximalSpectrum_of_module_finite (A := A) S
  refine ⟨hfin, ?_⟩
  haveI : Fintype (MaximalSpectrum S) := Fintype.ofFinite _
  choose ε hidem hnot hmem using fun m : MaximalSpectrum S =>
    exists_isIdempotentElem_notMem_forall_mem_of_forall_retraction hsec S m.asIdeal
  obtain ⟨e, hco, hnot', hmem'⟩ :=
    MaximalSpectrum.exists_completeOrthogonalIdempotents ε hidem hnot
      fun m m' h => hmem m m'.asIdeal m'.isMaximal fun hh => h (MaximalSpectrum.ext hh)
  have hloc : ∀ m : MaximalSpectrum S,
      IsLocalization m.asIdeal.primeCompl (S ⧸ Ideal.span {1 - e m}) := fun m =>
    (hco.idem m).isLocalization_quotient_span_one_sub m (hnot' m)
      fun M hM hne => hmem' m ⟨M, hM⟩ fun h => hne (congrArg MaximalSpectrum.asIdeal h)
  have E : ∀ m : MaximalSpectrum S,
      (S ⧸ Ideal.span {1 - e m}) ≃ₐ[S] Localization.AtPrime m.asIdeal := fun m =>
    haveI := hloc m
    IsLocalization.algEquiv m.asIdeal.primeCompl _ _
  have hE : ∀ (m : MaximalSpectrum S) (x : S),
      E m (Ideal.Quotient.mk (Ideal.span {1 - e m}) x) =
        algebraMap S (Localization.AtPrime m.asIdeal) x := fun m x => by
    rw [← Ideal.Quotient.algebraMap_eq]
    exact (E m).commutes x
  have key : ⇑(Pi.ringHom fun m : MaximalSpectrum S =>
        algebraMap S (Localization.AtPrime m.asIdeal)) =
      (fun v (m : MaximalSpectrum S) => E m (v m)) ∘
        ⇑(Pi.ringHom fun m : MaximalSpectrum S =>
          Ideal.Quotient.mk (Ideal.span {1 - e m})) := by
    funext x
    funext m
    exact (hE m x).symm
  rw [key]
  refine Function.Bijective.comp ⟨fun v w h => ?_, fun v => ?_⟩ hco.bijective_pi
  · funext m
    exact (E m).injective (congrFun h m)
  · exact ⟨fun m => (E m).symm (v m), funext fun m => (E m).apply_symm_apply (v m)⟩

end LocalRing
