/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Nakayama
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Proetale.Algebra.RetractionsStrictlyHenselian

/-!
# Sections of étale algebras over local rings whose finite algebras split

Let `L` be a local ring with separably closed residue field satisfying the *splitting
hypothesis*: every module-finite `L`-algebra `T` decomposes as the product of its
localizations at maximal ideals, i.e. the canonical map `T → ∏_{𝔫} T_𝔫` is bijective.
This is Stacks 04GG, condition (10), as produced by
`IsLocalRing.finite_maximalSpectrum_and_bijective_pi_localization_of_forall_retraction`.

We prove Stacks 04GG, (10) ⇒ (8) (and hence (1) ⇒ (8)) via Zariski's main theorem:

* `IsLocalRing.bijective_algebraMap_localization_atPrime_of_etale`: for every étale
  `L`-algebra `B` and every prime `q` of `B` lying over the maximal ideal of `L`, the
  canonical map `L → B_q` is bijective.

## Outline

By Zariski's main theorem
(`Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`) there is a
module-finite subalgebra `S' ≤ B` and `r ∈ S'` with `r ∉ q` and `S'[1/r] = B[1/r]`. The
contraction `q'` of `q` to `S'` is maximal (integrality), so the splitting hypothesis makes
`S' → S'_{q'}` surjective (a product projection). Since inverting `r` identifies `S'` and
`B`, the induced map `S'_{q'} → B_q` is surjective as well, so `B_q` is a finite `L`-module.
As `L → B_q` is moreover formally unramified, essentially of finite type and local,
`𝔪_L B_q = 𝔪_{B_q}` and the residue extension is finite separable, hence trivial because
the residue field of `L` is separably closed; Nakayama then gives surjectivity of `L → B_q`.
For injectivity, `B_q` is finite flat over the local ring `L`, hence free, so the surjection
`L → B_q` splits and its kernel is annihilated by a unit.

## Consequences

* `IsLocalRing.exists_retraction_of_etale_of_ker_comp_eq`: every character `χ : B →+* Ω`
  into a field whose restriction to `L` has kernel `𝔪_L` is compatible with a retraction
  `σ : B →+* L` (Stacks 04GG (8), existence).
* `IsLocalRing.retraction_eq_of_comp_eq`: uniqueness of such retractions.
* `IsStrictlyHenselianLocalRing.of_forall_module_finite_bijective_pi`: `L` is strictly
  henselian.
* `module_finite_localization_atPrime_of_bijective_pi`: the localization of a ring
  splitting as the product of its localizations at maximal ideals is module-finite over it.
-/

universe u

open IsLocalRing TensorProduct

section Split

variable {S : Type u} [CommRing S]

/-- If a ring splits as the product of its localizations at maximal ideals, the localization
map at each maximal ideal is surjective (it is a product projection). -/
theorem surjective_algebraMap_localization_atPrime_of_bijective_pi
    (hpi : Function.Bijective (Pi.ringHom
      (fun n : MaximalSpectrum S => algebraMap S (Localization.AtPrime n.asIdeal))))
    (m : Ideal S) [m.IsMaximal] :
    Function.Surjective (algebraMap S (Localization.AtPrime m)) := by
  classical
  intro x
  obtain ⟨y, hy⟩ := hpi.2 (Pi.single (⟨m, ‹m.IsMaximal›⟩ : MaximalSpectrum S) x)
  refine ⟨y, ?_⟩
  have h1 := congrFun hy (⟨m, ‹m.IsMaximal›⟩ : MaximalSpectrum S)
  rwa [Pi.single_eq_same] at h1

/-- If a ring splits as the product of its localizations at maximal ideals, its localization
at each maximal ideal is a finite module over it. -/
theorem module_finite_localization_atPrime_of_bijective_pi
    (hpi : Function.Bijective (Pi.ringHom
      (fun n : MaximalSpectrum S => algebraMap S (Localization.AtPrime n.asIdeal))))
    (m : Ideal S) [m.IsMaximal] :
    Module.Finite S (Localization.AtPrime m) :=
  Module.Finite.of_surjective (Algebra.linearMap S (Localization.AtPrime m))
    (surjective_algebraMap_localization_atPrime_of_bijective_pi hpi m)

end Split

section QuasiFinite

/-- An étale algebra is quasi-finite: its fibers are étale over the residue fields, hence
finite as modules. -/
theorem Algebra.Etale.quasiFinite (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] : Algebra.QuasiFinite R A :=
  ⟨fun P _ => Algebra.FormallyUnramified.finite_of_free P.ResidueField (P.Fiber A)⟩

end QuasiFinite

namespace IsLocalRing

variable {L : Type u} [CommRing L] [IsLocalRing L]

/-- **Stacks 04GG, (10) ⇒ (8), key step**: let `L` be a local ring with separably closed
residue field such that every module-finite `L`-algebra splits as the product of its
localizations at maximal ideals. Then for every étale `L`-algebra `B` and every prime `q`
of `B` lying over the maximal ideal, the canonical map `L → B_q` is bijective. -/
theorem bijective_algebraMap_localization_atPrime_of_etale
    (hsplit : ∀ (T : Type u) [CommRing T] [Algebra L T], Module.Finite L T →
      Function.Bijective (Pi.ringHom
        (fun n : MaximalSpectrum T => algebraMap T (Localization.AtPrime n.asIdeal))))
    [IsSepClosed (ResidueField L)]
    (B : Type u) [CommRing B] [Algebra L B] (hB : Algebra.Etale L B)
    (q : Ideal B) [q.IsPrime] (hq : q.comap (algebraMap L B) = maximalIdeal L) :
    Function.Bijective (algebraMap L (Localization.AtPrime q)) := by
  classical
  haveI := hB
  haveI : Algebra.QuasiFinite L B := Algebra.Etale.quasiFinite L B
  -- Zariski's main theorem: a module-finite subalgebra `S'` with `S'[1/r] = B[1/r]`, `r ∉ q`
  obtain ⟨S', hS'fg, r, hrq, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := L) q
  haveI : Module.Finite L S' := ⟨(Submodule.fg_top _).mpr hS'fg⟩
  -- the contraction of `q` to `S'` is maximal
  haveI hq'prime : (q.comap (algebraMap S' B)).IsPrime := Ideal.IsPrime.comap _
  have hq'under : (q.comap (algebraMap S' B)).comap (algebraMap L S') = maximalIdeal L := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hq]
  haveI hq'max : (q.comap (algebraMap S' B)).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (q.comap (algebraMap S' B))
      (hq'under ▸ maximalIdeal.isMaximal L)
  -- the splitting hypothesis: `S' → S'_{q'}` is surjective
  have hs1 : Function.Surjective
      (algebraMap S' (Localization.AtPrime (q.comap (algebraMap S' B)))) :=
    surjective_algebraMap_localization_atPrime_of_bijective_pi (hsplit S' inferInstance) _
  -- the canonical map `ψ : S' → B_q` inverts the complement of `q'`
  set ψ : S' →+* Localization.AtPrime q :=
    (algebraMap B (Localization.AtPrime q)).comp (algebraMap S' B) with hψdef
  have hψu : ∀ y : (q.comap (algebraMap S' B)).primeCompl, IsUnit (ψ y) := by
    rintro ⟨y, hy⟩
    exact IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q)
      ⟨algebraMap S' B y, hy⟩
  -- `ψ` is surjective: combine surjectivity of `S' → S'_{q'}` with `S'[1/r] = B[1/r]`
  have hψsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨b, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
    have hAway : ∀ a : B, ∃ (c : S') (n : ℕ),
        algebraMap S' B c = algebraMap S' B r ^ n * a :=
      Localization.awayMap_surjective_iff.mp hbij.2
    obtain ⟨b', m, hb'⟩ := hAway b
    obtain ⟨s', k, hs'⟩ := hAway s
    have hsq : s ∉ q := hs
    have hrq' : algebraMap S' B r ∉ q := hrq
    -- the denominator `r ^ m * s'` avoids `q'`
    have hu : algebraMap S' B (r ^ m * s') ∉ q := by
      rw [map_mul, map_pow, hs']
      intro hmem
      rcases ‹q.IsPrime›.mem_or_mem hmem with h | h
      · exact hrq' (‹q.IsPrime›.mem_of_pow_mem _ h)
      · rcases ‹q.IsPrime›.mem_or_mem h with h' | h'
        · exact hrq' (‹q.IsPrime›.mem_of_pow_mem _ h')
        · exact hsq h'
    have hu' : r ^ m * s' ∈ (q.comap (algebraMap S' B)).primeCompl := hu
    obtain ⟨v, hv⟩ := hs1 (IsLocalization.mk'
      (Localization.AtPrime (q.comap (algebraMap S' B))) (b' * r ^ k) ⟨r ^ m * s', hu'⟩)
    refine ⟨v, ?_⟩
    have hunit : IsUnit (ψ (r ^ m * s')) := hψu ⟨r ^ m * s', hu'⟩
    refine hunit.mul_right_cancel ?_
    -- both sides multiplied with `ψ (r ^ m * s')` equal `algebraMap B B_q (⟦r⟧ ^ (m + k) * b)`
    have hL : ψ v * ψ (r ^ m * s') =
        algebraMap B (Localization.AtPrime q) (algebraMap S' B r ^ (m + k) * b) := by
      have h3 : algebraMap S' (Localization.AtPrime (q.comap (algebraMap S' B)))
          (v * (r ^ m * s')) =
          algebraMap S' (Localization.AtPrime (q.comap (algebraMap S' B))) (b' * r ^ k) := by
        rw [map_mul, hv]
        exact IsLocalization.mk'_spec _ (b' * r ^ k) ⟨r ^ m * s', hu'⟩
      have h4 := congrArg (IsLocalization.lift hψu) h3
      rw [IsLocalization.lift_eq, IsLocalization.lift_eq] at h4
      have h5 : ψ (b' * r ^ k) =
          algebraMap B (Localization.AtPrime q) (algebraMap S' B r ^ (m + k) * b) := by
        rw [hψdef, RingHom.comp_apply]
        congr 1
        rw [map_mul, map_pow, hb', pow_add]
        ring
      calc ψ v * ψ (r ^ m * s') = ψ (v * (r ^ m * s')) := (map_mul ψ v _).symm
        _ = ψ (b' * r ^ k) := h4
        _ = _ := h5
    have hR : IsLocalization.mk' (Localization.AtPrime q) b ⟨s, hs⟩ * ψ (r ^ m * s') =
        algebraMap B (Localization.AtPrime q) (algebraMap S' B r ^ (m + k) * b) := by
      have h6 : ψ (r ^ m * s') = algebraMap B (Localization.AtPrime q)
          (algebraMap S' B r ^ (m + k)) * algebraMap B (Localization.AtPrime q) s := by
        rw [hψdef, RingHom.comp_apply, ← map_mul]
        congr 1
        rw [map_mul, map_pow, hs', pow_add]
        ring
      rw [h6, map_mul, ← mul_assoc,
        mul_comm (IsLocalization.mk' (Localization.AtPrime q) b ⟨s, hs⟩), mul_assoc]
      congr 1
      exact IsLocalization.mk'_spec _ b ⟨s, hs⟩
    exact hL.trans hR.symm
  -- hence `B_q` is a finite `L`-module
  haveI hfinBq : Module.Finite L (Localization.AtPrime q) :=
    Module.Finite.of_surjective
      ((IsScalarTower.toAlgHom L B (Localization.AtPrime q)).comp S'.val).toLinearMap hψsurj
  -- `L → B_q` is a local homomorphism
  have hqBq : (maximalIdeal (Localization.AtPrime q)).comap
      (algebraMap B (Localization.AtPrime q)) = q :=
    Localization.AtPrime.under_maximalIdeal
  have hcomap : (maximalIdeal (Localization.AtPrime q)).comap
      (algebraMap L (Localization.AtPrime q)) = maximalIdeal L := by
    rw [IsScalarTower.algebraMap_eq L B (Localization.AtPrime q), ← Ideal.comap_comap,
      hqBq, hq]
  haveI : IsLocalHom (algebraMap L (Localization.AtPrime q)) :=
    ((local_hom_TFAE (algebraMap L (Localization.AtPrime q))).out 4 0).mp hcomap
  -- the maximal ideal of `B_q` is generated by `𝔪_L`, and the residue extension is trivial
  have hmax : (maximalIdeal L).map (algebraMap L (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hressurj : Function.Surjective
      (algebraMap (ResidueField L) (ResidueField (Localization.AtPrime q))) :=
    IsSepClosed.algebraMap_surjective _ _
  -- surjectivity of `L → B_q` via Nakayama
  have hsurj : Function.Surjective (algebraMap L (Localization.AtPrime q)) := by
    have hle : (⊤ : Submodule L (Localization.AtPrime q)) ≤
        LinearMap.range (Algebra.linearMap L (Localization.AtPrime q)) ⊔
          maximalIdeal L • ⊤ := by
      intro x _
      obtain ⟨y, hy⟩ := hressurj (residue _ x)
      obtain ⟨l, rfl⟩ := residue_surjective y
      have hy' : residue (Localization.AtPrime q)
          (algebraMap L (Localization.AtPrime q) l) = residue _ x :=
        (ResidueField.algebraMap_residue l).symm.trans hy
      have hmem : x - algebraMap L (Localization.AtPrime q) l ∈
          maximalIdeal (Localization.AtPrime q) := by
        rw [← residue_eq_zero_iff, map_sub, hy', sub_self]
      refine Submodule.mem_sup.mpr ⟨algebraMap L _ l, ⟨l, rfl⟩,
        x - algebraMap L _ l, ?_, by ring⟩
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, hmax]
      exact hmem
    have hrange := Submodule.le_of_le_smul_of_le_jacobson_bot
      (Module.finite_def.mp hfinBq) (maximalIdeal_le_jacobson ⊥) hle
    intro x
    obtain ⟨l, hl⟩ := hrange (Submodule.mem_top : x ∈ ⊤)
    exact ⟨l, hl⟩
  -- injectivity: `B_q` is finite flat, hence free, so the surjection splits
  refine ⟨?_, hsurj⟩
  haveI : Module.Flat L (Localization.AtPrime q) := inferInstance
  haveI : Module.Free L (Localization.AtPrime q) := Module.free_of_flat_of_isLocalRing
  obtain ⟨sec, hsec⟩ := Module.projective_lifting_property
    (Algebra.linearMap L (Localization.AtPrime q)) LinearMap.id hsurj
  have hc1 : algebraMap L (Localization.AtPrime q) (sec 1) = 1 := LinearMap.congr_fun hsec 1
  have hcunit : IsUnit (sec 1) := by
    rcases isUnit_or_isUnit_one_sub_self (sec 1) with h | h
    · exact h
    · exfalso
      have h1 : algebraMap L (Localization.AtPrime q) (1 - sec 1) = 0 := by
        rw [map_sub, map_one, hc1, sub_self]
      exact not_isUnit_zero (h1 ▸ h.map (algebraMap L (Localization.AtPrime q)))
  intro a b hab
  have h3 : ∀ l : L, sec (algebraMap L (Localization.AtPrime q) l) = l * sec 1 := fun l => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have h2 : a * sec 1 = b * sec 1 := by rw [← h3, ← h3, hab]
  exact hcunit.mul_right_cancel h2

/-- **Stacks 04GG (8), existence**: over a local ring `L` with separably closed residue
field whose module-finite algebras split, every character `χ : B →+* Ω` of an étale
`L`-algebra `B` into a field, whose restriction to `L` has kernel the maximal ideal,
factors through a retraction `σ : B →+* L`. -/
theorem exists_retraction_of_etale_of_ker_comp_eq
    (hsplit : ∀ (T : Type u) [CommRing T] [Algebra L T], Module.Finite L T →
      Function.Bijective (Pi.ringHom
        (fun n : MaximalSpectrum T => algebraMap T (Localization.AtPrime n.asIdeal))))
    [IsSepClosed (ResidueField L)]
    (B : Type u) [CommRing B] [Algebra L B] (hB : Algebra.Etale L B)
    {Ω : Type u} [Field Ω] (χ : B →+* Ω)
    (hker : RingHom.ker (χ.comp (algebraMap L B)) = maximalIdeal L) :
    ∃ σ : B →+* L, σ.comp (algebraMap L B) = RingHom.id L ∧
      (χ.comp (algebraMap L B)).comp σ = χ := by
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  have hq : (RingHom.ker χ).comap (algebraMap L B) = maximalIdeal L := by
    rw [RingHom.comap_ker, hker]
  have hbij := bijective_algebraMap_localization_atPrime_of_etale hsplit B hB
    (RingHom.ker χ) hq
  set e : L ≃+* Localization.AtPrime (RingHom.ker χ) :=
    RingEquiv.ofBijective (algebraMap L (Localization.AtPrime (RingHom.ker χ))) hbij
    with hedef
  have he_apply : ∀ l : L,
      e l = algebraMap L (Localization.AtPrime (RingHom.ker χ)) l := fun l => rfl
  -- `χ` factors through the localization at its kernel
  have hχu : ∀ y : (RingHom.ker χ).primeCompl, IsUnit (χ y) := by
    rintro ⟨y, hy⟩
    exact isUnit_iff_ne_zero.mpr fun h0 => hy (RingHom.mem_ker.mpr h0)
  have hfac : ∀ b : B,
      IsLocalization.lift hχu (algebraMap B (Localization.AtPrime (RingHom.ker χ)) b) =
        χ b := fun b => IsLocalization.lift_eq hχu b
  refine ⟨e.symm.toRingHom.comp (algebraMap B (Localization.AtPrime (RingHom.ker χ))),
    ?_, ?_⟩
  · ext l
    have h1 : algebraMap B (Localization.AtPrime (RingHom.ker χ)) (algebraMap L B l) =
        e l := by
      rw [he_apply, IsScalarTower.algebraMap_apply L B (Localization.AtPrime (RingHom.ker χ))]
    simp only [RingHom.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, h1]
    exact e.symm_apply_apply l
  · ext b
    have hLfac : ∀ l : L, IsLocalization.lift hχu (e l) = χ (algebraMap L B l) := fun l => by
      rw [he_apply,
        IsScalarTower.algebraMap_apply L B (Localization.AtPrime (RingHom.ker χ)), hfac]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← hLfac, e.apply_symm_apply, hfac]

/-- **Stacks 04GG (8), uniqueness**: the retraction compatible with a character `χ` as in
`IsLocalRing.exists_retraction_of_etale_of_ker_comp_eq` is unique. -/
theorem retraction_eq_of_comp_eq
    (hsplit : ∀ (T : Type u) [CommRing T] [Algebra L T], Module.Finite L T →
      Function.Bijective (Pi.ringHom
        (fun n : MaximalSpectrum T => algebraMap T (Localization.AtPrime n.asIdeal))))
    [IsSepClosed (ResidueField L)]
    (B : Type u) [CommRing B] [Algebra L B] (hB : Algebra.Etale L B)
    {Ω : Type u} [Field Ω] (χ : B →+* Ω)
    (hker : RingHom.ker (χ.comp (algebraMap L B)) = maximalIdeal L)
    {σ₁ σ₂ : B →+* L}
    (h₁ : σ₁.comp (algebraMap L B) = RingHom.id L)
    (h₂ : σ₂.comp (algebraMap L B) = RingHom.id L)
    (hc₁ : (χ.comp (algebraMap L B)).comp σ₁ = χ)
    (hc₂ : (χ.comp (algebraMap L B)).comp σ₂ = χ) :
    σ₁ = σ₂ := by
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  have hq : (RingHom.ker χ).comap (algebraMap L B) = maximalIdeal L := by
    rw [RingHom.comap_ker, hker]
  have hbij := bijective_algebraMap_localization_atPrime_of_etale hsplit B hB
    (RingHom.ker χ) hq
  set e : L ≃+* Localization.AtPrime (RingHom.ker χ) :=
    RingEquiv.ofBijective (algebraMap L (Localization.AtPrime (RingHom.ker χ))) hbij
    with hedef
  have he_apply : ∀ l : L,
      e l = algebraMap L (Localization.AtPrime (RingHom.ker χ)) l := fun l => rfl
  have key : ∀ σ : B →+* L, σ.comp (algebraMap L B) = RingHom.id L →
      (χ.comp (algebraMap L B)).comp σ = χ → ∀ b : B,
        σ b = e.symm (algebraMap B (Localization.AtPrime (RingHom.ker χ)) b) := by
    intro σ hσ hcσ b
    -- `σ` inverts the complement of `ker χ`
    have hσu : ∀ y : (RingHom.ker χ).primeCompl, IsUnit (σ y) := by
      rintro ⟨y, hy⟩
      by_contra hunit
      have hmem : σ y ∈ RingHom.ker (χ.comp (algebraMap L B)) :=
        hker.symm ▸ (mem_maximalIdeal _).mpr hunit
      have h0 : χ (algebraMap L B (σ y)) = 0 := hmem
      have hcy : χ (algebraMap L B (σ y)) = χ y := RingHom.congr_fun hcσ y
      exact hy (RingHom.mem_ker.mpr (hcy.symm.trans h0))
    have hfacσ : IsLocalization.lift hσu
        (algebraMap B (Localization.AtPrime (RingHom.ker χ)) b) = σ b :=
      IsLocalization.lift_eq hσu b
    have hσe : ∀ l : L, IsLocalization.lift hσu (e l) = l := fun l => by
      rw [he_apply,
        IsScalarTower.algebraMap_apply L B (Localization.AtPrime (RingHom.ker χ)),
        IsLocalization.lift_eq]
      exact RingHom.congr_fun hσ l
    rw [← hfacσ]
    conv_lhs => rw [← e.apply_symm_apply
      (algebraMap B (Localization.AtPrime (RingHom.ker χ)) b)]
    rw [hσe]
  ext b
  rw [key σ₁ h₁ hc₁ b, key σ₂ h₂ hc₂ b]

end IsLocalRing

/-- **Stacks 04GG, (10) ⇒ (1)/(2)**: a local ring with separably closed residue field whose
module-finite algebras split as products of their localizations at maximal ideals is
strictly henselian. -/
theorem IsStrictlyHenselianLocalRing.of_forall_module_finite_bijective_pi
    {L : Type u} [CommRing L] [IsLocalRing L]
    (hsplit : ∀ (T : Type u) [CommRing T] [Algebra L T], Module.Finite L T →
      Function.Bijective (Pi.ringHom
        (fun n : MaximalSpectrum T => algebraMap T (Localization.AtPrime n.asIdeal))))
    [IsSepClosed (IsLocalRing.ResidueField L)] :
    IsStrictlyHenselianLocalRing L := by
  have hsec : ∀ (B : Type u) [CommRing B] [Algebra L B], Algebra.Etale L B →
      Function.Surjective (PrimeSpectrum.comap (algebraMap L B)) →
      ∃ f : B →+* L, f.comp (algebraMap L B) = RingHom.id L := by
    intro B _ _ hB hsurj
    obtain ⟨Q, hQ⟩ := hsurj (IsLocalRing.closedPoint L)
    haveI := Q.isPrime
    have hker : RingHom.ker ((algebraMap B Q.asIdeal.ResidueField).comp (algebraMap L B)) =
        IsLocalRing.maximalIdeal L := by
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
      exact congrArg PrimeSpectrum.asIdeal hQ
    obtain ⟨σ, hσ, -⟩ := IsLocalRing.exists_retraction_of_etale_of_ker_comp_eq hsplit B hB
      (algebraMap B Q.asIdeal.ResidueField) hker
    exact ⟨σ, hσ⟩
  haveI h := IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction hsec
    (IsLocalRing.maximalIdeal L)
  have e : L ≃ₐ[L] Localization.AtPrime (IsLocalRing.maximalIdeal L) :=
    IsLocalization.atUnits L (IsLocalRing.maximalIdeal L).primeCompl
      (fun y (hy : y ∉ IsLocalRing.maximalIdeal L) => by
        by_contra hn
        exact hy ((IsLocalRing.mem_maximalIdeal y).mpr (mem_nonunits_iff.mpr hn)))
  exact .of_ringEquiv e.toRingEquiv.symm
