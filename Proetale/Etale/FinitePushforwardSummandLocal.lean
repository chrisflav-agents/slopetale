/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.FinitePushforwardSummandSystem
import Proetale.Etale.FiberSectionsHenselian

/-!
# Local structure of the summand sections and the equalizing condition

This file continues stage C of the program towards the stalk formula for pushforwards
along finite morphisms (blueprint `lemma:pbc-finite`), building on
`Proetale.Etale.FinitePushforwardSummandSystem` and
`Proetale.Etale.FiberSectionsHenselian`.

Let `f : Y ⟶ X` be a finite morphism of schemes, `x : Spec Ω ⟶ X` a geometric point,
`p₁` a splitting stage carrying a complete orthogonal family of idempotents `es`, `i` a
distinguished index and `y : Spec Ω' ⟶ Y` a geometric point over `x` with compatible
character `χ` of the fiber sections. Write `Λ` for the summand sections colimit
`AlgebraicGeometry.Scheme.Etale.summandSections` and `m` for the maximal ideal of the
fiber sections cut out by `χ`, assumed to be the unique maximal ideal avoiding the
distinguished idempotent.

## The summand sections as a strictly henselian localization

- `AlgebraicGeometry.Scheme.Etale.isLocalization_atPrime_summandSections`: `Λ` is the
  localization of the fiber sections at `m`: it is the localization away from the
  distinguished idempotent `e`, which agrees with the quotient by the complementary
  idempotent `1 - e`, which in turn is the localization at `m` by
  `IsIdempotentElem.isLocalization_quotient_span_one_sub`.
- `AlgebraicGeometry.Scheme.Etale.localizationAtPrimeToSummandSections`: the resulting
  identification `Localization.AtPrime m ≃ₐ Λ`, and the bridge
  `summandSectionsToStrictLocalization_localizationAtPrimeToSummandSections`
  identifying the germ comparison of the summand sections with the comparison map
  `AlgebraicGeometry.Scheme.Etale.localizationAtPrimeToStrictLocalization` of
  `Proetale.Etale.FinitePushforwardStalkCofinal`.
- `AlgebraicGeometry.Scheme.Etale.isLocalRing_summandSections`,
  `AlgebraicGeometry.Scheme.Etale.isStrictlyHenselianLocalRing_summandSections`,
  `AlgebraicGeometry.Scheme.Etale.forall_module_finite_bijective_pi_summandSections`,
  `AlgebraicGeometry.Scheme.Etale.isSepClosed_residueField_summandSections`: transfers
  of the local structure of the fiber localization of
  `Proetale.Etale.FiberSectionsHenselian` along this identification, and
  `AlgebraicGeometry.Scheme.Etale.exists_retraction_of_etale_summandSections`, the
  resulting retraction property for étale `Λ`-algebras (Stacks 04GG (8) for `Λ`).

## Evaluation and the equalizing condition

- `AlgebraicGeometry.Scheme.Etale.summandSectionsEval` /
  `AlgebraicGeometry.Scheme.Etale.ker_summandSectionsEval`: the evaluation character of
  the summand sections at the lifted geometric point cuts out the maximal ideal, and
  `AlgebraicGeometry.Scheme.Etale.isUnit_toSummandSections_iff_eval_ne_zero` detects
  invertibility of germs by non-vanishing at the point.
- `AlgebraicGeometry.Scheme.Etale.exists_summandFunctor_map_comp_eq`: **the equalizing
  half of the cofinality of the summand system**: two morphisms from a summand to an
  étale neighbourhood of `y` agree after passing to a finer stage. Two such morphisms
  agree on the open agreement locus (the diagonal of an étale morphism is an open
  immersion); the lifted geometric point lies in the agreement locus, which therefore
  contains a basic open whose section does not vanish at the point, is hence invertible
  in the colimit and so already invertible at a finer stage — over which the summand is
  contained in the agreement locus.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

/-!
### The quotient by the complementary idempotent as a localization

For an idempotent `e` of a commutative ring `R`, the quotient `R ⧸ (1 - e)` is the
localization of `R` away from `e`: the image of `e` is `1`, the quotient map is
surjective and its kernel is annihilated by `e`.
-/

section AwayIdempotentQuotient

variable {R : Type u} [CommRing R]

private lemma algebraMap_quotient_span_one_sub (e : R) :
    algebraMap R (R ⧸ Ideal.span {1 - e}) e = 1 := by
  have h0 : Ideal.Quotient.mk (Ideal.span {1 - e}) (1 - e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have h1 : (1 : R ⧸ Ideal.span {1 - e}) -
      Ideal.Quotient.mk (Ideal.span {1 - e}) e = 0 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - e})), ← map_sub]
    exact h0
  rw [Ideal.Quotient.algebraMap_eq]
  exact (sub_eq_zero.mp h1).symm

private lemma isLocalization_away_quotient_span_one_sub {e : R}
    (he : IsIdempotentElem e) :
    IsLocalization.Away e (R ⧸ Ideal.span {1 - e}) := by
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hs1 : algebraMap R (R ⧸ Ideal.span {1 - e}) (s : R) = 1 := by
      rw [← hn, map_pow, algebraMap_quotient_span_one_sub e, one_pow]
    rw [hs1]
    exact isUnit_one
  · intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨(a, 1), by simp [Ideal.Quotient.algebraMap_eq]⟩
  · intro a b hab
    have hab' : a - b ∈ Ideal.span {1 - e} := by
      rw [Ideal.Quotient.algebraMap_eq] at hab
      exact Ideal.Quotient.eq.mp hab
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hab'
    refine ⟨⟨e, Submonoid.mem_powers e⟩, ?_⟩
    change e * a = e * b
    rw [← sub_eq_zero, ← mul_sub, hc, ← mul_assoc, he.mul_one_sub_self, zero_mul]

end AwayIdempotentQuotient

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X) (p₁ : (geometricPoint x).fiber.Elements)
  {ι : Type u} (es : ι → Γ(((Over.pullback @Etale ⊤ f).obj p₁.1).left, ⊤)) (i : ι)
  {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
  (σ : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))
  (y : Spec (CommRingCat.of Ω') ⟶ Y) (hy : y ≫ f = σ ≫ x)
  (χ : fiberSections f x →+* Ω')
  (heval : fiberSectionsToStrictLocalization f x σ y hy ≫ strictLocalizationEval y =
    CommRingCat.ofHom χ)
  (hi : χ ((toFiberSections f x p₁).hom (es i)) ≠ 0)

/-!
### The evaluation character of the summand sections
-/

/-- **The evaluation character of the summand sections**: evaluation of germs of
summand sections at the lifted geometric point of `y`, as a ring homomorphism to
`Ω'`. -/
noncomputable def summandSectionsEval :
    summandSections f x p₁ es i σ y hy χ heval hi →+* Ω' :=
  ((strictLocalizationEval y).hom).comp
    (summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi).hom

/-- The evaluation character of the summand sections restricts to the character `χ` on
the fiber sections. -/
theorem summandSectionsEval_algebraMap (z : fiberSections f x) :
    summandSectionsEval f x p₁ es i σ y hy χ heval hi
        (algebraMap (fiberSections f x)
          (summandSections f x p₁ es i σ y hy χ heval hi) z) = χ z := by
  have h1 := congrArg (fun t => CommRingCat.Hom.hom t z)
    (fiberSectionsToSummandSections_summandSectionsToStrictLocalization f x p₁ es i σ y
      hy χ heval hi)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  have h2 := fiberSectionsToStrictLocalization_eval_apply f x σ y hy χ heval z
  exact (congrArg (strictLocalizationEval y).hom h1).trans h2

/-!
### The agreement locus of two morphisms to an étale scheme

Two morphisms `φ, φ' : W ⟶ V` over `S` with `V ⟶ S` unramified of finite type agree on
an open subscheme of `W`, the pullback of the diagonal along `(φ, φ')`. If a morphism
`T ⟶ W` equalizes `φ` and `φ'`, it factors through the agreement locus, so for affine
`W` there is a basic open of `W` around any of its points on which `φ` and `φ'` agree.
-/

/-- If two morphisms `φ, φ' : W ⟶ V` to an étale (unramified, finite type) `S`-scheme
`V` are equalized by a morphism `pt : T ⟶ W`, then there is a basic open of the affine
scheme `W` containing the image of `pt` on which `φ` and `φ'` agree: any morphism
pulling back the corresponding section to a unit equalizes `φ` and `φ'`. -/
private lemma exists_mem_basicOpen_forall_comp_eq {W V S : Scheme.{u}} [IsAffine W]
    (h : V ⟶ S) [FormallyUnramified h] [LocallyOfFiniteType h]
    (φ φ' : W ⟶ V) (hw : φ ≫ h = φ' ≫ h)
    {T : Scheme.{u}} (pt : T ⟶ W) (hpt : pt ≫ φ = pt ≫ φ') (t₀ : T) :
    ∃ b : Γ(W, ⊤), pt.base t₀ ∈ W.basicOpen b ∧
      ∀ {W' : Scheme.{u}} (ρ : W' ⟶ W), IsUnit ((ρ.appTop).hom b) →
        ρ ≫ φ = ρ ≫ φ' := by
  haveI : IsOpenImmersion (pullback.diagonal h) := inferInstance
  -- the pair map to the self-fiber product and the agreement locus
  set q : W ⟶ pullback h h := pullback.lift φ φ' hw with hqdef
  have hqfst : q ≫ pullback.fst h h = φ := pullback.lift_fst _ _ _
  have hqsnd : q ≫ pullback.snd h h = φ' := pullback.lift_snd _ _ _
  set ιZ : pullback (pullback.diagonal h) q ⟶ W :=
    pullback.snd (pullback.diagonal h) q with hιZdef
  haveI : IsOpenImmersion ιZ :=
    inferInstanceAs (IsOpenImmersion (pullback.snd (pullback.diagonal h) q))
  have hcond : pullback.fst (pullback.diagonal h) q ≫ pullback.diagonal h = ιZ ≫ q :=
    pullback.condition
  -- the equalizing morphism lifts to the agreement locus
  have hlift : (pt ≫ φ) ≫ pullback.diagonal h = pt ≫ q := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [pullback.diagonal_fst, Category.comp_id, hqfst]
    · simp only [Category.assoc]
      rw [pullback.diagonal_snd, Category.comp_id, hqsnd]
      exact hpt
  set z₀ : T ⟶ pullback (pullback.diagonal h) q := pullback.lift (pt ≫ φ) pt hlift
    with hz₀def
  have hz₀ : z₀ ≫ ιZ = pt := pullback.lift_snd _ _ _
  -- a basic open around the point inside the open agreement locus
  have hmem : pt.base t₀ ∈ ιZ.opensRange := by
    refine ⟨z₀.base t₀, ?_⟩
    exact congrArg (fun v : T ⟶ W => v.base t₀) hz₀
  obtain ⟨b, hble, hbmem⟩ :=
    (isAffineOpen_top W).exists_basicOpen_le ⟨pt.base t₀, hmem⟩ trivial
  refine ⟨b, hbmem, ?_⟩
  intro W' ρ hρ
  -- a morphism inverting `b` factors through the basic open, hence the agreement locus
  have hpre : ρ ⁻¹ᵁ W.basicOpen b = W'.basicOpen ((ρ.appTop).hom b) :=
    ρ.preimage_basicOpen_top b
  have htop : W'.basicOpen ((ρ.appTop).hom b) = ⊤ :=
    RingedSpace.basicOpen_of_isUnit _ hρ
  have hrange : Set.range ρ.base ⊆ Set.range ιZ.base := by
    rintro - ⟨w', rfl⟩
    have h1 : w' ∈ ρ ⁻¹ᵁ W.basicOpen b := by
      rw [hpre, htop]
      trivial
    have h2 : ρ.base w' ∈ W.basicOpen b := h1
    exact hble h2
  set ℓ : W' ⟶ pullback (pullback.diagonal h) q := IsOpenImmersion.lift ιZ ρ hrange
    with hℓdef
  have hfac : ℓ ≫ ιZ = ρ := IsOpenImmersion.lift_fac _ _ hrange
  -- on the agreement locus, the two morphisms agree
  have hs : ρ ≫ φ = ℓ ≫ pullback.fst (pullback.diagonal h) q := by
    rw [← hfac, ← hqfst, Category.assoc, ← Category.assoc ιZ q (pullback.fst h h),
      ← hcond, Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have hs' : ρ ≫ φ' = ℓ ≫ pullback.fst (pullback.diagonal h) q := by
    rw [← hfac, ← hqsnd, Category.assoc, ← Category.assoc ιZ q (pullback.snd h h),
      ← hcond, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  rw [hs, hs']

section Local

variable [IsFinite f] [Fintype ι]
  (m : MaximalSpectrum (fiberSections f x))
  (hker : RingHom.ker χ = m.asIdeal)
  (hnot : (toFiberSections f x p₁).hom (es i) ∉ m.asIdeal)
  (hmem : ∀ m' : MaximalSpectrum (fiberSections f x), m' ≠ m →
    (toFiberSections f x p₁).hom (es i) ∈ m'.asIdeal)

/-!
### The summand sections as the localization at the maximal ideal
-/

include hnot hmem in
/-- **The summand sections are the localization of the fiber sections at `m`**: for the
maximal ideal `m` avoiding the distinguished idempotent `e` and containing all other
splitting idempotents, the localization away from `e` — i.e. the summand sections — is
the quotient by `1 - e`, which is the localization at `m`. -/
theorem isLocalization_atPrime_summandSections (hes : CompleteOrthogonalIdempotents es) :
    IsLocalization m.asIdeal.primeCompl
      (summandSections f x p₁ es i σ y hy χ heval hi) := by
  have hidem : IsIdempotentElem ((toFiberSections f x p₁).hom (es i)) :=
    (hes.idem i).map (toFiberSections f x p₁).hom
  haveI h1 : IsLocalization.Away ((toFiberSections f x p₁).hom (es i))
      (summandSections f x p₁ es i σ y hy χ heval hi) :=
    isLocalization_awaySelf_summandSections f x p₁ es i σ y hy χ heval hi hes
  haveI h2 : IsLocalization.Away ((toFiberSections f x p₁).hom (es i))
      (fiberSections f x ⧸ Ideal.span {1 - (toFiberSections f x p₁).hom (es i)}) :=
    isLocalization_away_quotient_span_one_sub hidem
  haveI h3 : IsLocalization m.asIdeal.primeCompl
      (fiberSections f x ⧸ Ideal.span {1 - (toFiberSections f x p₁).hom (es i)}) :=
    hidem.isLocalization_quotient_span_one_sub m hnot
      (fun M hM hne => hmem ⟨M, hM⟩ (fun h => hne (congrArg MaximalSpectrum.asIdeal h)))
  exact IsLocalization.isLocalization_of_algEquiv m.asIdeal.primeCompl
    (IsLocalization.algEquiv
      (Submonoid.powers ((toFiberSections f x p₁).hom (es i)))
      (fiberSections f x ⧸ Ideal.span {1 - (toFiberSections f x p₁).hom (es i)})
      (summandSections f x p₁ es i σ y hy χ heval hi))

/-- **The identification of the localization of the fiber sections at `m` with the
summand sections**, as an algebra isomorphism over the fiber sections. -/
noncomputable def localizationAtPrimeToSummandSections
    (hes : CompleteOrthogonalIdempotents es) :
    Localization.AtPrime m.asIdeal ≃ₐ[fiberSections f x]
      summandSections f x p₁ es i σ y hy χ heval hi :=
  haveI := isLocalization_atPrime_summandSections f x p₁ es i σ y hy χ heval hi m hnot
    hmem hes
  IsLocalization.algEquiv m.asIdeal.primeCompl (Localization.AtPrime m.asIdeal)
    (summandSections f x p₁ es i σ y hy χ heval hi)

include hnot hmem in
/-- The summand sections form a local ring: they are the localization of the fiber
sections at the maximal ideal `m`. -/
theorem isLocalRing_summandSections (hes : CompleteOrthogonalIdempotents es) :
    IsLocalRing (summandSections f x p₁ es i σ y hy χ heval hi) := by
  haveI := isLocalization_atPrime_summandSections f x p₁ es i σ y hy χ heval hi m hnot
    hmem hes
  exact IsLocalization.AtPrime.isLocalRing
    (S := summandSections f x p₁ es i σ y hy χ heval hi) m.asIdeal

include hnot hmem in
/-- **The summand sections are strictly henselian** (Stacks 04GH for the summand
sections): they are isomorphic to the localization of the fiber sections at a maximal
ideal, which is a finite local algebra over the strictly henselian strict
localization. -/
theorem isStrictlyHenselianLocalRing_summandSections
    (hes : CompleteOrthogonalIdempotents es) :
    IsStrictlyHenselianLocalRing (summandSections f x p₁ es i σ y hy χ heval hi) := by
  haveI := isStrictlyHenselianLocalRing_localization_atPrime_fiberSections f x m
  exact IsStrictlyHenselianLocalRing.of_ringEquiv
    (localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot hmem
      hes).toRingEquiv

include hnot hmem in
/-- **The splitting hypothesis for the summand sections** (Stacks 04GG (10) for the
summand sections): every module-finite algebra over the summand sections splits as the
product of its localizations at maximal ideals — the splitting property of the fiber
localization at `m` transferred along the identification, being intrinsic to the
algebra. -/
theorem forall_module_finite_bijective_pi_summandSections
    (hes : CompleteOrthogonalIdempotents es) :
    ∀ (T : Type u) [CommRing T]
      [Algebra (summandSections f x p₁ es i σ y hy χ heval hi) T],
      Module.Finite (summandSections f x p₁ es i σ y hy χ heval hi) T →
      Function.Bijective (Pi.ringHom
        (fun n : MaximalSpectrum T => algebraMap T (Localization.AtPrime n.asIdeal))) := by
  intro T _ _ hT
  -- transfer the algebra structure along the identification with the localization
  letI : Algebra (Localization.AtPrime m.asIdeal)
      (summandSections f x p₁ es i σ y hy χ heval hi) :=
    (localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot hmem
      hes).toAlgHom.toRingHom.toAlgebra
  letI : Algebra (Localization.AtPrime m.asIdeal) T :=
    ((algebraMap (summandSections f x p₁ es i σ y hy χ heval hi) T).comp
      (algebraMap (Localization.AtPrime m.asIdeal)
        (summandSections f x p₁ es i σ y hy χ heval hi))).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime m.asIdeal)
      (summandSections f x p₁ es i σ y hy χ heval hi) T :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : Module.Finite (Localization.AtPrime m.asIdeal)
      (summandSections f x p₁ es i σ y hy χ heval hi) :=
    Module.Finite.of_surjective
      (Algebra.linearMap (Localization.AtPrime m.asIdeal)
        (summandSections f x p₁ es i σ y hy χ heval hi))
      (localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot hmem
        hes).surjective
  haveI hTfin : Module.Finite (Localization.AtPrime m.asIdeal) T :=
    Module.Finite.trans (summandSections f x p₁ es i σ y hy χ heval hi) T
  -- the splitting is intrinsic to `T`
  exact forall_module_finite_bijective_pi_localization_fiberSections f x m T hTfin

/-- **The residue field of the summand sections is separably closed**: it is the residue
field of the fiber localization at `m`. -/
theorem isSepClosed_residueField_summandSections
    (hes : CompleteOrthogonalIdempotents es) :
    haveI := isLocalRing_summandSections f x p₁ es i σ y hy χ heval hi m hnot hmem hes
    IsSepClosed (IsLocalRing.ResidueField
      (summandSections f x p₁ es i σ y hy χ heval hi)) := by
  haveI := isLocalRing_summandSections f x p₁ es i σ y hy χ heval hi m hnot hmem hes
  haveI : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime m.asIdeal)) :=
    isSepClosed_residueField_localization_atPrime_fiberSections f x m
  exact IsSepClosed.of_ringEquiv (IsLocalRing.ResidueField.mapEquiv
    (localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot hmem
      hes).toRingEquiv)

/-- **Retractions of étale algebras over the summand sections** (Stacks 04GG (8) for
the summand sections): every character of an étale algebra over the summand sections
whose restriction cuts out the maximal ideal is compatible with a retraction. This is
the workhorse for the dominance half of the cofinality of the summand system. -/
theorem exists_retraction_of_etale_summandSections
    (hes : CompleteOrthogonalIdempotents es)
    (B : Type u) [CommRing B]
    [Algebra (summandSections f x p₁ es i σ y hy χ heval hi) B]
    (hB : Algebra.Etale (summandSections f x p₁ es i σ y hy χ heval hi) B)
    {Ω'' : Type u} [Field Ω''] (χB : B →+* Ω'')
    (hkerB : RingHom.ker (χB.comp
        (algebraMap (summandSections f x p₁ es i σ y hy χ heval hi) B)) =
      haveI := isLocalRing_summandSections f x p₁ es i σ y hy χ heval hi m hnot hmem hes
      IsLocalRing.maximalIdeal (summandSections f x p₁ es i σ y hy χ heval hi)) :
    ∃ τ : B →+* summandSections f x p₁ es i σ y hy χ heval hi,
      τ.comp (algebraMap (summandSections f x p₁ es i σ y hy χ heval hi) B) =
        RingHom.id (summandSections f x p₁ es i σ y hy χ heval hi) ∧
      (χB.comp (algebraMap (summandSections f x p₁ es i σ y hy χ heval hi) B)).comp τ =
        χB := by
  haveI := isLocalRing_summandSections f x p₁ es i σ y hy χ heval hi m hnot hmem hes
  haveI : IsSepClosed (IsLocalRing.ResidueField
      (summandSections f x p₁ es i σ y hy χ heval hi)) :=
    isSepClosed_residueField_summandSections f x p₁ es i σ y hy χ heval hi m hnot hmem
      hes
  exact IsLocalRing.exists_retraction_of_etale_of_ker_comp_eq
    (forall_module_finite_bijective_pi_summandSections f x p₁ es i σ y hy χ heval hi m
      hnot hmem hes) B hB χB hkerB

/-!
### The kernel of the evaluation character and unit detection
-/

include hker hnot hmem in
/-- **The evaluation character cuts out the maximal ideal of the summand sections**:
the kernel of evaluation at the lifted geometric point is the maximal ideal of the
local ring of summand sections. -/
theorem ker_summandSectionsEval (hes : CompleteOrthogonalIdempotents es) :
    haveI := isLocalRing_summandSections f x p₁ es i σ y hy χ heval hi m hnot hmem hes
    RingHom.ker (summandSectionsEval f x p₁ es i σ y hy χ heval hi) =
      IsLocalRing.maximalIdeal (summandSections f x p₁ es i σ y hy χ heval hi) := by
  haveI := isLocalization_atPrime_summandSections f x p₁ es i σ y hy χ heval hi m hnot
    hmem hes
  haveI := isLocalRing_summandSections f x p₁ es i σ y hy χ heval hi m hnot hmem hes
  refine Ideal.ext fun w => ?_
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective m.asIdeal.primeCompl w
  have hs0 : (s : fiberSections f x) ∉ m.asIdeal := s.2
  have hχs : χ (s : fiberSections f x) ≠ 0 := by
    intro h0
    have hks : (s : fiberSections f x) ∈ RingHom.ker χ := RingHom.mem_ker.mpr h0
    rw [hker] at hks
    exact hs0 hks
  have hspec := IsLocalization.mk'_spec
    (summandSections f x p₁ es i σ y hy χ heval hi) a s
  have hmul := congrArg (summandSectionsEval f x p₁ es i σ y hy χ heval hi) hspec
  rw [map_mul] at hmul
  simp only [summandSectionsEval_algebraMap f x p₁ es i σ y hy χ heval hi] at hmul
  rw [RingHom.mem_ker,
    IsLocalization.AtPrime.mk'_mem_maximal_iff
      (summandSections f x p₁ es i σ y hy χ heval hi) m.asIdeal a s]
  constructor
  · intro h0
    have hχa : χ a = 0 := by
      rw [← hmul, h0, zero_mul]
    have hma : a ∈ RingHom.ker χ := RingHom.mem_ker.mpr hχa
    rwa [hker] at hma
  · intro hma
    have hka : a ∈ RingHom.ker χ := by
      rw [hker]
      exact hma
    have hχa : χ a = 0 := RingHom.mem_ker.mp hka
    have h0 : summandSectionsEval f x p₁ es i σ y hy χ heval hi
        (IsLocalization.mk' (summandSections f x p₁ es i σ y hy χ heval hi) a s) *
          χ (s : fiberSections f x) = 0 := by
      rw [hmul, hχa]
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hχs

include hker hnot hmem in
/-- **Unit detection for germs of summand sections**: the germ of a section of a
summand in the summand sections colimit is invertible if and only if the value of the
section at the lifted geometric point is nonzero. -/
theorem isUnit_toSummandSections_iff_eval_ne_zero
    (hes : CompleteOrthogonalIdempotents es) (g : SummandIndex x p₁)
    (b : Γ((summand f x p₁ es i g).left, ⊤)) :
    IsUnit ((toSummandSections f x p₁ es i σ y hy χ heval hi g).hom b) ↔
      (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom
        (((summandPoint f x p₁ es i σ y hy χ heval hi g).val.appTop).hom b) ≠ 0 := by
  haveI := isLocalRing_summandSections f x p₁ es i σ y hy χ heval hi m hnot hmem hes
  have hker' := ker_summandSectionsEval f x p₁ es i σ y hy χ heval hi m hker hnot hmem
    hes
  have h1 : summandSectionsEval f x p₁ es i σ y hy χ heval hi
      ((toSummandSections f x p₁ es i σ y hy χ heval hi g).hom b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom.hom
        (((summandPoint f x p₁ es i σ y hy χ heval hi g).val.appTop).hom b) :=
    eval_toSummandSections f x p₁ es i σ y hy χ heval hi g b
  rw [← IsLocalRing.notMem_maximalIdeal, not_iff_not, ← hker', RingHom.mem_ker, h1]

/-!
### The equalizing condition for the summand system
-/

include hker hnot hmem in
/-- **The equalizing half of the cofinality of the summand system**: two morphisms from
a summand (with its lifted point) to an étale neighbourhood of `y` are equalized by the
transition map from a finer stage. The two morphisms agree on the open agreement locus,
which contains the lifted geometric point; a basic open around the point inside the
agreement locus has a section which does not vanish at the point, hence has invertible
germ in the summand sections, hence is invertible at a finer stage — over which the
summand maps into the agreement locus. -/
theorem exists_summandFunctor_map_comp_eq (hes : CompleteOrthogonalIdempotents es)
    {d : (geometricPoint y).fiber.Elements} {g : SummandIndex x p₁}
    (s s' : (summandFunctor f x p₁ es i σ y hy χ heval hi).obj g ⟶ d) :
    ∃ (g' : SummandIndex x p₁) (t : g' ⟶ g),
      (summandFunctor f x p₁ es i σ y hy χ heval hi).map t ≫ s =
        (summandFunctor f x p₁ es i σ y hy χ heval hi).map t ≫ s' := by
  haveI : Etale d.1.hom := d.1.prop
  haveI : IsAffine ((summandFunctor f x p₁ es i σ y hy χ heval hi).obj g).1.left :=
    inferInstanceAs (IsAffine (summand f x p₁ es i g).left)
  -- the two morphisms are over `Y` and equalized by the lifted point
  have hw : s.val.left ≫ d.1.hom = s'.val.left ≫ d.1.hom :=
    (MorphismProperty.Over.w s.val).trans (MorphismProperty.Over.w s'.val).symm
  have hpt : (summandPoint f x p₁ es i σ y hy χ heval hi g).val ≫ s.val.left =
      (summandPoint f x p₁ es i σ y hy χ heval hi g).val ≫ s'.val.left := by
    have h1 : (summandPoint f x p₁ es i σ y hy χ heval hi g).val ≫ s.val.left =
        d.2.val := congrArg Subtype.val s.property
    have h2 : (summandPoint f x p₁ es i σ y hy χ heval hi g).val ≫ s'.val.left =
        d.2.val := congrArg Subtype.val s'.property
    exact h1.trans h2.symm
  -- a basic open around the point on which the morphisms agree
  obtain ⟨b, hbmem, hbeq⟩ := exists_mem_basicOpen_forall_comp_eq d.1.hom s.val.left
    s'.val.left hw (summandPoint f x p₁ es i σ y hy χ heval hi g).val hpt default
  -- its section has invertible germ in the summand sections
  have hunit : IsUnit ((toSummandSections f x p₁ es i σ y hy χ heval hi g).hom b) := by
    refine (isUnit_toSummandSections_iff_eval_ne_zero f x p₁ es i σ y hy χ heval hi m
      hker hnot hmem hes g b).mpr ?_
    intro h0
    -- the value of `b` at the point vanishes, so `b` vanishes on the point's preimage
    have hc0 : (((summandPoint f x p₁ es i σ y hy χ heval hi g).val.appTop).hom b) = 0 := by
      have h9 := congrArg (fun t => CommRingCat.Hom.hom t
          (((summandPoint f x p₁ es i σ y hy χ heval hi g).val.appTop).hom b))
        (Scheme.ΓSpecIso (CommRingCat.of Ω')).hom_inv_id
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id,
        RingHom.id_apply] at h9
      rw [← h9, h0, map_zero]
    -- contradiction with the membership in the basic open
    have hd : default ∈ (summandPoint f x p₁ es i σ y hy χ heval hi g).val ⁻¹ᵁ
        ((summand f x p₁ es i g).left.basicOpen b) := hbmem
    have hpre : (summandPoint f x p₁ es i σ y hy χ heval hi g).val ⁻¹ᵁ
        ((summand f x p₁ es i g).left.basicOpen b) =
        (Spec (CommRingCat.of Ω')).basicOpen
          (((summandPoint f x p₁ es i σ y hy χ heval hi g).val.appTop).hom b) :=
      (summandPoint f x p₁ es i σ y hy χ heval hi g).val.preimage_basicOpen_top b
    rw [hpre, hc0, Scheme.basicOpen_zero] at hd
    simp at hd
  -- descend the invertibility to a finer stage
  obtain ⟨g', t, ht⟩ := exists_isUnit_map_of_isUnit f x p₁ es i σ y hy χ heval hi g b
    hunit
  have ht' : IsUnit ((((summandMap f x p₁ es i t).left).appTop).hom b) := ht
  -- the transition map from the finer stage equalizes the two morphisms
  have hcomp : (summandMap f x p₁ es i t).left ≫ s.val.left =
      (summandMap f x p₁ es i t).left ≫ s'.val.left :=
    hbeq (summandMap f x p₁ es i t).left ht'
  refine ⟨g', t, ?_⟩
  refine CategoryOfElements.ext _ _ _ ?_
  refine MorphismProperty.Over.Hom.ext ?_
  exact hcomp

/-!
### Compatibility with the comparison map of the fiber localization
-/

/-- **The identification of the summand sections with the fiber localization is
compatible with the comparison maps to the strict localization**: the germ comparison
of the summand sections, composed with the identification, is the comparison map
`AlgebraicGeometry.Scheme.Etale.localizationAtPrimeToStrictLocalization` from the
localization of the fiber sections at `m`. -/
theorem summandSectionsToStrictLocalization_localizationAtPrimeToSummandSections
    (hes : CompleteOrthogonalIdempotents es) (z : Localization.AtPrime m.asIdeal) :
    (summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi).hom
        (localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot hmem
          hes z) =
      localizationAtPrimeToStrictLocalization f x σ y hy χ m heval hker z := by
  have hcomp : ((summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval
      hi).hom).comp
        (localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot hmem
          hes).toAlgHom.toRingHom =
      localizationAtPrimeToStrictLocalization f x σ y hy χ m heval hker := by
    apply IsLocalization.ringHom_ext m.asIdeal.primeCompl
    refine RingHom.ext fun z' => ?_
    have h1 : localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot
        hmem hes
          (algebraMap (fiberSections f x) (Localization.AtPrime m.asIdeal) z') =
        algebraMap (fiberSections f x)
          (summandSections f x p₁ es i σ y hy χ heval hi) z' :=
      (localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot hmem
        hes).commutes z'
    have h2 := congrArg (fun t => CommRingCat.Hom.hom t z')
      (fiberSectionsToSummandSections_summandSectionsToStrictLocalization f x p₁ es i σ
        y hy χ heval hi)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    have h3 := localizationAtPrimeToStrictLocalization_algebraMap f x σ y hy χ m heval
      hker z'
    have h4 : (summandSectionsToStrictLocalization f x p₁ es i σ y hy χ heval hi).hom
        (localizationAtPrimeToSummandSections f x p₁ es i σ y hy χ heval hi m hnot hmem
          hes
          (algebraMap (fiberSections f x) (Localization.AtPrime m.asIdeal) z')) =
        (fiberSectionsToStrictLocalization f x σ y hy).hom z' := by
      rw [h1]
      exact h2
    exact h4.trans h3.symm
  exact RingHom.congr_fun hcomp z

end Local

end AlgebraicGeometry.Scheme.Etale
