/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WLocalization.Basic
import Proetale.Algebra.IndEtale
import Proetale.Algebra.ProEtaleContraction
import Proetale.Mathlib.Algebra.Algebra.Prod
import Proetale.Mathlib.RingTheory.Etale.IndSpreads
import Proetale.Mathlib.RingTheory.Etale.Prod
import Proetale.Mathlib.RingTheory.Henselian

/-!
# w-strict-localization

In this file we show that every ring admits a faithfully flat, ind-étale w-strictly-local algebra.
-/

universe u

/-! ### Transfer of strict henselianity along ring isomorphisms

These helpers let us move the property `IsStrictlyHenselianLocalRing` across a ring
isomorphism. They are used below to reduce the strict-henselian-stalks step in
`isStrictlyHenselianLocalRing_WLocalization_IndEtaleContraction` to a single
maximality hypothesis on the comap of the maximal ideal.
-/

/-- `IsSepClosed` transfers along a ring isomorphism of fields. -/
private lemma isSepClosed_of_ringEquiv {k : Type*} [Field k] {k' : Type*} [Field k']
    (e : k ≃+* k') [IsSepClosed k] : IsSepClosed k' := by
  refine ⟨fun p hp => ?_⟩
  -- Pull back to k via e.symm; the pullback is separable, hence splits in k; push forward.
  have hsep : (p.map (e.symm.toRingHom)).Separable := hp.map
  have hsplit : (p.map (e.symm.toRingHom)).Splits :=
    IsSepClosed.splits_of_separable _ hsep
  have hpush := hsplit.map e.toRingHom
  rw [Polynomial.map_map, e.toRingHom_comp_symm_toRingHom, Polynomial.map_id] at hpush
  exact hpush

/-- `HenselianLocalRing` transfers along a ring isomorphism. -/
private lemma henselianLocalRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [HenselianLocalRing R] (e : R ≃+* S) : HenselianLocalRing S := by
  haveI : IsLocalRing S := e.isLocalRing
  refine HenselianLocalRing.mk (fun f hf a₀ hmem hunit => ?_)
  -- Pull `f` and `a₀` back through `e.symm`.
  let f' : Polynomial R := f.map e.symm.toRingHom
  have hf'_monic : f'.Monic := hf.map _
  let a₀' : R := e.symm a₀
  -- `eval a₀' f' = e.symm (eval a₀ f)`.
  have heval : Polynomial.eval a₀' f' = e.symm (Polynomial.eval a₀ f) := by
    show Polynomial.eval (e.symm.toRingHom a₀) (f.map e.symm.toRingHom) = _
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rfl
  have hderiv : Polynomial.eval a₀' f'.derivative = e.symm (Polynomial.eval a₀ f.derivative) := by
    show Polynomial.eval (e.symm.toRingHom a₀) (Polynomial.derivative (f.map e.symm.toRingHom)) = _
    rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rfl
  have hmem' : Polynomial.eval a₀' f' ∈ IsLocalRing.maximalIdeal R := by
    rw [heval, IsLocalRing.mem_maximalIdeal] at *
    intro hu
    exact hmem (by simpa using e.toRingHom.isUnit_map hu)
  have hunit' : IsUnit (Polynomial.eval a₀' f'.derivative) := by
    rw [hderiv]; exact e.symm.toRingHom.isUnit_map hunit
  obtain ⟨a, ha_root, ha_diff⟩ :=
    HenselianLocalRing.is_henselian f' hf'_monic a₀' hmem' hunit'
  refine ⟨e a, ?_, ?_⟩
  · -- `f.IsRoot (e a)`.
    show Polynomial.eval (e a) f = 0
    have key : Polynomial.eval (e a) f = e (Polynomial.eval a f') := by
      show Polynomial.eval (e.toRingHom a) f = _
      have hf_eq : f = f'.map e.toRingHom := by
        show f = (f.map e.symm.toRingHom).map e.toRingHom
        rw [Polynomial.map_map, e.toRingHom_comp_symm_toRingHom, Polynomial.map_id]
      conv_lhs => rw [hf_eq]
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
      rfl
    rw [key, ha_root, map_zero]
  · -- `e a - a₀ ∈ maximalIdeal S`.
    rw [IsLocalRing.mem_maximalIdeal] at ha_diff ⊢
    intro hu
    apply ha_diff
    have h1 : a - a₀' = e.symm (e a - a₀) := by
      simp [a₀']
    rw [h1]; exact e.symm.toRingHom.isUnit_map hu

/-- `IsStrictlyHenselianLocalRing` transfers along a ring isomorphism. -/
private lemma isStrictlyHenselianLocalRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsStrictlyHenselianLocalRing R] (e : R ≃+* S) : IsStrictlyHenselianLocalRing S := by
  haveI : IsLocalRing S := e.isLocalRing
  haveI : HenselianLocalRing S := henselianLocalRing_of_ringEquiv e
  refine ⟨?_⟩
  exact isSepClosed_of_ringEquiv (IsLocalRing.ResidueField.mapEquiv e)

section StrictlyHenselianWLocalizationOfIndEtaleContraction

/-! ### Strictly Henselian stalks of `WLocalization (IndEtaleContraction A)`

The key mathematical results needed for `WStrictLocalization`:

1. **cor:strictly-henselian-etale-contraction** (Blueprint): For any maximal ideal `m` of
   `IndEtaleContraction A`, `(IndEtaleContraction A)_m` is strictly Henselian. This follows from
   `prop:etale-contraction-retraction` (formalized as
   `RingHom.Etale.exists_comp_eq_id_indContraction`: every faithfully flat etale map out of
   `IndEtaleContraction A` has a retraction) and `lemma:retractions-strictly-henselian` (if every
   faithfully flat etale map has a retraction, then localizations at maximal ideals are strictly
   Henselian).

2. **thm:ind-Zariski-identifies-local-rings** (partially formalized as
   `bijectiveOnStalks_algebraMap`): The ind-Zariski map `IndEtaleContraction A -> WLocalization
   (IndEtaleContraction A)` has bijective stalk maps, so local rings are identified through ring
   isomorphisms.

3. **Transfer**: The bijective stalk map at a maximal ideal `m` of `WLocalization(IndEtaleContraction A)`
   gives a ring isomorphism between the localization at `m.comap` and the localization at `m`.
   Combined with (1), (2), and the fact that `m.comap` is maximal (which follows from the
   closed point structure of the WLocalization), this gives strictly Henselian stalks.

The full proof uses `lemma:retractions-strictly-henselian` (etale-ind-spreads, prime avoidance,
faithfully flat etale covers); see the docstring on the private lemma below for the outline.
-/

variable {A : Type u} [CommRing A]

/-- **Etale-ind-spreads at the localization-at-a-prime** (Stacks 00U6 specialized).

Given a maximal ideal `m` of `A`, the local ring `A_m = Localization.AtPrime m` is the filtered
colimit (over `f ∉ m`) of the standard opens `A_f = Localization.Away f`. Since étale algebras
are finitely presented, any étale `A_m`-algebra `B` descends to an étale `A_f`-algebra `B'` at
some finite stage, with `B ≃ₐ[A_m] A_m ⊗[A_f] B'`.

This is the key "descent" step needed in `isStrictlyHenselianLocalRing_of_exists_retraction`
(Blueprint `lemma:retractions-strictly-henselian`, local-structure.tex lines 1758–1797): it
converts the abstract étale `A_m`-algebra appearing as `S_f = A_m[X,Y]/(f, f'·Y − 1)` (resp. as
`L = A_m[X]/(f)` after lifting from the residue field) into an étale `A_f`-algebra `B'`, after
which prime avoidance + the faithfully-flat-étale product cover + the retraction hypothesis
combine to produce the desired section.

The full Lean proof would proceed via:
* the colimit presentation `Localization.AtPrime m ≃ filtered colim_{f ∉ m} Localization.Away f`
  (objective 2 of the round: see `IndZariski.of_isLocalization`),
* `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit` applied to the structure map
  `Localization.Away f₀ → B` (where `f₀` is the unit of the localization), to descend `B` to a
  finitely presented `Localization.Away f`-algebra `B'`,
* `Algebra.FormallyEtale.localization_map` (Mathlib) — or rather its converse — to transport
  the formally-étale property along the localization,
* checking that the descended `B'` is étale by `Algebra.FormallyEtale.of_isLocalization`-style
  reasoning at the stage and the finite-presentation already established.

This is left as a sub-task. -/
private lemma exists_descent_at_localization
    {R : Type u} [CommRing R] (m : Ideal R) [m.IsMaximal]
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime m) B]
    [Algebra.Etale (Localization.AtPrime m) B] :
    ∃ (f : R) (_hf : f ∉ m) (B' : Type u) (_ : CommRing B')
      (_ : Algebra (Localization.Away f) B') (_ : Algebra.Etale (Localization.Away f) B')
      (_ : Algebra (Localization.Away f) (Localization.AtPrime m))
      (_ : Algebra (Localization.Away f) B)
      (_ : IsScalarTower (Localization.Away f) (Localization.AtPrime m) B),
      Nonempty (B ≃ₐ[Localization.AtPrime m]
        TensorProduct (Localization.Away f) (Localization.AtPrime m) B') := by
  -- Structural outline. Five-step proof; the deep gap is in step 1 (the colimit
  -- presentation `A_m = colim_{f ∉ m} A_f`), which is currently `sorry` in
  -- `Algebra.IndZariski.of_isLocalization` (`Proetale/Algebra/IndZariski.lean:183`).
  --
  -- Step 1: `A_m ≃ colim_{f ∉ m} A_f` as a filtered colimit of standard-open localizations.
  --   Concretely: index category `(R.primeCompl m).divisibility` (a thin filtered category);
  --   diagram `f ↦ CommAlgCat.of R (Localization.Away f)`; cocone vertex `CommAlgCat.of R A_m`;
  --   `IsColimit` witness from `IsLocalization (m.primeCompl) A_m`.
  --   Currently this is `Algebra.IndZariski.of_isLocalization R (Localization.AtPrime m)
  --     m.primeCompl`, which gives `Algebra.IndZariski R (Localization.AtPrime m)`. To extract a
  --   concrete `ColimitPresentation`, refine to a presentation where each stage *is* a
  --   `Localization.Away f`. (The generic `IndZariski` presentation only guarantees stages are
  --   `IsLocalIso`.)
  --
  -- Step 2: étale ⇒ finitely presented (`Algebra.Etale.finitePresentation`), so `B` is
  --   `Algebra.FinitePresentation (Localization.AtPrime m) B`, equivalently
  --   `IsFinitelyPresentable.{u} (Under.mk (algebraMap _ B) : Under (CommRingCat.of A_m))`.
  --
  -- Step 3: `IsFinitelyPresentable.exists_hom_of_isColimit_under` applied to the diagram of
  --   stage-Away-algebras + the structure map gives `(j : J)` (some `f ∉ m`) and a stage-level
  --   structure map `Localization.Away f → B'` with `B'` finitely presented over `Localization.Away f`.
  --
  -- Step 4: `Algebra.FormallyEtale.localization_map` (converse direction): if `Localization.AtPrime m`
  --   is a localization of `Localization.Away f` (yes, at the prime above `m`), and the base change
  --   `Localization.AtPrime m ⊗[Localization.Away f] B' ≃ B` is formally étale (B is étale over
  --   A_m by hypothesis), then `B'` is formally étale at the stage. Combined with FP (step 3),
  --   `B'` is étale over `Localization.Away f`.
  --
  -- Step 5: the comparison `Localization.AtPrime m ⊗[Localization.Away f] B' → B` is built from
  --   the universal property + the factorisation of step 3; it is an iso by Stacks 00U6.
  --
  -- The structural blocker: step 1 produces a generic `IndZariski` presentation whose stages
  -- are not standard opens. Refining to standard opens (the "filtered colim of Away f's") is
  -- the missing piece; once `Algebra.IndZariski.of_isLocalization` is filled with the explicit
  -- standard-open presentation, the entire descent goes through.
  --
  -- The descent is now packaged in
  -- `Algebra.Etale.exists_descent_along_localizationAtPrime`
  -- (`Proetale/Mathlib/RingTheory/Etale/IndSpreads.lean`). That helper still carries
  -- a `sorry` body (the full Stacks 00U6 spreading is estimated at 300-500 LOC and is
  -- left for a future round), but the central statement has been factored out so that
  -- this lemma reduces to a single application. The new descent additionally exposes
  -- an `IsScalarTower R (Loc.Away f) (Loc.AtPrime m)` binder; this wrapper drops it
  -- since the older signature pre-dates that addition.
  obtain ⟨f, hf, B', _instB'Ring, _instB'Alg, _instB'Etale,
          _instAfAm, _instRAfAm, _instAfB, _instTower, iso⟩ :=
    Algebra.Etale.exists_descent_along_localizationAtPrime m B
  exact ⟨f, hf, B', _instB'Ring, _instB'Alg, _instB'Etale, _instAfAm,
         _instAfB, _instTower, iso⟩

/-- **Step 3 (prime avoidance).** Given a prime ideal `q` and finitely many ideals
`f i` (`i ∈ s`), none of which is contained in `q`, there exists an element `g`
lying in every `f i` but not in `q`.

This is the standard "prime avoidance" lemma, packaged in the form used by
`lemma:retractions-strictly-henselian`. -/
private lemma exists_mem_finset_inf_notMem_of_isPrime
    {R : Type*} [CommRing R] {ι : Type*} {s : Finset ι} {f : ι → Ideal R}
    {q : Ideal R} [q.IsPrime] (hnotle : ∀ i ∈ s, ¬ f i ≤ q) :
    ∃ g : R, g ∉ q ∧ ∀ i ∈ s, g ∈ f i := by
  -- The intersection `s.inf f` is not contained in `q`, by the prime-ideal form
  -- of `s.inf f ≤ q ↔ ∃ i ∈ s, f i ≤ q`.
  have hnot_le : ¬ (s.inf f ≤ q) := fun h => by
    obtain ⟨i, his, hi⟩ := (Ideal.IsPrime.inf_le' ‹q.IsPrime›).mp h
    exact hnotle i his hi
  have hnot_subset : ¬ ((s.inf f : Ideal R) : Set R) ⊆ (q : Set R) := hnot_le
  rw [Set.not_subset] at hnot_subset
  obtain ⟨g, hg_inf, hg_q⟩ := hnot_subset
  refine ⟨g, hg_q, ?_⟩
  rwa [SetLike.mem_coe, Submodule.mem_finsetInf] at hg_inf

/-- **Step 2 (finite primes over a maximal ideal in an étale algebra).**
Given an étale algebra `S'` over `T` and a maximal ideal `J` of `T`, the set of primes
of `S'` lying over `J` is finite.

This follows from `Algebra.QuasiFinite.finite_primesOver` together with the (still-to-be
formalised) fact that an étale algebra is quasi-finite: the fibre at any maximal ideal
is a finite product of finite separable field extensions of the residue field, hence
finite-dimensional over it.

Left as a typed `sorry`; the formal proof requires importing/proving
`Algebra.Etale → Algebra.QuasiFinite`. -/
private lemma Algebra.Etale.finite_primesOver
    {T : Type u} [CommRing T] (S' : Type u) [CommRing S'] [Algebra T S']
    [Algebra.Etale T S'] (J : Ideal T) [J.IsMaximal] :
    (J.primesOver S').Finite := by
  -- Strategy: establish `Algebra.QuasiFinite T S'` and apply
  -- `Algebra.QuasiFinite.finite_primesOver J`. The instance unfolds to: for each
  -- prime `P` of `T`, the fibre `P.Fiber S' = P.ResidueField ⊗[T] S'` is finite
  -- as a module over `P.ResidueField`. The fibre is étale over the residue field
  -- by base change, and a field-étale algebra is a finite product of finite
  -- separable extensions (Stacks 02GL = `Algebra.Etale.iff_exists_algEquiv_prod`),
  -- hence finite-dimensional.
  haveI : Algebra.QuasiFinite T S' := by
    refine ⟨fun P _ => ?_⟩
    -- The fibre is étale over `P.ResidueField` by base change.
    haveI : Algebra.Etale P.ResidueField (P.Fiber S') :=
      Algebra.Etale.baseChange T S' P.ResidueField
    -- A field-étale algebra is `≃ₐ` to a finite product of finite separable extensions.
    obtain ⟨I, hfin, Ai, hField, hAlg, e, hprod⟩ :=
      (Algebra.Etale.iff_exists_algEquiv_prod P.ResidueField (P.Fiber S')).mp inferInstance
    haveI : Finite I := hfin
    letI : ∀ i, Field (Ai i) := hField
    letI : ∀ i, Algebra P.ResidueField (Ai i) := hAlg
    haveI : ∀ i, Module.Finite P.ResidueField (Ai i) := fun i => (hprod i).1
    haveI : Module.Finite P.ResidueField (∀ i, Ai i) := Module.Finite.pi
    -- Transfer module-finiteness through `e.symm`.
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact Algebra.QuasiFinite.finite_primesOver J

/-- **Geometric helper for the natural cover.** Given a closed set `Z` in `Spec A` whose
complement contains the maximal point `m`, there is a finite family of elements
`(aᵢ)ᵢ∈s` of `A`, none of which lies in `m`, such that the basic opens `D(aᵢ)` cover `Z`.

This packages the standard prime-avoidance + quasi-compactness argument used in
`Algebra.Etale.exists_ff_etale_product_cover_of_prime_over`. -/
private lemma exists_finset_basicOpen_cover_avoiding_maximal
    {A : Type u} [CommRing A] (m : Ideal A) [hm : m.IsMaximal]
    (Z : Set (PrimeSpectrum A)) (hZ_closed : IsClosed Z)
    (_hZ_avoid : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∉ Z) :
    ∃ (s : Finset A), (∀ a ∈ s, a ∉ m) ∧
      Z ⊆ ⋃ a ∈ s, (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
  have hZ_compact : IsCompact Z := hZ_closed.isCompact
  -- For each q ∈ Z, there exists a ∉ m with a ∉ q.asIdeal (i.e., q ∈ basicOpen a).
  -- Reason: q.asIdeal is a proper prime, so A \ q.asIdeal ≠ ∅; if A \ m ⊆ q.asIdeal then
  -- q.asIdeal would contain 1 (since 1 ∉ m). Hence some a is outside both.
  have hcover : Z ⊆ ⋃ a : {a : A // a ∉ m},
      (PrimeSpectrum.basicOpen a.1 : Set (PrimeSpectrum A)) := by
    intro q _
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists] at hnot
    have h1m : (1 : A) ∉ m := fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h)
    have h1notin : q ∉ PrimeSpectrum.basicOpen (1 : A) := hnot ⟨1, h1m⟩
    rw [PrimeSpectrum.mem_basicOpen, not_not] at h1notin
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1notin)
  -- Extract finite subcover via compactness.
  obtain ⟨t, ht⟩ := hZ_compact.elim_finite_subcover
      (fun a : {a : A // a ∉ m} => (PrimeSpectrum.basicOpen a.1 : Set _))
      (fun _ => (PrimeSpectrum.basicOpen _).isOpen) hcover
  classical
  refine ⟨t.image Subtype.val, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact b.2
  · intro q hq
    have := ht hq
    rw [Set.mem_iUnion₂] at this
    rcases this with ⟨b, hb_mem_t, hq_basicOpen⟩
    rw [Set.mem_iUnion₂]
    exact ⟨b.1, Finset.mem_image.mpr ⟨b, hb_mem_t, rfl⟩, hq_basicOpen⟩

/-- **Step 4 (étale faithfully-flat cover from an étale algebra with a prime over `m`).**
Let `A` be a ring and `m` a maximal ideal. If `C` is an étale `A`-algebra in which some
prime ideal lies over `m`, then there exists an étale faithfully flat `A`-algebra `D`
together with an `A`-algebra projection `D →ₐ[A] C`.

The cover used is the natural one `D = C × ∏_{i ∈ s} Localization.Away aᵢ`, where `s` is
a finite set of elements `aᵢ ∈ A`, none in `m`, whose basic opens cover the complement
of the image of `Spec C → Spec A`. The étale property follows from `Algebra.Etale.prod`
+ the Pi-étale instance + the standard `Algebra.Etale.of_isLocalizationAway`. Faithful
flatness follows from surjectivity of `Spec D → Spec A`, which holds by case-split:
the `C`-part covers the image `U`, and the Pi-of-localizations covers `Uᶜ`. -/
private lemma Algebra.Etale.exists_ff_etale_product_cover_of_prime_over
    {A : Type u} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.Etale A C]
    (hCm : ∃ p : Ideal C, p.IsPrime ∧ p.comap (algebraMap A C) = m) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D) (_ : Algebra.Etale A D)
      (_ : Module.FaithfullyFlat A D), Nonempty (D →ₐ[A] C) := by
  haveI : Algebra.HasGoingDown A C := Algebra.HasGoingDown.of_flat
  haveI : Algebra.FinitePresentation A C := Algebra.Etale.finitePresentation
  -- Open image of Spec C → Spec A.
  have hOpenMap : IsOpenMap (PrimeSpectrum.comap (algebraMap A C)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  have hU_open : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap A C))) :=
    hOpenMap.isOpen_range
  obtain ⟨p, hp_prime, hp_comap⟩ := hCm
  let m_pt : PrimeSpectrum A := ⟨m, ‹m.IsMaximal›.isPrime⟩
  have hm_in : m_pt ∈ Set.range (PrimeSpectrum.comap (algebraMap A C)) :=
    ⟨⟨p, hp_prime⟩, PrimeSpectrum.ext hp_comap⟩
  set U : Set (PrimeSpectrum A) := Set.range (PrimeSpectrum.comap (algebraMap A C))
  have hZ_closed : IsClosed (Uᶜ) := hU_open.isClosed_compl
  have hZ_avoid : m_pt ∉ Uᶜ := fun h => h hm_in
  -- Geometric data: finite cover by basic opens avoiding m.
  obtain ⟨s, _hs_notm, hs_cover⟩ :=
    exists_finset_basicOpen_cover_avoiding_maximal m Uᶜ hZ_closed hZ_avoid
  classical
  -- Pi family of `Localization.Away` indexed by `s`.
  haveI : Finite { a : A // a ∈ s } := Finset.finite_toSet s |>.to_subtype
  letI : ∀ i : {a : A // a ∈ s}, Algebra.Etale A (Localization.Away (i.1 : A)) :=
    fun i => Algebra.Etale.of_isLocalizationAway i.1
  let E : Type u := (i : {a : A // a ∈ s}) → Localization.Away (i.1 : A)
  let D : Type u := C × E
  refine ⟨D, inferInstance, inferInstance, inferInstance, ?_, ⟨AlgHom.fst A C E⟩⟩
  -- Module.FaithfullyFlat A D via surjectivity of Spec D → Spec A.
  refine Module.FaithfullyFlat.of_comap_surjective ?_
  intro q
  by_cases hqU : q ∈ U
  · -- q ∈ U: lift through the first projection D → C.
    obtain ⟨qC, hqC⟩ := hqU
    refine ⟨PrimeSpectrum.comap (RingHom.fst C E) qC, ?_⟩
    have hfst : (RingHom.fst C E).comp (algebraMap A D) = algebraMap A C := rfl
    rw [← PrimeSpectrum.comap_comp_apply, hfst, hqC]
  · -- q ∉ U: by `hs_cover`, q ∈ basicOpen aᵢ for some i ∈ s.
    have hq_in_cover := hs_cover hqU
    rw [Set.mem_iUnion₂] at hq_in_cover
    obtain ⟨a, ha_s, hq_basic⟩ := hq_in_cover
    set i : {a : A // a ∈ s} := ⟨a, ha_s⟩
    have hq_in_range : q ∈ Set.range
        (PrimeSpectrum.comap (algebraMap A (Localization.Away a))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
      exact hq_basic
    obtain ⟨qLoc, hqLoc⟩ := hq_in_range
    -- Push qLoc through E.evalRingHom i, then through Prod.snd.
    let qE : PrimeSpectrum E := PrimeSpectrum.comap (Pi.evalRingHom _ i) qLoc
    refine ⟨PrimeSpectrum.comap (RingHom.snd C E) qE, ?_⟩
    have hsnd : (RingHom.snd C E).comp (algebraMap A D) = algebraMap A E := rfl
    have heval : ((Pi.evalRingHom _ i).comp (algebraMap A E) :
        A →+* Localization.Away (i.1 : A)) = algebraMap A (Localization.Away a) := rfl
    rw [← PrimeSpectrum.comap_comp_apply, hsnd,
        show qE = PrimeSpectrum.comap (Pi.evalRingHom _ i) qLoc from rfl,
        ← PrimeSpectrum.comap_comp_apply, heval, hqLoc]

/-- **Explicit-product variant of the étale faithfully-flat cover.**

Same conclusion as `Algebra.Etale.exists_ff_etale_product_cover_of_prime_over`, but
exposing the cover `D` literally as a binary product `C × E` so that the local-ring
case-split tool `AlgHom.exists_section_of_isLocalRing`
(from `Proetale.Mathlib.Algebra.Algebra.Prod`) can be applied to sections out of the
cover.

This is the variant consumed by the step-5 assembly in
`exists_residue_compatible_section_of_retraction`. -/
private lemma Algebra.Etale.exists_explicit_ff_etale_product_cover_of_prime_over
    {A : Type u} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.Etale A C]
    (hCm : ∃ p : Ideal C, p.IsPrime ∧ p.comap (algebraMap A C) = m) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra A E) (_ : Algebra.Etale A E),
      Algebra.Etale A (C × E) ∧ Module.FaithfullyFlat A (C × E) := by
  haveI : Algebra.HasGoingDown A C := Algebra.HasGoingDown.of_flat
  haveI : Algebra.FinitePresentation A C := Algebra.Etale.finitePresentation
  have hOpenMap : IsOpenMap (PrimeSpectrum.comap (algebraMap A C)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  have hU_open : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap A C))) :=
    hOpenMap.isOpen_range
  obtain ⟨p, hp_prime, hp_comap⟩ := hCm
  let m_pt : PrimeSpectrum A := ⟨m, ‹m.IsMaximal›.isPrime⟩
  have hm_in : m_pt ∈ Set.range (PrimeSpectrum.comap (algebraMap A C)) :=
    ⟨⟨p, hp_prime⟩, PrimeSpectrum.ext hp_comap⟩
  set U : Set (PrimeSpectrum A) := Set.range (PrimeSpectrum.comap (algebraMap A C))
  have hZ_closed : IsClosed (Uᶜ) := hU_open.isClosed_compl
  have hZ_avoid : m_pt ∉ Uᶜ := fun h => h hm_in
  obtain ⟨s, _hs_notm, hs_cover⟩ :=
    exists_finset_basicOpen_cover_avoiding_maximal m Uᶜ hZ_closed hZ_avoid
  classical
  haveI : Finite { a : A // a ∈ s } := Finset.finite_toSet s |>.to_subtype
  letI : ∀ i : {a : A // a ∈ s}, Algebra.Etale A (Localization.Away (i.1 : A)) :=
    fun i => Algebra.Etale.of_isLocalizationAway i.1
  let E : Type u := (i : {a : A // a ∈ s}) → Localization.Away (i.1 : A)
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  -- `Module.FaithfullyFlat A (C × E)` via surjectivity of Spec D → Spec A.
  refine Module.FaithfullyFlat.of_comap_surjective ?_
  intro q
  by_cases hqU : q ∈ U
  · -- q ∈ U: lift through the first projection C × E → C.
    obtain ⟨qC, hqC⟩ := hqU
    refine ⟨PrimeSpectrum.comap (RingHom.fst C E) qC, ?_⟩
    have hfst : (RingHom.fst C E).comp (algebraMap A (C × E)) = algebraMap A C := rfl
    rw [← PrimeSpectrum.comap_comp_apply, hfst, hqC]
  · -- q ∉ U: by `hs_cover`, q ∈ basicOpen aᵢ for some i ∈ s.
    have hq_in_cover := hs_cover hqU
    rw [Set.mem_iUnion₂] at hq_in_cover
    obtain ⟨a, ha_s, hq_basic⟩ := hq_in_cover
    set i : {a : A // a ∈ s} := ⟨a, ha_s⟩
    have hq_in_range : q ∈ Set.range
        (PrimeSpectrum.comap (algebraMap A (Localization.Away a))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away a) a]
      exact hq_basic
    obtain ⟨qLoc, hqLoc⟩ := hq_in_range
    let qE : PrimeSpectrum E := PrimeSpectrum.comap (Pi.evalRingHom _ i) qLoc
    refine ⟨PrimeSpectrum.comap (RingHom.snd C E) qE, ?_⟩
    have hsnd : (RingHom.snd C E).comp (algebraMap A (C × E)) = algebraMap A E := rfl
    have heval : ((Pi.evalRingHom _ i).comp (algebraMap A E) :
        A →+* Localization.Away (i.1 : A)) = algebraMap A (Localization.Away a) := rfl
    rw [← PrimeSpectrum.comap_comp_apply, hsnd,
        show qE = PrimeSpectrum.comap (Pi.evalRingHom _ i) qLoc from rfl,
        ← PrimeSpectrum.comap_comp_apply, heval, hqLoc]

/-- **Core content of lemma:retractions-strictly-henselian** (Blueprint
`local-structure.tex` L1701–1740).

If every faithfully flat étale `A`-algebra admits a retraction, then for every maximal
ideal `m` of `A` and every étale `A_m`-algebra `S` equipped with a residue-field map
`g : S → κ(m) = A_m / m·A_m`, there exists a `compatible section` `σ : S → A_m`
(i.e. `(residue) ∘ σ = g`).

This is the single structural sorry left for the blueprint argument; the full proof
proceeds in five steps, each now decomposed as a sub-helper above:

* (1) Stacks 00U6 descent: `Algebra.Etale.exists_descent_along_localizationAtPrime`
  produces `f ∉ m`, an étale `A_f`-algebra `S'`, and an `A_m`-algebra iso
  `S ≃ A_m ⊗[A_f] S'`. The kernel `q` of the composite `S' → S → κ(m)` is a prime
  of `S'` lying over `m·A_f`.

* (2) `Algebra.Etale.finite_primesOver` produces the (currently typed-sorry) Finset
  `{q₁ = q, q₂, …, qₙ}` of all primes of `S'` over `m`.

* (3) `exists_mem_finset_inf_notMem_of_isPrime` (proved above) provides the
  prime-avoidance element `g₁ ∈ ⋂_{i ≥ 2} qᵢ` with `g₁ ∉ q`. Then `q` is the unique
  prime of `S'_{g₁}` over `m`.

* (4) `Algebra.Etale.exists_ff_etale_product_cover_of_prime_over` packages an étale
  faithfully flat cover `D` of `A` together with a projection `D →ₐ[A] C` (with the
  natural cover this is `Prod.fst`-style; the helper currently returns the trivial
  cover `D = A` while still recording the geometric witnesses).

* (5) Apply `hret` to the cover from (4) to obtain a retraction `σ' : D →ₐ[A] A`.
  Localize at `q` (equivalently, restrict via the projection `D → C` to obtain
  `C → A_m`) and pull back through the descent iso of (1) to get the desired
  `S →ₐ[A_m] A_m`. The residue compatibility `(mk) ∘ σ = g` follows from the way
  `q` was chosen to correspond to `ker(g)`.

The final step (5) — assembling the section from the cover + retraction — remains a
structural sorry. -/
private lemma exists_residue_compatible_section_of_retraction
    {A : Type u} [CommRing A]
    (hret : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
      [Module.FaithfullyFlat A B], ∃ σ : B →ₐ[A] A, True)
    (m : Ideal A) [m.IsMaximal]
    (S : Type u) [CommRing S] [Algebra (Localization.AtPrime m) S]
    [Algebra.Etale (Localization.AtPrime m) S]
    (g : S →ₐ[Localization.AtPrime m]
            ((Localization.AtPrime m) ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime m))) :
    ∃ σ : S →ₐ[Localization.AtPrime m] Localization.AtPrime m,
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime m))).comp
        (σ : S →+* _) = (g : S →+* _) := by
  -- Step 1: descent (Stacks 00U6 via `exists_descent_along_localizationAtPrime`).
  -- The output gives us `f ∉ m`, an étale `A_f`-algebra `S'`, scalar-tower instances,
  -- and an `A_m`-algebra iso `S ≃ A_m ⊗[A_f] S'`.
  obtain ⟨f, hf, S', _instS'Ring, _instS'Alg, _instS'Etale,
          _instAfAm, _instRAfAm, _instAfS, _instTower, ⟨iso⟩⟩ :=
    Algebra.Etale.exists_descent_along_localizationAtPrime m S
  -- ====================================================================
  -- Step 2 (kernel of the composite `S' → S → κ(m)`).
  -- We build the ring hom `π_S' : S' →+* κ` as
  --   `S' --(includeRight)--> A_m ⊗[A_f] S' --(iso.symm)--> S --g--> κ`.
  -- Its kernel is a prime ideal of `S'` lying over the prime `m·A_f` of `A_f`.
  -- ====================================================================
  haveI : (IsLocalRing.maximalIdeal (Localization.AtPrime m)).IsMaximal :=
    IsLocalRing.maximalIdeal.isMaximal _
  haveI : Field (Localization.AtPrime m ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime m)) :=
    Ideal.Quotient.field _
  let π_S' : S' →+*
      (Localization.AtPrime m ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime m)) :=
    g.toRingHom.comp (iso.symm.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := Localization.Away f) (A := Localization.AtPrime m) (B := S')).toRingHom)
  let q : Ideal S' := RingHom.ker π_S'
  haveI hq_prime : q.IsPrime := RingHom.ker_isPrime π_S'
  -- ====================================================================
  -- Steps 3–5 (prime-avoidance + cover + retraction assembly).
  --
  -- Outline (per `iter/iter-019/plan.md` Decision 1, the local-ring case-split route):
  -- (a) `Algebra.Etale.finite_primesOver` enumerates `{q₁ = q, q₂, …, qₙ}`, all primes
  --     of `S'` over `m·A_f`.
  -- (b) `exists_mem_finset_inf_notMem_of_isPrime` picks `g₁ ∈ S'` with `g₁ ∉ q` and
  --     `g₁ ∈ qᵢ` for `i ≥ 2`. Then `q` is the unique prime of `S'_{g₁}` over `m`.
  -- (c) `C := Localization.Away g₁` (as `S'`-algebra, hence `A`-algebra via the tower
  --     `A → A_f → S' → S'_{g₁}`); it is étale over `A` (composition of étale maps).
  -- (d) `Algebra.Etale.exists_explicit_ff_etale_product_cover_of_prime_over` (helper
  --     just above) applied to `(m, C, hCm)` yields `E`, `Algebra.Etale A (C × E)`,
  --     and `Module.FaithfullyFlat A (C × E)`.
  -- (e) `hret (C × E)` yields `σ' : C × E →ₐ[A] A`.
  -- (f) Compose with `A → A_m` to obtain `σ'_m : C × E →ₐ[A] A_m` (codomain is local).
  -- (g) `AlgHom.exists_section_of_isLocalRing σ'_m` case-splits:
  --     * C-branch: `σ_C : C →ₐ[A] A_m`, transferred to `A_f`-linear, then via
  --       `Algebra.TensorProduct.lift` against `iso` we get `σ : S →ₐ[A_m] A_m`.
  --       Residue compatibility follows from `q ↔ ker g` correspondence.
  --     * E-branch: per Decision 2 of `iter/iter-019/plan.md`, the only sanctioned
  --       partial close this iter is a typed sorry restricted to this branch.
  --
  -- ====================================================================
  -- Step (a) — A-algebra structure on S' via the tower A → A_f → S' and
  -- étaleness of A → S' by composing the two étale maps.
  -- ====================================================================
  letI algAS' : Algebra A S' :=
    ((algebraMap (Localization.Away f) S').comp
      (algebraMap A (Localization.Away f))).toAlgebra
  haveI istAAfS' : IsScalarTower A (Localization.Away f) S' :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI hEtaleAAf : Algebra.Etale A (Localization.Away f) :=
    Algebra.Etale.of_isLocalizationAway f
  haveI hEtaleAS' : Algebra.Etale A S' :=
    Algebra.Etale.comp A (Localization.Away f) S'
  -- ====================================================================
  -- Step (a) cont'd — `q` lies over `m` in `A`.
  -- The composite `π_S'` sends `algebraMap A S' x` to the residue of `x`
  -- in `κ(m) = A_m / m·A_m`. Hence its kernel pulls back to `m`.
  -- ====================================================================
  have hq_over_m : q.comap (algebraMap A S') = m := by
    -- We identify the composite ring hom `A → S' → κ(m)` (whose kernel is
    -- `q.comap (algebraMap A S')`) with `A → A_m → A_m / max(A_m) = κ(m)`
    -- (whose kernel is `m` by `IsLocalization.AtPrime.comap_maximalIdeal`).
    --
    -- Identifications used:
    --   `Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap` swaps the
    --     left and right include maps after composing with the base algebraMap.
    --   `iso.symm.commutes` (since `iso` is A_m-linear).
    --   `g.commutes` (since `g` is A_m-linear).
    --   `_instTower : IsScalarTower (Loc.Away f) (Loc.AtPrime m) S` gives
    --     `algMap A_f S = algMap A_m S ∘ algMap A_f A_m`.
    --   `IsLocalization.AtPrime.comap_maximalIdeal` closes the kernel computation
    --     for `A → A_m → A_m/max(A_m)`.
    classical
    -- Step (i): show the composite ring hom `S' → κ` is `A_f`-linear by composing
    -- through `S`. As an `A_f`-ring hom we'll use that
    --   `algMap A_f κ z = g (algMap A_f S z)`
    -- for `z : A_f`, where the RHS is the composite via `_instAfS` + the residue.
    -- Since `g` is A_m-linear and `algMap A_f S = algMap A_m S ∘ algMap A_f A_m`
    -- by `_instTower`, applying `g.commutes` gives the equation.
    --
    -- Step (ii): the same composite via the tensor product. Use
    -- `Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap` to identify
    -- `includeRight ∘ algMap A_f S'` with `includeLeftRingHom ∘ algMap A_f A_m`,
    -- and `iso.symm.commutes` to transport through to `algMap A_f S` directly.
    -- ----------------------------------------------------------------
    -- The structural gap: identifying `algMap A_f A_m ∘ algMap A A_f`
    -- with `algMap A A_m`. This is precisely the missing
    -- `IsScalarTower A (Loc.Away f) (Loc.AtPrime m)` instance — the descent
    -- proof constructs `_instAfAm` as `(IsLocalization.Away.lift f hf_unit).toAlgebra`,
    -- but the descent statement does not expose this scalar-tower compatibility.
    -- Without modifying `IndSpreads.lean` to expose the IsScalarTower data,
    -- we cannot conclude this identification.
    -- We provide the full reduction chain to the IsScalarTower equation
    -- as the only remaining structural sorry below.
    have key_Af : ∀ z : Localization.Away f,
        π_S' (algebraMap (Localization.Away f) S' z) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime m))
          (algebraMap (Localization.Away f) (Localization.AtPrime m) z) := by
      intro z
      -- Compute `π_S' (algMap A_f S' z)` step by step.
      -- π_S' = g ∘ iso.symm ∘ includeRight (as functions).
      show g (iso.symm (Algebra.TensorProduct.includeRight
        (R := Localization.Away f) (A := Localization.AtPrime m) (B := S')
        (algebraMap (Localization.Away f) S' z))) = _
      -- Step 1: includeRight ∘ algMap A_f S' = includeLeftRingHom ∘ algMap A_f A_m.
      have hswap : ∀ y : Localization.Away f,
          (Algebra.TensorProduct.includeRight (R := Localization.Away f)
              (A := Localization.AtPrime m) (B := S'))
            (algebraMap (Localization.Away f) S' y) =
          Algebra.TensorProduct.includeLeftRingHom
            (algebraMap (Localization.Away f) (Localization.AtPrime m) y) := by
        intro y
        have := (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
          (R := Localization.Away f) (A := Localization.AtPrime m) (B := S')).symm
        exact congr_arg (fun (φ : (Localization.Away f) →+* _) => φ y) this
      rw [hswap z]
      -- Step 2: includeLeftRingHom w = algMap A_m (A_m ⊗ S') w (definitionally).
      -- Step 3: iso.symm.commutes — iso.symm (algMap A_m _ w) = algMap A_m S w.
      have hcomm_iso : iso.symm
          (Algebra.TensorProduct.includeLeftRingHom
            (algebraMap (Localization.Away f) (Localization.AtPrime m) z)) =
          algebraMap (Localization.AtPrime m) S
            (algebraMap (Localization.Away f) (Localization.AtPrime m) z) :=
        AlgEquiv.commutes iso.symm _
      rw [hcomm_iso]
      -- Step 4: g.commutes — g (algMap A_m S w) = algMap A_m κ w.
      rw [AlgHom.commutes g]
      -- Step 5: algMap A_m κ = Ideal.Quotient.mk (max A_m) — and
      -- algMap A_f κ z = algMap A_m κ (algMap A_f A_m z) by IsScalarTower (auto).
      rfl
    -- Step (iii): now identify `q.comap (algMap A S')` with
    -- `m.comap (algMap A A_m)` via the chain
    -- A → A_f → S' → κ ≡ A → A_f → A_m → κ.
    ext x
    simp only [Ideal.mem_comap, q, RingHom.mem_ker]
    -- `algebraMap A S' x = algebraMap A_f S' (algebraMap A A_f x)` (by algAS' def).
    have halg : (algebraMap A S' : A →+* S') x =
        algebraMap (Localization.Away f) S' (algebraMap A (Localization.Away f) x) := rfl
    rw [halg, key_Af]
    -- Need: Quotient.mk (max A_m) (algMap A_f A_m (algMap A A_f x)) = 0 ↔ x ∈ m.
    rw [Ideal.Quotient.eq_zero_iff_mem]
    -- ↔ algMap A_f A_m (algMap A A_f x) ∈ max(A_m).
    -- For x ∈ m: by IsLocalization.AtPrime.map_eq_maximalIdeal, m maps into max(A_m).
    -- For x ∉ m: f := algMap A A_f x maps to a unit in A_m... but this composite
    -- depends on the structure of _instAfAm which is opaque after `obtain`.
    -- ============================================================================
    -- THE STRUCTURAL GAP (iter-021): the descent's `_instAfAm` is constructed as
    -- `(IsLocalization.Away.lift f hf_unit).toAlgebra` inside the descent proof,
    -- but the IsScalarTower A (Loc.Away f) (Loc.AtPrime m) compatibility is not
    -- exposed in the descent statement. To close this, the descent in
    -- `IndSpreads.lean` needs to additionally return
    -- `IsScalarTower R (Loc.Away f) (Loc.AtPrime m)` (or the equivalent
    -- `(algebraMap A_f A_m).comp (algebraMap A A_f) = algebraMap A A_m`).
    -- ============================================================================
    have hscalar : algebraMap (Localization.Away f) (Localization.AtPrime m)
        (algebraMap A (Localization.Away f) x) = algebraMap A (Localization.AtPrime m) x := by
      exact (IsScalarTower.algebraMap_apply A (Localization.Away f)
        (Localization.AtPrime m) x).symm
    rw [hscalar]
    -- Now reduce to IsLocalization.AtPrime.comap_maximalIdeal.
    have hcomap_max : Ideal.comap (algebraMap A (Localization.AtPrime m))
        (IsLocalRing.maximalIdeal (Localization.AtPrime m)) = m :=
      IsLocalization.AtPrime.comap_maximalIdeal
        (R := A) (S := Localization.AtPrime m) (I := m)
    constructor
    · intro hmem
      have hx_comap : x ∈ Ideal.comap (algebraMap A (Localization.AtPrime m))
          (IsLocalRing.maximalIdeal (Localization.AtPrime m)) := hmem
      rwa [hcomap_max] at hx_comap
    · intro hmem
      show algebraMap A (Localization.AtPrime m) x ∈ IsLocalRing.maximalIdeal _
      have : x ∈ Ideal.comap (algebraMap A (Localization.AtPrime m))
          (IsLocalRing.maximalIdeal (Localization.AtPrime m)) := by
        rw [hcomap_max]; exact hmem
      exact this
  haveI hq_liesOver : q.LiesOver m := ⟨hq_over_m.symm⟩
  -- ====================================================================
  -- Step (a) cont'd — finite set of primes of `S'` over `m`.
  -- ====================================================================
  have hfin_primes : (m.primesOver S').Finite :=
    Algebra.Etale.finite_primesOver S' m
  classical
  let primeSet : Finset (Ideal S') := hfin_primes.toFinset.erase q
  -- ====================================================================
  -- Step (b) — Prime avoidance.
  --
  -- For each prime `q' ∈ primeSet`, `q' ⊄ q`. (Both lie over the maximal
  -- ideal `m` in the étale extension `A → S'`. By the unramified
  -- structure / dimension argument, both are maximal in `S'`, hence
  -- incomparable; distinct maximal ideals never contain each other.)
  -- ====================================================================
  have hnotle : ∀ q' ∈ primeSet, ¬ q' ≤ q := by
    -- Strategy: primes of `S'` lying over `m` are maximal (fibre argument:
    -- `m.Fiber S' = m.ResidueField ⊗_A S'` is étale over the field
    -- `m.ResidueField`, hence a finite product of finite separable extensions,
    -- hence Artinian; and an Artinian ring has all primes maximal).
    -- We use `m.ResidueField` (which carries a `Field` instance natively,
    -- avoiding diamond issues with `A/m`).
    -- m.Fiber S' is Module.Finite over m.ResidueField, hence Artinian.
    haveI hFiberEtale : Algebra.Etale m.ResidueField (m.Fiber S') :=
      Algebra.Etale.baseChange A S' m.ResidueField
    haveI hFiberFinite : Module.Finite m.ResidueField (m.Fiber S') := by
      obtain ⟨I, hfin, Ai, hField, hAlg, e, hprod⟩ :=
        (Algebra.Etale.iff_exists_algEquiv_prod m.ResidueField (m.Fiber S')).mp hFiberEtale
      haveI : Finite I := hfin
      letI : ∀ i, Field (Ai i) := hField
      letI : ∀ i, Algebra m.ResidueField (Ai i) := hAlg
      haveI : ∀ i, Module.Finite m.ResidueField (Ai i) := fun i => (hprod i).1
      haveI : Module.Finite m.ResidueField (∀ i, Ai i) := Module.Finite.pi
      exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
    haveI hFiberArt : IsArtinianRing (m.Fiber S') :=
      (Module.finite_iff_isArtinianRing m.ResidueField _).mp hFiberFinite
    -- Order iso: primes of S' over m ↔ primes of m.Fiber S'.
    haveI hmPrime : m.IsPrime := ‹m.IsMaximal›.isPrime
    let φ := PrimeSpectrum.primesOverOrderIsoFiber A S' m
    -- Helper: any prime of S' lying over m is maximal-among-primes-over-m,
    -- hence maximal in S' (since any larger prime would also lie over m by
    -- maximality of m, contradicting top-ness in the order iso).
    have hmax : ∀ {p : Ideal S'}, (hp : p.IsPrime) → p.LiesOver m → p.IsMaximal := by
      intro p hp_prime hp_liesOver
      have hp_mem : p ∈ m.primesOver S' := ⟨hp_prime, hp_liesOver⟩
      -- Top-ness in the fibre: the image in PrimeSpectrum(m.Fiber S') is maximal there.
      let pFib : PrimeSpectrum (m.Fiber S') := φ ⟨p, hp_mem⟩
      haveI hpFib_max : pFib.asIdeal.IsMaximal :=
        IsArtinianRing.isMaximal_of_isPrime pFib.asIdeal
      -- Show p.IsMaximal in S'.
      refine ⟨⟨hp_prime.ne_top, ?_⟩⟩
      intro J hJ_lt
      -- J ⊋ p, want J = ⊤.
      by_contra hJ_top
      -- J ≠ ⊤; take a maximal ideal q containing J. q is prime, q ⊋ p (since J ⊋ p).
      obtain ⟨qmax, hqmax_max, hqmax_le⟩ := Ideal.exists_le_maximal J hJ_top
      have hp_lt_qmax : p < qmax := lt_of_lt_of_le hJ_lt hqmax_le
      -- qmax lies over a prime of A containing m (since p ⊆ qmax, m = comap p ⊆ comap qmax).
      have hqmax_prime : qmax.IsPrime := hqmax_max.isPrime
      have hcomap_le : m ≤ qmax.comap (algebraMap A S') := by
        have heq : m = qmax.comap (algebraMap A S') ⊓ m :=
          le_antisymm
            (le_inf
              (hp_liesOver.over ▸ Ideal.comap_mono hp_lt_qmax.le : m ≤ Ideal.under A qmax) le_rfl)
            inf_le_right
        exact heq ▸ inf_le_left
      -- m is maximal in A and comap qmax is prime ≠ ⊤, so comap qmax = m.
      have hcomap_prime : (qmax.comap (algebraMap A S')).IsPrime := hqmax_prime.comap _
      have hcomap_ne_top : qmax.comap (algebraMap A S') ≠ ⊤ := hcomap_prime.ne_top
      have hcomap_eq : qmax.comap (algebraMap A S') = m :=
        (‹m.IsMaximal›.eq_of_le hcomap_ne_top hcomap_le).symm
      -- So qmax ∈ m.primesOver S'.
      have hqmax_liesOver : qmax.LiesOver m := ⟨hcomap_eq.symm⟩
      have hqmax_mem : qmax ∈ m.primesOver S' := ⟨hqmax_prime, hqmax_liesOver⟩
      -- Compare in the fibre: φ⟨p,_⟩ < φ⟨qmax,_⟩ since p < qmax.
      have hφ_lt : φ ⟨p, hp_mem⟩ < φ ⟨qmax, hqmax_mem⟩ := by
        apply φ.lt_iff_lt.mpr
        exact (Subtype.mk_lt_mk).mpr hp_lt_qmax
      -- But φ⟨p,_⟩ = pFib is maximal, so this is a contradiction.
      have : pFib < φ ⟨qmax, hqmax_mem⟩ := hφ_lt
      -- pFib is maximal, so its prime ideal is the unique top, so nothing > it.
      have h_not_top : pFib.asIdeal < (φ ⟨qmax, hqmax_mem⟩).asIdeal := this
      have heq : pFib.asIdeal = (φ ⟨qmax, hqmax_mem⟩).asIdeal :=
        hpFib_max.eq_of_le (φ ⟨qmax, hqmax_mem⟩).isPrime.ne_top h_not_top.le
      exact absurd heq h_not_top.ne
    have hq_max : q.IsMaximal := hmax hq_prime hq_liesOver
    intro q' hq'
    have hq'_ne : q' ≠ q := (Finset.mem_erase.mp hq').1
    have hq'_mem : q' ∈ m.primesOver S' :=
      hfin_primes.mem_toFinset.mp (Finset.mem_erase.mp hq').2
    obtain ⟨hq'_prime, hq'_liesOver⟩ := hq'_mem
    have hq'_max : q'.IsMaximal := hmax hq'_prime hq'_liesOver
    intro hle
    exact hq'_ne (hq'_max.eq_of_le hq_max.ne_top hle)
  obtain ⟨g₁, hg₁_notmem_q, hg₁_mem_all⟩ :=
    exists_mem_finset_inf_notMem_of_isPrime (f := id) (s := primeSet) (q := q) hnotle
  -- ====================================================================
  -- Step (c) — Localize `S'` at `g₁` to obtain `C := S'_{g₁}`.
  -- Provide its A-algebra structure via the tower
  --   `A → A_f → S' → S'_{g₁}`
  -- and Étaleness via two applications of `Algebra.Etale.comp`.
  -- ====================================================================
  -- The canonical `Algebra A (Localization.Away g₁)` is provided by Mathlib
  -- via `OreLocalization.instAlgebra`, given the `Algebra A S'` above and
  -- the `S'`-algebra structure on `Localization.Away g₁`.
  haveI hEtaleS'C : Algebra.Etale S' (Localization.Away g₁) :=
    Algebra.Etale.of_isLocalizationAway (R := S') (A := Localization.Away g₁) g₁
  haveI hEtaleAC : Algebra.Etale A (Localization.Away g₁) :=
    Algebra.Etale.comp A S' (Localization.Away g₁)
  -- Now alias `C` to the localization for downstream uses.
  let C : Type u := Localization.Away g₁
  -- ====================================================================
  -- Step (c) cont'd — Witness a prime of `C` lying over `m`.
  -- Concretely: `q` survives in the localization `S'_{g₁}` because
  -- `g₁ ∉ q`, so `q · C` is a proper prime of `C` over `m`.
  -- ====================================================================
  have hCm : ∃ p : Ideal C, p.IsPrime ∧ p.comap (algebraMap A C) = m := by
    -- Powers of `g₁` are disjoint from `q` since `g₁ ∉ q` and `q` is prime.
    have hDisj : Disjoint ((Submonoid.powers g₁ : Submonoid S') : Set S') (q : Set S') := by
      rw [Set.disjoint_iff]
      rintro x ⟨⟨n, rfl⟩, hxq⟩
      exact hg₁_notmem_q (hq_prime.mem_of_pow_mem n hxq)
    let p : Ideal C := Ideal.map (algebraMap S' C) q
    refine ⟨p, ?_, ?_⟩
    · -- `p = q · C` is prime since `q.IsPrime` and powers of `g₁` ∉ q.
      exact IsLocalization.isPrime_of_isPrime_disjoint
        (Submonoid.powers g₁) C q hq_prime hDisj
    · -- `p.comap (algebraMap A C) = m`.
      have hcomap_S' : Ideal.comap (algebraMap S' C) p = q :=
        IsLocalization.under_map_of_isPrime_disjoint
          (Submonoid.powers g₁) C hq_prime hDisj
      -- `algebraMap A C` factors as `(algebraMap S' C).comp (algebraMap A S')`.
      -- We need `(algebraMap A C).comp ... = (algebraMap S' C).comp (algebraMap A S')`,
      -- which holds via `IsScalarTower`. Concretely:
      haveI istASC' : IsScalarTower A S' C := inferInstance
      have hAC_factor : (algebraMap A C : A →+* C) =
          (algebraMap S' C).comp (algebraMap A S') :=
        IsScalarTower.algebraMap_eq A S' C
      have hcomap_eq :
          Ideal.comap (algebraMap A C) p =
            Ideal.comap (algebraMap A S') (Ideal.comap (algebraMap S' C) p) := by
        rw [hAC_factor, ← Ideal.comap_comap]
      rw [hcomap_eq, hcomap_S', hq_over_m]
  -- ====================================================================
  -- Step (d) — Apply the explicit étale faithfully flat cover helper.
  -- ====================================================================
  obtain ⟨E, _instERing, _instEAlg, _instEEtale, hEtaleCE, hFFCE⟩ :=
    Algebra.Etale.exists_explicit_ff_etale_product_cover_of_prime_over m C hCm
  -- ====================================================================
  -- Step (e) — Apply the retraction hypothesis to the cover `C × E`.
  -- ====================================================================
  obtain ⟨σ', _⟩ := hret (C × E)
  -- ====================================================================
  -- Step (f) — Post-compose with `A → A_m` to land in the local ring.
  -- ====================================================================
  let σ_m : C × E →ₐ[A] Localization.AtPrime m :=
    (IsScalarTower.toAlgHom A A (Localization.AtPrime m)).comp σ'
  -- ====================================================================
  -- Step (g) — Local-ring case-split on the product target.
  -- ====================================================================
  rcases AlgHom.exists_section_of_isLocalRing σ_m with ⟨h_inl, _hfact⟩ | ⟨h_inr, _hfact⟩
  · -- C-branch: build `σ : S →ₐ[A_m] A_m` via `Algebra.TensorProduct.lift`.
    -- Step (i): σ_C : C →ₐ[A] A_m.
    let σ_C : C →ₐ[A] Localization.AtPrime m := σ_m.compFstSection h_inl
    -- Step (ii): The underlying ring hom σ_S' : S' →+* A_m.
    let σ_S'_ring : S' →+* Localization.AtPrime m :=
      σ_C.toRingHom.comp (algebraMap S' C)
    -- Step (iii): σ_S'_ring is A_f-linear: its precomposition with `algMap A_f S'`
    -- equals `algMap A_f A_m`. Both are ring homs `A_f → A_m`; they agree on the
    -- image of `A → A_f` (LHS: A-linearity of σ_C plus the scalar towers A → A_f → S'
    -- and A → S' → C; RHS: the new `_instRAfAm` tower). `IsLocalization.ringHom_ext`
    -- at `Submonoid.powers f` then gives equality.
    have hAfLinear : σ_S'_ring.comp (algebraMap (Localization.Away f) S') =
        (algebraMap (Localization.Away f) (Localization.AtPrime m) :
          Localization.Away f →+* Localization.AtPrime m) := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) ?_
      ext x
      show σ_C ((algebraMap S' C) ((algebraMap (Localization.Away f) S')
          ((algebraMap A (Localization.Away f)) x))) =
        algebraMap (Localization.Away f) (Localization.AtPrime m)
          ((algebraMap A (Localization.Away f)) x)
      rw [← IsScalarTower.algebraMap_apply A (Localization.Away f) S' x,
        ← IsScalarTower.algebraMap_apply A S' C x, σ_C.commutes x,
        ← IsScalarTower.algebraMap_apply A (Localization.Away f)
          (Localization.AtPrime m) x]
    -- Upgrade σ_S'_ring to an `A_f`-algebra hom.
    let σ_S'_alg : S' →ₐ[Localization.Away f] Localization.AtPrime m :=
      { toFun := σ_S'_ring
        map_one' := σ_S'_ring.map_one
        map_mul' := σ_S'_ring.map_mul
        map_zero' := σ_S'_ring.map_zero
        map_add' := σ_S'_ring.map_add
        commutes' := fun z => RingHom.congr_fun hAfLinear z }
    -- Step (iv): Build the lift `A_m ⊗[A_f] S' →ₐ[A_m] A_m` via TensorProduct.lift.
    haveI istAfAmAm : IsScalarTower (Localization.Away f)
        (Localization.AtPrime m) (Localization.AtPrime m) := IsScalarTower.right
    let σ_tensor :
        TensorProduct (Localization.Away f) (Localization.AtPrime m) S'
          →ₐ[Localization.AtPrime m] Localization.AtPrime m :=
      Algebra.TensorProduct.lift (AlgHom.id _ _) σ_S'_alg (fun _ _ => mul_comm _ _)
    -- Step (v): Pre-compose with iso to get σ_final : S →ₐ[A_m] A_m.
    let σ_final : S →ₐ[Localization.AtPrime m] Localization.AtPrime m :=
      σ_tensor.comp iso.toAlgHom
    refine ⟨σ_final, ?_⟩
    -- Step (vi): Residue compatibility.
    --
    -- We have to show that the two ring homs `S →+* A_m/max(A_m)`
    --   LHS := (Quotient.mk max) ∘ σ_final
    --   RHS := g
    -- are equal.
    --
    -- Strategy: Reduce to comparison on `S'` (the "right" factor of `A_m ⊗ S'`).
    -- Both LHS and RHS, viewed as `A_m`-algebra homs `S → κ` (where `κ = A_m/max`),
    -- agree on the image of `A_m` (the canonical residue map). It suffices to
    -- check agreement on the image of `S' → S` via `iso.symm ∘ includeRight`.
    --
    -- For RHS: `g ∘ iso.symm ∘ includeRight = π_S'` (by definition of `π_S'`).
    -- For LHS: `(Quotient.mk max) ∘ σ_final ∘ iso.symm ∘ includeRight =
    --          (Quotient.mk max) ∘ σ_tensor ∘ includeRight =
    --          (Quotient.mk max) ∘ σ̃_S' = (Quotient.mk max) ∘ σ_S'_ring`.
    -- So we reduce to: `∀ s : S', Quotient.mk max (σ_S'_ring s) = π_S' s`.
    --
    -- Both are ring homs `S' → κ`. Their kernels are: ker(π_S') = q by definition;
    -- ker((Quotient.mk max) ∘ σ_S'_ring) = (σ_C ∘ algMap S' C)⁻¹(max) = q since
    -- σ_C⁻¹(max) is the unique prime of `C` over `m` (= q·C, by the prime
    -- avoidance construction), and `(algMap S' C)⁻¹(q·C) = q` by `hcomap_S'`.
    -- Both factor through `S'/q`, and since `g : S → κ` is surjective realizing
    -- `S'/q ≅ κ` (as A_m-algebras), any other A_m-algebra hom `S'/q → κ` is
    -- forced to equal `g`. This is the substantive residue-compatibility step.
    --
    -- Reduce the equation to checking on `S` via composition with `iso`.
    -- iso is a ring iso, so equality of ring homs `S →+* κ` is equivalent to
    -- equality after composing with `iso.symm.toRingHom : (A_m ⊗ S') →+* S`.
    -- Then apply `Algebra.TensorProduct.ringHom_ext` to split into includeLeft
    -- (the A_m component, which is automatic from `g`'s A_m-linearity and
    -- `σ_final`'s A_m-linearity composed with `Quotient.mk` = canonical
    -- algebra map) and includeRight (the substantive S' component).
    set κ : Type u := Localization.AtPrime m ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime m)
    -- Reduce: equality of LHS and RHS as ring homs iff equality after composing
    -- with iso.symm.toAlgHom.toRingHom (since iso.symm is a ring iso).
    -- Equivalently, equality of `g.comp iso.symm.toRingHom` and
    -- `((Quotient.mk max).comp σ_final.toRingHom).comp iso.symm.toRingHom`.
    -- Apply Algebra.TensorProduct.ringHom_ext.
    have hsubst :
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime m))).comp
            σ_final.toRingHom).comp iso.symm.toAlgHom.toRingHom =
        g.toRingHom.comp iso.symm.toAlgHom.toRingHom := by
      refine Algebra.TensorProduct.ringHom_ext ?_ ?_
      · -- includeLeft component: A_m → A_m ⊗ S' → S → κ via both sides.
        ext a
        -- LHS: Q.mk(σ_final(iso.symm(a ⊗ 1))) = Q.mk(σ_tensor(a ⊗ 1)) = Q.mk(a · 1) = Q.mk(a).
        -- RHS: g(iso.symm(a ⊗ 1)) = g(algMap A_m S a) = Q.mk(a) (g is A_m-linear).
        show Ideal.Quotient.mk _ (σ_final (iso.symm
          (Algebra.TensorProduct.includeLeftRingHom a))) =
          g (iso.symm (Algebra.TensorProduct.includeLeftRingHom a))
        have hLHS : σ_final (iso.symm (Algebra.TensorProduct.includeLeftRingHom a)) = a := by
          show σ_tensor (iso (iso.symm (Algebra.TensorProduct.includeLeftRingHom a))) = a
          rw [AlgEquiv.apply_symm_apply]
          show Algebra.TensorProduct.lift (AlgHom.id _ _) σ_S'_alg _
              (Algebra.TensorProduct.includeLeftRingHom a) = a
          -- includeLeftRingHom a = a ⊗ 1, lift on a ⊗ 1 = (id a) * (σ_S'_alg 1) = a * 1 = a.
          show Algebra.TensorProduct.lift (AlgHom.id _ _) σ_S'_alg _ (a ⊗ₜ 1) = a
          rw [Algebra.TensorProduct.lift_tmul]
          simp
        have hRHS : g (iso.symm (Algebra.TensorProduct.includeLeftRingHom a)) =
            algebraMap (Localization.AtPrime m) κ a := by
          show g (iso.symm (a ⊗ₜ 1)) = _
          -- iso.symm (a ⊗ₜ 1) = algMap A_m S a (since iso is A_m-linear, iso.symm sends
          -- includeLeft to algMap).
          have : iso.symm (a ⊗ₜ[Localization.Away f] (1 : S')) =
              algebraMap (Localization.AtPrime m) S a := by
            have := AlgEquiv.commutes iso.symm a
            -- algMap A_m (A_m ⊗ S') a = a ⊗ₜ 1 (by definition of TensorProduct algebra map)
            -- so iso.symm (a ⊗ₜ 1) = iso.symm (algMap A_m (A_m ⊗ S') a) = algMap A_m S a.
            rw [show (a ⊗ₜ[Localization.Away f] (1 : S') :
                TensorProduct (Localization.Away f) (Localization.AtPrime m) S') =
                algebraMap (Localization.AtPrime m)
                  (TensorProduct (Localization.Away f) (Localization.AtPrime m) S') a from rfl]
            exact this
          rw [this, AlgHom.commutes]
        rw [hLHS, hRHS]
        rfl
      · -- includeRight component: S' → A_m ⊗ S' → S → κ via both sides.
        -- LHS: Q.mk(σ_final(iso.symm(1 ⊗ s'))) = Q.mk(σ_tensor(1 ⊗ s')) = Q.mk(σ_S'_alg s')
        --      = Q.mk(σ_S'_ring s').
        -- RHS: g(iso.symm(1 ⊗ s')) = π_S' s' by definition of π_S'.
        -- The substantive residue equation: Q.mk ∘ σ_S'_ring = π_S' as ring homs S' → κ.
        --
        -- This is the focused residue-matching step. The full argument:
        --   (a) Both ring homs are A_f-linear (LHS by hAfLinear; RHS by g's A_m-linearity).
        --   (b) Both are surjective onto κ (image contains image of algMap A_f κ which is
        --       all of κ since A_m → κ = Quotient.mk is surjective).
        --   (c) ker(LHS) = σ_S'_ring⁻¹(max). This is a prime of S' over m (computed via
        --       σ_S'_ring restricted to algMap A S' = algMap A A_m, then Quotient.mk).
        --       σ_S'_ring(g₁) is the image of g₁ under σ_C ∘ algMap S' C; g₁ inverts in C,
        --       so its image is a unit in A_m, hence not in max. So g₁ ∉ ker(LHS).
        --   (d) ker(RHS) = q by definition.
        --   (e) By the prime-avoidance setup, q is the unique prime of S' over m not
        --       containing g₁. Hence ker(LHS) = q.
        --   (f) Both factor through S'/q. S'/q ≅ κ via π_S' (surjective with trivial residue).
        --       Any A_m-algebra hom S'/q → κ equals π_S' since A_m → κ is surjective
        --       (Quotient.mk) and hence Aut(κ/A_m) = {id}.
        --
        -- Below: build up the key auxiliary facts (h agrees with algMap A κ on
        -- algMap A S'; σ_S'_ring g₁ is a unit; h surjective with kernel a prime
        -- of S' over m), then leave the final kernel-uniqueness + same-kernel
        -- conclusion as a focused sorry.
        set h_ring : S' →+* κ :=
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime m))).comp σ_S'_ring
        -- (a) h_ring agrees with algMap A κ on the image of A → S'.
        have h_on_A : h_ring.comp (algebraMap A S') =
            (algebraMap A κ : A →+* κ) := by
          ext a
          show (Ideal.Quotient.mk _) (σ_C (algebraMap S' C ((algebraMap A S') a))) =
            algebraMap A κ a
          rw [← IsScalarTower.algebraMap_apply A S' C, σ_C.commutes]
          exact (IsScalarTower.algebraMap_apply A (Localization.AtPrime m) κ a).symm
        -- (b) σ_S'_ring g₁ is a unit in A_m (because g₁ is inverted in C).
        have hg₁_unit_in_Am : IsUnit (σ_S'_ring g₁) := by
          show IsUnit (σ_C (algebraMap S' C g₁))
          exact (IsLocalization.Away.algebraMap_isUnit (S := C) g₁).map σ_C.toRingHom
        -- (c) Hence g₁ ∉ ker(h_ring): h_ring g₁ ≠ 0 in κ.
        have hg₁_not_in_ker_h : g₁ ∉ RingHom.ker h_ring := by
          intro hmem
          have hh : h_ring g₁ = 0 := hmem
          have : σ_S'_ring g₁ ∈ IsLocalRing.maximalIdeal (Localization.AtPrime m) :=
            Ideal.Quotient.eq_zero_iff_mem.mp hh
          exact (IsLocalRing.notMem_maximalIdeal.mpr hg₁_unit_in_Am) this
        -- iter-024 Lane A: the residue equation. Strategy: reduce the includeRight
        -- subgoal to `h_ring = π_S' : S' →+* κ`, then prove the latter via the
        -- 7-step kernel-uniqueness chain (a-mirror / surjectivity / ker maximal /
        -- ker over m / ker ∈ primesOver / ker = q / pointwise conclude).
        suffices h_eq_π : h_ring = π_S' by
          ext s'
          show (Ideal.Quotient.mk _)
              (σ_final (iso.symm (Algebra.TensorProduct.includeRight
                (R := Localization.Away f) (A := Localization.AtPrime m) (B := S') s'))) =
              g (iso.symm (Algebra.TensorProduct.includeRight
                (R := Localization.Away f) (A := Localization.AtPrime m) (B := S') s'))
          have hLHS : σ_final (iso.symm (Algebra.TensorProduct.includeRight
              (R := Localization.Away f) (A := Localization.AtPrime m) (B := S') s')) =
              σ_S'_ring s' := by
            show σ_tensor (iso (iso.symm
              (Algebra.TensorProduct.includeRight s'))) = _
            rw [AlgEquiv.apply_symm_apply]
            show Algebra.TensorProduct.lift (AlgHom.id _ _) σ_S'_alg _
              ((1 : Localization.AtPrime m) ⊗ₜ s') = σ_S'_ring s'
            rw [Algebra.TensorProduct.lift_tmul]
            show (AlgHom.id (Localization.AtPrime m) (Localization.AtPrime m)) 1 *
              σ_S'_alg s' = σ_S'_ring s'
            rw [AlgHom.id_apply, one_mul]
            rfl
          rw [hLHS]
          exact RingHom.congr_fun h_eq_π s'
        -- (a-mirror) π_S' agrees with `algebraMap A κ` on the image of `A → S'`.
        have π_on_A : π_S'.comp (algebraMap A S') = (algebraMap A κ : A →+* κ) := by
          ext a
          show g (iso.symm (Algebra.TensorProduct.includeRight
              (R := Localization.Away f) (A := Localization.AtPrime m) (B := S')
              ((algebraMap A S' : A →+* S') a))) = algebraMap A κ a
          -- `algebraMap A S' a = algebraMap A_f S' (algebraMap A A_f a)` (from algAS').
          show g (iso.symm (Algebra.TensorProduct.includeRight
              (R := Localization.Away f) (A := Localization.AtPrime m) (B := S')
              (algebraMap (Localization.Away f) S'
                (algebraMap A (Localization.Away f) a)))) = algebraMap A κ a
          rw [show (Algebra.TensorProduct.includeRight (R := Localization.Away f)
                  (A := Localization.AtPrime m) (B := S'))
                  (algebraMap (Localization.Away f) S'
                    (algebraMap A (Localization.Away f) a)) =
                Algebra.TensorProduct.includeLeftRingHom
                  (algebraMap (Localization.Away f) (Localization.AtPrime m)
                    (algebraMap A (Localization.Away f) a)) from
              congr_arg (fun (φ : (Localization.Away f) →+* _) => φ _)
                (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
                  (R := Localization.Away f) (A := Localization.AtPrime m)
                  (B := S')).symm]
          rw [show iso.symm (Algebra.TensorProduct.includeLeftRingHom
                (algebraMap (Localization.Away f) (Localization.AtPrime m)
                  (algebraMap A (Localization.Away f) a))) =
                algebraMap (Localization.AtPrime m) S
                  (algebraMap (Localization.Away f) (Localization.AtPrime m)
                    (algebraMap A (Localization.Away f) a)) from
              AlgEquiv.commutes iso.symm _]
          rw [AlgHom.commutes,
              ← IsScalarTower.algebraMap_apply A (Localization.Away f)
                (Localization.AtPrime m) a,
              ← IsScalarTower.algebraMap_apply A (Localization.AtPrime m) κ a]
        -- (b-bridge) `algebraMap A κ` is surjective (via `equivQuotMaximalIdeal`).
        have hAκ_surj : Function.Surjective (algebraMap A κ : A → κ) := by
          intro k
          obtain ⟨amclass, ha⟩ :=
            (IsLocalization.AtPrime.equivQuotMaximalIdeal m
              (Localization.AtPrime m)).surjective k
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective amclass
          rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk] at ha
          exact ⟨a, by rw [← Ideal.Quotient.mk_algebraMap]; exact ha⟩
        -- (b) h_ring is surjective: lift via hAκ_surj + h_on_A.
        have h_surj : Function.Surjective h_ring := by
          intro k
          obtain ⟨a, rfl⟩ := hAκ_surj k
          exact ⟨algebraMap A S' a, RingHom.congr_fun h_on_A a⟩
        -- (c) ker h_ring is prime (via comap of the maximal ideal of A_m, sidestepping
        -- the Field/Quotient.semiring diamond on κ).
        have hker_eq_comap : RingHom.ker h_ring =
            (IsLocalRing.maximalIdeal (Localization.AtPrime m)).comap σ_S'_ring := by
          show RingHom.ker
            ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime m))).comp
              σ_S'_ring) = _
          rw [← RingHom.comap_ker]
          congr 1
          exact Ideal.mk_ker
        haveI hmax_prime :
            (IsLocalRing.maximalIdeal (Localization.AtPrime m)).IsPrime :=
          (IsLocalRing.maximalIdeal.isMaximal _).isPrime
        haveI hker_prime : (RingHom.ker h_ring).IsPrime := by
          rw [hker_eq_comap]; infer_instance
        -- (d) (ker h_ring).under A = m.
        have hker_under_m : (RingHom.ker h_ring).under A = m := by
          ext a
          rw [Ideal.mem_under, RingHom.mem_ker,
              show h_ring (algebraMap A S' a) = algebraMap A κ a from
                RingHom.congr_fun h_on_A a,
              ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          constructor
          · intro hmem
            have h2 : a ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime m)).under A := hmem
            rwa [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime m) m] at h2
          · intro hmem
            have h2 : a ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime m)).under A := by
              rw [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime m) m]
              exact hmem
            exact h2
        -- (e) ker h_ring ∈ m.primesOver S'.
        haveI hker_liesOver : (RingHom.ker h_ring).LiesOver m := ⟨hker_under_m.symm⟩
        have hker_in_primesOver : RingHom.ker h_ring ∈ m.primesOver S' :=
          ⟨hker_prime, hker_liesOver⟩
        have hker_mem_toFinset : RingHom.ker h_ring ∈ hfin_primes.toFinset :=
          hfin_primes.mem_toFinset.mpr hker_in_primesOver
        -- (f) ker h_ring = q (by prime-avoidance: any other element of primesOver
        -- would contain g₁, contradicting hg₁_not_in_ker_h).
        have hker_eq_q : RingHom.ker h_ring = q := by
          by_contra hne
          have hin_erase : RingHom.ker h_ring ∈ primeSet :=
            Finset.mem_erase.mpr ⟨hne, hker_mem_toFinset⟩
          exact hg₁_not_in_ker_h (hg₁_mem_all _ hin_erase)
        -- (g) Conclude h_ring = π_S' as ring homs.
        ext s'
        obtain ⟨a, ha⟩ := hAκ_surj (π_S' s')
        -- s' - algMap A S' a ∈ ker π_S' = q
        have hdiff_in_q : s' - algebraMap A S' a ∈ q := by
          show π_S' (s' - algebraMap A S' a) = 0
          rw [map_sub]
          rw [show π_S' (algebraMap A S' a) = algebraMap A κ a from
                RingHom.congr_fun π_on_A a]
          rw [ha, sub_self]
        have hdiff_in_kerh : s' - algebraMap A S' a ∈ RingHom.ker h_ring := by
          rw [hker_eq_q]; exact hdiff_in_q
        have hsub_zero : h_ring (s' - algebraMap A S' a) = 0 := hdiff_in_kerh
        rw [map_sub, sub_eq_zero] at hsub_zero
        rw [hsub_zero,
            show h_ring (algebraMap A S' a) = algebraMap A κ a from
              RingHom.congr_fun h_on_A a, ha]
    -- Conclude the original equation by composing back via iso.
    ext s
    have heq := RingHom.congr_fun hsubst (iso s)
    show Ideal.Quotient.mk _ (σ_final s) = g s
    simpa using heq
  · -- E-branch: sanctioned typed sorry (per iter-020 Decision 1).
    sorry

/-- **lemma:retractions-strictly-henselian** (Blueprint): If every faithfully flat etale ring map
`A -> B` has a retraction, then every local ring `A_m` at a maximal ideal is strictly Henselian.

Both branches (HenselianLocalRing and IsSepClosed) reduce to
`exists_residue_compatible_section_of_retraction`; see that helper for the
underlying blueprint argument. -/
private lemma isStrictlyHenselianLocalRing_of_exists_retraction
    (A : Type u) [CommRing A]
    (hret : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
      [Module.FaithfullyFlat A B], ∃ σ : B →ₐ[A] A, True)
    (m : Ideal A) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
  haveI : IsLocalRing (Localization.AtPrime m) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime m) m
  set R : Type u := Localization.AtPrime m
  set I : Ideal R := IsLocalRing.maximalIdeal R
  -- For a local ring, `Ring.jacobson R = maximalIdeal R`.
  have hI_le_jac : I ≤ Ring.jacobson R := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
  -- HenselianLocalRing from HenselianRing R I via `henselian_if_exists_section`.
  -- The section hypothesis is exactly the helper above.
  have hHensRing : HenselianRing R I :=
    henselian_if_exists_section R I hI_le_jac
      (fun S _ _ _ g => exists_residue_compatible_section_of_retraction hret m S g)
  haveI hHens : HenselianLocalRing R := by
    refine HenselianLocalRing.mk fun f hf_monic a₀ hmem hunit => ?_
    -- HenselianRing's `is_henselian` uses `IsUnit ((Quotient.mk I) (eval a₀ f'))`,
    -- which is equivalent to `IsUnit (eval a₀ f')` in a local ring.
    have hunit_quot : IsUnit ((Ideal.Quotient.mk I) (Polynomial.eval a₀ f.derivative)) :=
      hunit.map _
    exact hHensRing.is_henselian f hf_monic a₀ hmem hunit_quot
  -- `IsSepClosed (κ(m))`: every monic separable polynomial over `κ(m) = R/I` has a root.
  refine { isSepClosed_residueField := ?_ }
  refine IsSepClosed.of_exists_root _ ?_
  intro f hf_monic hf_irr hf_sep
  -- Strategy (Blueprint `lemma:retractions-strictly-henselian`, IsSepClosed direction):
  --
  -- Step (a). Lift `f : (R/I)[X]` to a monic polynomial `ftilde : R[X]` of the same degree.
  -- Such a lift exists since `Ideal.Quotient.mk I` is surjective, hence
  -- `Polynomial.map (Ideal.Quotient.mk I)` is surjective on monic polynomials
  -- (`Polynomial.lifts_and_degree_eq_and_monic`).
  have hf_lifts : f ∈ Polynomial.lifts (Ideal.Quotient.mk I : R →+* R ⧸ I) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective f
  obtain ⟨ftilde, hftilde_map, _hftilde_deg, hftilde_monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hf_lifts hf_monic
  -- Step (b). Form the étale `R`-algebra `B := R[X]/(ftilde)`. Because `ftilde` is monic, this
  -- is `Module.Free R B` (`Polynomial.Monic.free_quotient`), and the reduction
  -- `B/IB ≃ (R/I)[X]/(f) = κ(m)[X]/(f)` is the finite separable residue extension.
  -- Faithfulness over `R` follows from `Module.Free R B` + the rank-positivity of
  -- a monic polynomial quotient.
  --
  -- Step (c). `B` is étale over `R`. The separability hypothesis `hf_sep` says that
  -- `f' * q₁ + f * q₂ = 1` for some `q₁, q₂ ∈ (R/I)[X]`. Lifting `q₁, q₂` to `R[X]`,
  -- this gives `ftilde' * q̃₁ + ftilde * q̃₂ = 1 + r` with `r ∈ I·R[X]`. Reducing mod `ftilde` in
  -- `B`, `ftilde'·(q̃₁ mod ftilde)` differs from `1` by an element of `I·B`. Since `R` is local
  -- with `I = maxIdeal R` and `B` is a finite `R`-module, the Jacobson radical of
  -- `B` contains `I·B`, so `ftilde'` is a unit mod `ftilde`. Hence `(R[X]/(ftilde))[1/1] = R[X]/(ftilde)`
  -- arises as `StandardEtalePair`-style étale, giving `Algebra.Etale R (R[X]/(ftilde))`.
  --
  -- Step (d). The hypothesis `hret` applied to `B = R[X]/(ftilde)` (which is the A-algebra
  -- via the structure map `A → R → B`, after upgrading `R = A_m` to `A` via the
  -- analogous descent of step 1 in `exists_residue_compatible_section_of_retraction`)
  -- yields a section `σ : B →ₐ[A] A`. Composing with the residue projection
  -- `A → A/m = κ(m)`, the image of `X̄` is a root of `f` in `κ(m)`.
  --
  -- The gap: hret takes A-algebras, but `R[X]/(ftilde)` is naturally an R = A_m algebra;
  -- the descent to an A-algebra via `A_f → R = A_m`, plus the natural cover step,
  -- mirrors the L390 assembly and is currently the same structural blocker.
  -- IsSepClosed reduces to L390 + Stacks 04GG = `bijective_localRingHom_of_strictlyHenselian`.
  -- See blueprint `local-structure.tex` `thm:etale-over-strictly-henselian-localization-isom`.
  -- The remaining step (assembling the section via descent + cover + retraction) is
  -- shared with L390 and is left as a structural sorry.
  -- Note: `hftilde_monic, hftilde_map` are the polynomial lifts; using them keeps the lift
  -- explicitly visible in the proof skeleton for future iterations.
  have _hftilde_data : ftilde.Monic ∧ ftilde.map (Ideal.Quotient.mk I) = f := ⟨hftilde_monic, hftilde_map⟩
  sorry

/-- **cor:strictly-henselian-etale-contraction** (Blueprint): For any maximal ideal `m` of
`IndEtaleContraction A`, the localization `(IndEtaleContraction A)_m` is strictly Henselian.

This follows from `prop:etale-contraction-retraction` (formalized as
`RingHom.Etale.exists_comp_eq_id_indContraction`) and `lemma:retractions-strictly-henselian`. -/
private lemma isStrictlyHenselianLocalRing_IndEtaleContraction
    (m : Ideal (IndEtaleContraction A)) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
  apply isStrictlyHenselianLocalRing_of_exists_retraction
  intro B _ _ hEtale hFF
  -- By prop:etale-contraction-retraction, every faithfully flat etale ring map out of
  -- IndEtaleContraction A has a retraction.
  -- The algebraMap is etale as a ring hom:
  have hf_etale : (algebraMap (IndEtaleContraction A) B).Etale :=
    RingHom.etale_algebraMap.mpr hEtale
  -- Faithfully flat implies surjective Spec map:
  have hf_surj : Function.Surjective
      (PrimeSpectrum.comap (algebraMap (IndEtaleContraction A) B)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  -- Apply exists_comp_eq_id_indContraction:
  obtain ⟨g, hg⟩ := RingHom.Etale.exists_comp_eq_id_indContraction
    (algebraMap (IndEtaleContraction A) B) hf_etale hf_surj
  -- g is a RingHom retraction: g ∘ algebraMap = id
  -- Convert g to an AlgHom:
  refine ⟨{ toRingHom := g, commutes' := fun r => ?_ }, trivial⟩
  -- Need: g (algebraMap r) = algebraMap r (where algebraMap : IndEtaleContraction A → IndEtaleContraction A = id)
  -- From hg: g ∘ algebraMap = RingHom.id, so g (algebraMap r) = r
  show g ((algebraMap (IndEtaleContraction A) B) r) =
    (algebraMap (IndEtaleContraction A) (IndEtaleContraction A)) r
  rw [show (algebraMap (IndEtaleContraction A) (IndEtaleContraction A)) r = r from rfl]
  exact RingHom.congr_fun hg r

lemma isStrictlyHenselianLocalRing_WLocalization_IndEtaleContraction
    (m : Ideal (WLocalization (IndEtaleContraction A))) (hm : m.IsMaximal) :
    @IsStrictlyHenselianLocalRing (Localization.AtPrime m) _ := by
  -- Proof outline (cor:strictly-henselian-etale-contraction in blueprint):
  --
  -- Step 1: The map `algebraMap (IndEtaleContraction A) (WLocalization (IndEtaleContraction A))`
  --   is `Algebra.IndZariski`, hence bijective on stalks (`Algebra.IndZariski.bijectiveOnStalks_algebraMap`).
  -- Step 2: The bijective stalk map at `m` yields a ring isomorphism
  --     `Localization.AtPrime (m.comap algebraMap) ≃+* Localization.AtPrime m`.
  -- Step 3: We would need `m.comap algebraMap` to be maximal in `IndEtaleContraction A`. Then
  --   `isStrictlyHenselianLocalRing_IndEtaleContraction` gives the source is strictly henselian.
  -- Step 4: Transfer strict-henselianity through the ring isomorphism.
  --
  -- GAP: Step 3 is not provable for the current definition. The closed points of
  -- `WLocalization B` correspond (via `bijOn_algebraMap_specComap_zeroLocus_ideal`) to ALL primes
  -- of `B`, not just maximal ideals. So `m.comap algebraMap` is generally just a prime, and the
  -- localization at a non-maximal prime of a strictly henselian local ring is NOT generally
  -- strictly henselian (e.g., the fraction field of the strict henselization of `ℤ_p` is not
  -- separably closed).
  --
  -- The blueprint resolves this by defining the w-strict-localization not as
  --   `WLocalization (IndEtaleContraction (WLocalization R))`,
  -- but as the additional localization
  --   `((T^∞(A_w))_w)_{V~(I (T^∞(A_w))_w)}`
  -- where `I` is the ideal cutting out the closed points of `A_w = WLocalization R`. See the
  -- blueprint remark in `local-structure.tex`, lines 1995–2008. Without that additional step,
  -- the current definition has "extra" maximal ideals whose localizations may not be strictly
  -- henselian.
  --
  -- Below we set up the structural pieces (Step 1–2) that are unconditionally available.
  haveI : m.IsPrime := hm.isPrime
  -- Step 1: get the bijective stalks instance.
  have hbij : (algebraMap (IndEtaleContraction A)
      (WLocalization (IndEtaleContraction A))).BijectiveOnStalks :=
    Algebra.IndZariski.bijectiveOnStalks_algebraMap (IndEtaleContraction A)
      (WLocalization (IndEtaleContraction A))
  -- Step 2: stalk bijection at this specific `m` gives a ring isomorphism
  --   `Localization.AtPrime (m.comap _) ≃+* Localization.AtPrime m`.
  set f : IndEtaleContraction A →+* WLocalization (IndEtaleContraction A) :=
    algebraMap (IndEtaleContraction A) (WLocalization (IndEtaleContraction A))
  have hφ_bij : Function.Bijective (Localization.localRingHom (m.comap f) m f rfl) := hbij m
  haveI : (m.comap f).IsPrime := Ideal.IsPrime.comap f
  let e : Localization.AtPrime (m.comap f) ≃+* Localization.AtPrime m :=
    RingEquiv.ofBijective (Localization.localRingHom (m.comap f) m f rfl) hφ_bij
  -- Step 3 (GAP): need `(m.comap f).IsMaximal`. Without it we cannot invoke
  -- `isStrictlyHenselianLocalRing_IndEtaleContraction`. The current definition of
  -- `WStrictLocalization` is missing the final "localize-at-V~(IB)" step from the blueprint
  -- which would force closed points of the outer `WLocalization` to lie over maximals of
  -- `IndEtaleContraction A`. See the blueprint remark in `local-structure.tex` lines 1995–2008.
  haveI hcomap_max : (m.comap f).IsMaximal := by sorry
  -- Step 4: given maximality, the source is strictly henselian by Cor.
  have hSH : IsStrictlyHenselianLocalRing (Localization.AtPrime (m.comap f)) :=
    isStrictlyHenselianLocalRing_IndEtaleContraction (m.comap f)
  -- Step 5: transfer via the ring iso `e`.
  exact isStrictlyHenselianLocalRing_of_ringEquiv e

end StrictlyHenselianWLocalizationOfIndEtaleContraction

-- def Precontraction

/-- The w-strict localization of `R`. The construction proceeds as follows:
1. Take the w-localization `WLocalization R` (w-local, ind-Zariski, faithfully flat over `R`).
2. Take its ind-étale contraction `IndEtaleContraction (WLocalization R)` (ind-étale, faithfully
   flat, with strictly Henselian maximal ideal localizations).
3. Take the w-localization of the result (to restore the w-local property, while the ind-Zariski
   map preserves the strictly Henselian stalks). -/
def WStrictLocalization (R : Type u) [CommRing R] : Type u :=
  WLocalization (IndEtaleContraction (WLocalization R))

variable (R : Type u) [CommRing R]

noncomputable instance : CommRing (WStrictLocalization R) :=
  inferInstanceAs <| CommRing (WLocalization (IndEtaleContraction (WLocalization R)))

noncomputable instance : Algebra R (WStrictLocalization R) :=
  ((algebraMap (IndEtaleContraction (WLocalization R))
      (WLocalization (IndEtaleContraction (WLocalization R)))).comp
    ((algebraMap (WLocalization R) (IndEtaleContraction (WLocalization R))).comp
      (algebraMap R (WLocalization R)))).toAlgebra

-- Intermediate algebra: R → IndEtaleContraction (WLocalization R) via WLocalization R.
private noncomputable instance algebraIndEtaleContraction :
    Algebra R (IndEtaleContraction (WLocalization R)) :=
  ((algebraMap (WLocalization R) (IndEtaleContraction (WLocalization R))).comp
    (algebraMap R (WLocalization R))).toAlgebra

-- The canonical algebra structure: IndEtaleContraction(WLoc R) → WStrictLocalization R
-- This is WLocalization.algebra for the intermediate ring.
private noncomputable instance algebraWStrictOfIndEtale :
    Algebra (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
  inferInstanceAs <| Algebra (IndEtaleContraction (WLocalization R))
    (WLocalization (IndEtaleContraction (WLocalization R)))

private instance scalarTower_WLoc :
    IsScalarTower R (WLocalization R) (IndEtaleContraction (WLocalization R)) :=
  IsScalarTower.of_algebraMap_eq' rfl

private instance scalarTower_IndEtale :
    IsScalarTower R (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
  IsScalarTower.of_algebraMap_eq' rfl

-- Composition of ind-Zariski (WLocalization) ∘ ind-étale (IndEtaleContraction) ∘ ind-Zariski
-- (WLocalization) is ind-étale. Uses `Algebra.IndEtale.trans` twice.
instance : Algebra.IndEtale R (WStrictLocalization R) := by
  -- Step 1: R → WLocalization R is ind-Zariski, hence ind-étale.
  -- Step 2: WLocalization R → IndEtaleContraction (WLocalization R) is ind-étale.
  -- By trans: R → IndEtaleContraction (WLocalization R) is ind-étale.
  have : Algebra.IndEtale R (IndEtaleContraction (WLocalization R)) :=
    Algebra.IndEtale.trans R (WLocalization R) (IndEtaleContraction (WLocalization R))
  -- Step 3: IndEtaleContraction (WLocalization R) → WStrictLocalization R is ind-Zariski, hence ind-étale.
  -- By trans: R → WStrictLocalization R is ind-étale.
  have : Algebra.IndEtale (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
    inferInstanceAs <| Algebra.IndEtale _ (WLocalization (IndEtaleContraction (WLocalization R)))
  exact Algebra.IndEtale.trans R (IndEtaleContraction (WLocalization R)) (WStrictLocalization R)

-- Composition of three faithfully flat maps. Uses `Module.FaithfullyFlat.trans` twice.
instance : Module.FaithfullyFlat R (WStrictLocalization R) := by
  -- Step 1: R → WLocalization R is faithfully flat.
  -- Step 2: WLocalization R → IndEtaleContraction (WLocalization R) is faithfully flat.
  -- By trans: R → IndEtaleContraction (WLocalization R) is faithfully flat.
  have : Module.FaithfullyFlat R (IndEtaleContraction (WLocalization R)) :=
    Module.FaithfullyFlat.trans R (WLocalization R) (IndEtaleContraction (WLocalization R))
  -- Step 3: IndEtaleContraction (WLocalization R) → WStrictLocalization R is faithfully flat.
  -- By trans: R → WStrictLocalization R is faithfully flat.
  have : Module.FaithfullyFlat (IndEtaleContraction (WLocalization R)) (WStrictLocalization R) :=
    WLocalization.faithfullyFlat (IndEtaleContraction (WLocalization R))
  exact Module.FaithfullyFlat.trans R (IndEtaleContraction (WLocalization R)) (WStrictLocalization R)

-- `IsWLocalRing` follows from the outer `WLocalization`. Strictly Henselian stalks at maximal
-- ideals: the `IndEtaleContraction` makes stalks of `WLocalization R` strictly Henselian, and
-- the outer `WLocalization` (being ind-Zariski) identifies local rings at closed points.
instance : IsWLocalRing (WStrictLocalization R) :=
  inferInstanceAs (IsWLocalRing (WLocalization (IndEtaleContraction (WLocalization R))))

instance : IsWStrictlyLocalRing (WStrictLocalization R) where
  -- Strictly Henselian stalks: the IndEtaleContraction makes stalks of WLocalization R
  -- strictly Henselian (cor:strictly-henselian-etale-contraction in blueprint), and the
  -- outer WLocalization (being ind-Zariski) identifies local rings at closed points
  -- (thm:ind-Zariski-identifies-local-rings in blueprint).
  -- This requires deep infrastructure not yet formalized.
  isStrictlyHenselianLocalRing_localization := fun m => by
    -- WStrictLocalization R = WLocalization (IndEtaleContraction (WLocalization R))
    -- m is a maximal ideal of this ring.
    -- Apply the helper lemma with A := WLocalization R.
    -- The types are definitionally equal, but we need to help Lean with the instance.
    exact isStrictlyHenselianLocalRing_WLocalization_IndEtaleContraction (A := WLocalization R) m ‹_›

/-- Any ring has an ind-étale, faithfully flat cover that is w-strictly-local. -/
theorem exists_isWStrictlyLocalRing (R : Type u) [CommRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.IndEtale R S)
      (_ : Module.FaithfullyFlat R S),
      IsWStrictlyLocalRing S := by
  use WStrictLocalization R, inferInstance, inferInstance, inferInstance, inferInstance
  infer_instance
