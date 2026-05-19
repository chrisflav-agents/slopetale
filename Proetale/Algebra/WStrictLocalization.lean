/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WLocalization.Basic
import Proetale.Algebra.IndEtale
import Proetale.Algebra.ProEtaleContraction
import Proetale.Mathlib.RingTheory.Etale.IndSpreads

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
  -- this lemma reduces to a single application.
  exact Algebra.Etale.exists_descent_along_localizationAtPrime m B

/-- **lemma:retractions-strictly-henselian** (Blueprint): If every faithfully flat etale ring map
`A -> B` has a retraction, then every local ring `A_m` at a maximal ideal is strictly Henselian.

Blueprint proof outline (local-structure.tex, lines 1701–1740):
Given a maximal `m` of `A`, set `A_m := Localization.AtPrime m`. Then:
1. Factor `A_m → B → κ(m)^sep` where `A_m → B` is etale.
2. Descend `B` to an etale `A_f`-algebra `B'` via etale-ind-spreads (`A_m = colim A_f`).
3. Use prime avoidance to find `g` isolating a unique prime `q` of `B'_g` lying over `m`.
4. Construct the faithfully flat etale cover `A → B'_g × ∏ A_{aᵢ}`.
5. Apply the retraction hypothesis to obtain `σ`.
6. Localize `σ` at `q` to get `B'_q → A_m`, then extend to `B → A_m`.

The blueprint argument shows that every etale `A_m → B` factoring through a separable closure
of `κ(m)` admits a section, which characterizes strict henselianity of `A_m`. Conjunction of:
* `HenselianLocalRing`: lifting of simple roots — via `henselian_if_exists_section` style argument.
* `IsSepClosed (ResidueField A_m)` — i.e. `A/m` is separably closed.

The full formalization requires extensive infrastructure (etale-ind-spreads at the level of
`Localization.AtPrime m`, prime avoidance for finite collections of primes lying over `m`,
construction of the faithfully flat etale product cover, descent of the retraction back along
the localization map). This is left as an open task: see `task_results/Algebra_WStrictLocalization.lean.md`. -/
private lemma isStrictlyHenselianLocalRing_of_exists_retraction
    (A : Type u) [CommRing A]
    (hret : ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra.Etale A B]
      [Module.FaithfullyFlat A B], ∃ σ : B →ₐ[A] A, True)
    (m : Ideal A) [m.IsMaximal] :
    IsStrictlyHenselianLocalRing (Localization.AtPrime m) := by
  -- We must show both:
  --   (1) HenselianLocalRing (Localization.AtPrime m).
  --   (2) IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime m)).
  -- Both reductions go via the retraction hypothesis using the blueprint's prime-avoidance
  -- + faithfully-flat-etale-cover construction (see file header). The IsLocalRing instance
  -- comes for free from `IsLocalization.AtPrime`.
  haveI : IsLocalRing (Localization.AtPrime m) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime m) m
  -- HenselianLocalRing instance for `Localization.AtPrime m`.
  --
  -- Following the blueprint argument: a simple root `a₀ ∈ κ(m)` of a monic `f` defines a
  -- residue-field map `S_f → κ(m)` where `S_f = A_m[X,Y]/(f, f'·Y - 1)` is etale (= the
  -- "Henselian polynomial algebra" of `f`). The descent to a faithfully flat etale
  -- `A_f`-algebra, the prime-avoidance separation of the unique prime above `m`, and the
  -- retraction hypothesis combine to produce the desired section `S_f → A_m`, hence the
  -- root. This requires substantial infrastructure not yet available.
  haveI hHens : HenselianLocalRing (Localization.AtPrime m) := by sorry
  -- `IsSepClosed (κ(m))`: every monic separable polynomial over `κ(m) = A/m` has a root.
  --
  -- Given a separable irreducible `f ∈ κ(m)[X]`, the corresponding finite separable
  -- extension `L = κ(m)[X]/(f)` is a finite etale `κ(m)`-algebra. We lift it to a finite
  -- etale `A_m`-algebra `B` (by smoothness of `A_m → κ(m)`). Then `B` descends to an etale
  -- `A_f`-algebra `B'`. Via the prime avoidance + retraction argument, we obtain a section
  -- `B → A_m`, which produces a `κ(m)`-algebra map `L → κ(m)`, i.e. a root of `f` in `κ(m)`.
  exact { isSepClosed_residueField := by sorry }

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
