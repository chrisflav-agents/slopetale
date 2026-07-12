/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.DevissageComparisonA

/-!
# Naturality of the base change comparison and the two-out-of-three property
-/

universe w v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

namespace AlgebraicGeometry.Scheme

open CochainComplex.Plus CochainComplex.Plus.modelCategoryQuillen
variable {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X'.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S'.smallEtaleTopology Ab.{u + 1})]

/-! ## Naturality of the comparison morphism and the two-out-of-three property -/

/-- The comparison morphisms of `baseChangeComparison` are natural with respect to
compatible squares of replacements. -/
lemma baseChangeComparison_naturality
    {M₁ M₂ : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})} (t : M₁ ⟶ M₂)
    {J₁ J₂ : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})} (u : J₁ ⟶ J₂)
    (j₁ : (etalePullback g').mapCochainComplexPlus.obj M₁ ⟶ J₁)
    (j₂ : (etalePullback g').mapCochainComplexPlus.obj M₂ ⟶ J₂)
    (hcomm : j₁ ≫ u = (etalePullback g').mapCochainComplexPlus.map t ≫ j₂) :
    baseChangeComparison f g f' g' w M₁ j₁ ≫
        (etalePushforward f').mapCochainComplexPlus.map u =
      (etalePushforward f ⋙ etalePullback g).mapCochainComplexPlus.map t ≫
        baseChangeComparison f g f' g' w M₂ j₂ := by
  have e : (etalePullback g' ⋙ etalePushforward f').mapCochainComplexPlus.map t =
      (etalePushforward f').mapCochainComplexPlus.map
        ((etalePullback g').mapCochainComplexPlus.map t) := rfl
  dsimp only [baseChangeComparison, Functor.mapCochainComplexPlusComp]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.assoc]
  rw [← Functor.map_comp, hcomm, Functor.map_comp, ← e]
  rw [← Category.assoc, ← (NatTrans.mapCochainComplexPlus
    (etaleBaseChangeNatTrans f g f' g' w)).naturality t, Category.assoc]

/-- The core of the two-out-of-three property: a short exact sequence of fibrant
bounded below complexes on `X_ét` gives rise to a morphism of short exact sequences of
complexes on `S'_ét` whose components detect the `BaseChangeIso` property. -/
lemma exists_ladder_of_fibrant
    (T : ShortComplex (CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ))
    (hT : T.ShortExact)
    (p₁ : CochainComplex.plus _ T.X₁) (p₂ : CochainComplex.plus _ T.X₂)
    (p₃ : CochainComplex.plus _ T.X₃)
    (hi₁ : ∀ n, Injective (T.X₁.X n)) (hi₂ : ∀ n, Injective (T.X₂.X n))
    (hi₃ : ∀ n, Injective (T.X₃.X n)) :
    ∃ (R₁ R₂ : ShortComplex (CochainComplex (Sheaf S'.smallEtaleTopology Ab.{u + 1}) ℤ))
      (Ψ : R₁ ⟶ R₂), R₁.ShortExact ∧ R₂.ShortExact ∧
      ((BaseChangeIso f g f' g' w ⟨T.X₁, p₁⟩ ↔ QuasiIso Ψ.τ₁) ∧
       (BaseChangeIso f g f' g' w ⟨T.X₂, p₂⟩ ↔ QuasiIso Ψ.τ₂) ∧
       (BaseChangeIso f g f' g' w ⟨T.X₃, p₃⟩ ↔ QuasiIso Ψ.τ₃)) ∧
      (∀ q : ℤ,
        (IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map
            ((derivedBaseChangeNatTrans f g f' g' w).app
              ((DerivedCategoryPlus.Q _).obj (⟨T.X₁, p₁⟩ : CochainComplex.Plus _)))) ↔
          IsIso (HomologicalComplex.homologyMap Ψ.τ₁ q)) ∧
        (IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map
            ((derivedBaseChangeNatTrans f g f' g' w).app
              ((DerivedCategoryPlus.Q _).obj (⟨T.X₂, p₂⟩ : CochainComplex.Plus _)))) ↔
          IsIso (HomologicalComplex.homologyMap Ψ.τ₂ q)) ∧
        (IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map
            ((derivedBaseChangeNatTrans f g f' g' w).app
              ((DerivedCategoryPlus.Q _).obj (⟨T.X₃, p₃⟩ : CochainComplex.Plus _)))) ↔
          IsIso (HomologicalComplex.homologyMap Ψ.τ₃ q))) ∧
      (∀ n : ℤ, (∀ i, i < n → T.X₃.ExactAt i) →
        ∀ r, r ≤ n - 2 → (R₁.X₃.ExactAt r ∧ R₂.X₃.ExactAt r)) := by
  -- pull back the sequence to `X'`
  let U := T.map ((etalePullback g').mapHomologicalComplex (ComplexShape.up ℤ))
  have hU : U.ShortExact := hT.map_mapHomologicalComplex hi₁ (etalePullback g')
  have pu₁ : CochainComplex.plus _ U.X₁ :=
    ((etalePullback g').mapCochainComplexPlus.obj ⟨T.X₁, p₁⟩).2
  have pu₂ : CochainComplex.plus _ U.X₂ :=
    ((etalePullback g').mapCochainComplexPlus.obj ⟨T.X₂, p₂⟩).2
  -- resolve it by a short exact sequence of fibrant complexes
  obtain ⟨U', Φ, hU', ⟨q₁, q₂, q₃⟩, ⟨k₁, k₂, k₃⟩, hΦ₁, hΦ₂, hΦ₃⟩ :=
    CochainComplex.Plus.exists_fibrant_ses_resolution U hU pu₁ pu₂
  -- fibrancy
  haveI : IsFibrant (⟨T.X₁, p₁⟩ : CochainComplex.Plus _) :=
    (modelCategoryQuillen.isFibrant_iff _).mpr hi₁
  haveI : IsFibrant (⟨T.X₂, p₂⟩ : CochainComplex.Plus _) :=
    (modelCategoryQuillen.isFibrant_iff _).mpr hi₂
  haveI : IsFibrant (⟨T.X₃, p₃⟩ : CochainComplex.Plus _) :=
    (modelCategoryQuillen.isFibrant_iff _).mpr hi₃
  haveI : IsFibrant (⟨U'.X₁, q₁⟩ : CochainComplex.Plus _) :=
    (modelCategoryQuillen.isFibrant_iff _).mpr k₁
  haveI : IsFibrant (⟨U'.X₂, q₂⟩ : CochainComplex.Plus _) :=
    (modelCategoryQuillen.isFibrant_iff _).mpr k₂
  haveI : IsFibrant (⟨U'.X₃, q₃⟩ : CochainComplex.Plus _) :=
    (modelCategoryQuillen.isFibrant_iff _).mpr k₃
  -- the replacements, as morphisms of `CochainComplex.Plus`
  let j₁ : (etalePullback g').mapCochainComplexPlus.obj ⟨T.X₁, p₁⟩ ⟶
      (⟨U'.X₁, q₁⟩ : CochainComplex.Plus _) := ObjectProperty.homMk Φ.τ₁
  let j₂ : (etalePullback g').mapCochainComplexPlus.obj ⟨T.X₂, p₂⟩ ⟶
      (⟨U'.X₂, q₂⟩ : CochainComplex.Plus _) := ObjectProperty.homMk Φ.τ₂
  let j₃ : (etalePullback g').mapCochainComplexPlus.obj ⟨T.X₃, p₃⟩ ⟶
      (⟨U'.X₃, q₃⟩ : CochainComplex.Plus _) := ObjectProperty.homMk Φ.τ₃
  -- the two rows and the ladder between them
  have sq₁₂ := baseChangeComparison_naturality f g f' g' w
    (M₁ := ⟨T.X₁, p₁⟩) (M₂ := ⟨T.X₂, p₂⟩) (ObjectProperty.homMk T.f)
    (J₁ := ⟨U'.X₁, q₁⟩) (J₂ := ⟨U'.X₂, q₂⟩) (ObjectProperty.homMk U'.f) j₁ j₂
    (by
      apply (CochainComplex.Plus.fullyFaithfulι _).map_injective
      exact Φ.comm₁₂)
  have sq₂₃ := baseChangeComparison_naturality f g f' g' w
    (M₁ := ⟨T.X₂, p₂⟩) (M₂ := ⟨T.X₃, p₃⟩) (ObjectProperty.homMk T.g)
    (J₁ := ⟨U'.X₂, q₂⟩) (J₂ := ⟨U'.X₃, q₃⟩) (ObjectProperty.homMk U'.g) j₂ j₃
    (by
      apply (CochainComplex.Plus.fullyFaithfulι _).map_injective
      exact Φ.comm₂₃)
  refine ⟨T.map ((etalePushforward f ⋙ etalePullback g).mapHomologicalComplex
      (ComplexShape.up ℤ)),
    U'.map ((etalePushforward f').mapHomologicalComplex (ComplexShape.up ℤ)),
    { τ₁ := (baseChangeComparison f g f' g' w ⟨T.X₁, p₁⟩ j₁).hom
      τ₂ := (baseChangeComparison f g f' g' w ⟨T.X₂, p₂⟩ j₂).hom
      τ₃ := (baseChangeComparison f g f' g' w ⟨T.X₃, p₃⟩ j₃).hom
      comm₁₂ := congrArg (fun q => q.hom) sq₁₂
      comm₂₃ := congrArg (fun q => q.hom) sq₂₃ },
    hT.map_mapHomologicalComplex hi₁ _, hU'.map_mapHomologicalComplex k₁ _,
    ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact baseChangeIso_iff_quasiIso_baseChangeComparison f g f' g' w _ j₁ hΦ₁
  · exact baseChangeIso_iff_quasiIso_baseChangeComparison f g f' g' w _ j₂ hΦ₂
  · exact baseChangeIso_iff_quasiIso_baseChangeComparison f g f' g' w _ j₃ hΦ₃
  · intro q
    exact ⟨isIso_homologyMap_baseChangeComparison_iff f g f' g' w _ j₁ hΦ₁ q,
      isIso_homologyMap_baseChangeComparison_iff f g f' g' w _ j₂ hΦ₂ q,
      isIso_homologyMap_baseChangeComparison_iff f g f' g' w _ j₃ hΦ₃ q⟩
  · intro n hn r hr
    constructor
    · -- the third term of the first row is `(g^* ∘ f_*)(T.X₃)`
      obtain ⟨a₃, ha₃⟩ := p₃
      exact exactAt_mapHomologicalComplex_of_exact_lowDegree
        (etalePushforward f ⋙ etalePullback g) T.X₃ a₃ ha₃ hi₃ n hn r hr
    · -- the third term of the second row is `f'_*(U'.X₃)`
      obtain ⟨a₃', ha₃'⟩ := q₃
      refine exactAt_mapHomologicalComplex_of_exact_lowDegree
        (etalePushforward f') U'.X₃ a₃' ha₃' k₃ n (fun i hi => ?_) r hr
      have hUi : U.X₃.ExactAt i :=
        exactAt_mapHomologicalComplex_of_exactAt (etalePullback g') T.X₃ (hn i hi)
      haveI := hΦ₃.quasiIsoAt i
      exact (exactAt_iff_of_quasiIsoAt Φ.τ₃ i).mp hUi

/-- Transfer of `BaseChangeIso` from a short exact sequence to a fibrant resolution of
it, in all three components. -/
lemma baseChangeIso_iff_of_fibrant_resolution
    (T T' : ShortComplex (CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ))
    (Φ : T ⟶ T')
    (p₁ : CochainComplex.plus _ T.X₁) (p₂ : CochainComplex.plus _ T.X₂)
    (p₃ : CochainComplex.plus _ T.X₃)
    (q₁ : CochainComplex.plus _ T'.X₁) (q₂ : CochainComplex.plus _ T'.X₂)
    (q₃ : CochainComplex.plus _ T'.X₃)
    (m₁ : QuasiIso Φ.τ₁) (m₂ : QuasiIso Φ.τ₂) (m₃ : QuasiIso Φ.τ₃) :
    (BaseChangeIso f g f' g' w ⟨T.X₁, p₁⟩ ↔ BaseChangeIso f g f' g' w ⟨T'.X₁, q₁⟩) ∧
    (BaseChangeIso f g f' g' w ⟨T.X₂, p₂⟩ ↔ BaseChangeIso f g f' g' w ⟨T'.X₂, q₂⟩) ∧
    (BaseChangeIso f g f' g' w ⟨T.X₃, p₃⟩ ↔ BaseChangeIso f g f' g' w ⟨T'.X₃, q₃⟩) :=
  ⟨baseChangeIso_iff_of_quasiIso f g f' g' w (ObjectProperty.homMk Φ.τ₁) m₁,
    baseChangeIso_iff_of_quasiIso f g f' g' w (ObjectProperty.homMk Φ.τ₂) m₂,
    baseChangeIso_iff_of_quasiIso f g f' g' w (ObjectProperty.homMk Φ.τ₃) m₃⟩

/-- Two out of three for `BaseChangeIso`: the middle term. -/
lemma baseChangeIso_X₂
    (T : ShortComplex (CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ))
    (hT : T.ShortExact)
    (p₁ : CochainComplex.plus _ T.X₁) (p₂ : CochainComplex.plus _ T.X₂)
    (p₃ : CochainComplex.plus _ T.X₃)
    (h₁ : BaseChangeIso f g f' g' w ⟨T.X₁, p₁⟩)
    (h₃ : BaseChangeIso f g f' g' w ⟨T.X₃, p₃⟩) :
    BaseChangeIso f g f' g' w ⟨T.X₂, p₂⟩ := by
  obtain ⟨T', Φ, hT', ⟨q₁, q₂, q₃⟩, ⟨k₁, k₂, k₃⟩, m₁, m₂, m₃⟩ :=
    CochainComplex.Plus.exists_fibrant_ses_resolution T hT p₁ p₂
  obtain ⟨e₁, e₂, e₃⟩ := baseChangeIso_iff_of_fibrant_resolution f g f' g' w
    T T' Φ p₁ p₂ p₃ q₁ q₂ q₃ m₁ m₂ m₃
  obtain ⟨R₁, R₂, Ψ, hR₁, hR₂, ⟨i₁, i₂, i₃⟩, -, -⟩ := exists_ladder_of_fibrant f g f' g' w
    T' hT' q₁ q₂ q₃ k₁ k₂ k₃
  rw [e₂, i₂]
  exact CochainComplex.quasiIso_τ₂_of_shortExact Ψ hR₁ hR₂
    (i₁.mp (e₁.mp h₁)) (i₃.mp (e₃.mp h₃))

/-- Two out of three for `BaseChangeIso`: the first term. -/
lemma baseChangeIso_X₁
    (T : ShortComplex (CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ))
    (hT : T.ShortExact)
    (p₁ : CochainComplex.plus _ T.X₁) (p₂ : CochainComplex.plus _ T.X₂)
    (p₃ : CochainComplex.plus _ T.X₃)
    (h₂ : BaseChangeIso f g f' g' w ⟨T.X₂, p₂⟩)
    (h₃ : BaseChangeIso f g f' g' w ⟨T.X₃, p₃⟩) :
    BaseChangeIso f g f' g' w ⟨T.X₁, p₁⟩ := by
  obtain ⟨T', Φ, hT', ⟨q₁, q₂, q₃⟩, ⟨k₁, k₂, k₃⟩, m₁, m₂, m₃⟩ :=
    CochainComplex.Plus.exists_fibrant_ses_resolution T hT p₁ p₂
  obtain ⟨e₁, e₂, e₃⟩ := baseChangeIso_iff_of_fibrant_resolution f g f' g' w
    T T' Φ p₁ p₂ p₃ q₁ q₂ q₃ m₁ m₂ m₃
  obtain ⟨R₁, R₂, Ψ, hR₁, hR₂, ⟨i₁, i₂, i₃⟩, -, -⟩ := exists_ladder_of_fibrant f g f' g' w
    T' hT' q₁ q₂ q₃ k₁ k₂ k₃
  rw [e₁, i₁]
  exact CochainComplex.quasiIso_τ₁_of_shortExact Ψ hR₁ hR₂
    (i₂.mp (e₂.mp h₂)) (i₃.mp (e₃.mp h₃))

/-- Two out of three for `BaseChangeIso`: the third term. -/
lemma baseChangeIso_X₃
    (T : ShortComplex (CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ))
    (hT : T.ShortExact)
    (p₁ : CochainComplex.plus _ T.X₁) (p₂ : CochainComplex.plus _ T.X₂)
    (p₃ : CochainComplex.plus _ T.X₃)
    (h₁ : BaseChangeIso f g f' g' w ⟨T.X₁, p₁⟩)
    (h₂ : BaseChangeIso f g f' g' w ⟨T.X₂, p₂⟩) :
    BaseChangeIso f g f' g' w ⟨T.X₃, p₃⟩ := by
  obtain ⟨T', Φ, hT', ⟨q₁, q₂, q₃⟩, ⟨k₁, k₂, k₃⟩, m₁, m₂, m₃⟩ :=
    CochainComplex.Plus.exists_fibrant_ses_resolution T hT p₁ p₂
  obtain ⟨e₁, e₂, e₃⟩ := baseChangeIso_iff_of_fibrant_resolution f g f' g' w
    T T' Φ p₁ p₂ p₃ q₁ q₂ q₃ m₁ m₂ m₃
  obtain ⟨R₁, R₂, Ψ, hR₁, hR₂, ⟨i₁, i₂, i₃⟩, -, -⟩ := exists_ladder_of_fibrant f g f' g' w
    T' hT' q₁ q₂ q₃ k₁ k₂ k₃
  rw [e₃, i₃]
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ Ψ hR₁ hR₂
    (i₁.mp (e₁.mp h₁)) (i₂.mp (e₂.mp h₂))

end AlgebraicGeometry.Scheme
