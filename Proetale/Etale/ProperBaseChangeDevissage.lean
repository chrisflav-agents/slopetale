/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.ProperBaseChange

/-!
# Dévissage in `K` for the proper base change theorem

Let

```
X' --g'--> X
|          |
f'         f
↓          ↓
S' --g---> S
```

be a commutative square of schemes. The proper base change theorem asserts that the
derived base change transformation `Rf_* ⋙ g^* ⟶ g'^* ⋙ Rf'_*` is an isomorphism on
every bounded below complex with locally torsion cohomology sheaves (when the square is
cartesian and `f` is proper). This file proves the **dévissage in `K`**: the statement
for arbitrary such complexes follows from the statement for a single locally torsion
sheaf placed in degree `0`
(`AlgebraicGeometry.Scheme.isIso_derivedBaseChangeNatTrans_app_of_singleFunctor`).

The proof avoids the (not yet formalized) triangulated structure on
`DerivedCategoryPlus` and instead works entirely with concrete short exact sequences of
bounded below cochain complexes:

- a morphism `ψ` of bounded below complexes becomes an isomorphism in
  `DerivedCategoryPlus` iff it is a quasi-isomorphism
  (`DerivedCategoryPlus.isIso_Q_map_iff_quasiIso`);
- on a fibrant complex `I` (a bounded below complex of injectives for the injective
  model structure on `CochainComplex.Plus`), the value of the derived base change
  transformation is, up to isomorphism, `Q.map` of a concrete comparison morphism
  `g^* f_* I ⟶ f'_* J` for any fibrant replacement `J` of `g'^* I`;
- short exact sequences of complexes are resolved by short exact sequences of fibrant
  complexes (a model-categorical horseshoe lemma,
  `CochainComplex.Plus.exists_fibrant_ses_resolution`);
- the five lemma for the homology long exact sequence then yields a two-out-of-three
  property for the class of complexes on which the transformation is an isomorphism;
- singles in all degrees are reached from degree `0` via short exact sequences
  `0 ⟶ single (n+1) F ⟶ D ⟶ single n F ⟶ 0` with `D` acyclic (no shift functors are
  needed), and general complexes by induction on the cohomological amplitude using the
  canonical truncations; finally, bounded below complexes with unbounded cohomology are
  treated degreewise using that a fibrant complex which is acyclic in degrees `< n`
  splits in low degrees, so that its image under any additive functor is acyclic in
  degrees `≤ n - 2`.
-/

universe w v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

section Preliminaries

/-! ## The five lemma for the homology sequence: the `τ₁` and `τ₂` variants

Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃` shows that in a morphism of
short exact sequences of homological complexes, if `τ₁` and `τ₂` are
quasi-isomorphisms, then so is `τ₃`. Here we prove the two remaining variants.
-/

namespace HomologicalComplex.HomologySequence

open ComposableArrows Abelian

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

/-- The exact sequence
`H_i(X₃) ⟶ H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃) ⟶ H_k(X₁)` associated to a short exact
sequence of homological complexes. -/
@[simp]
noncomputable def composableArrows₄ (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    ComposableArrows C 4 :=
  mk₄ (hS₁.δ i j hij) (homologyMap S₁.f j) (homologyMap S₁.g j) (hS₁.δ j k hjk)

lemma composableArrows₄_exact (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    (composableArrows₄ hS₁ i j k hij hjk).Exact :=
  exact_of_δ₀ (hS₁.homology_exact₁ i j hij).exact_toComposableArrows
    (exact_of_δ₀ (hS₁.homology_exact₂ j).exact_toComposableArrows
      (hS₁.homology_exact₃ j k hjk).exact_toComposableArrows)

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `composableArrows₄ hS₁ i j k ⟶ composableArrows₄ hS₂ i j k` induced
by a morphism of short exact sequences of homological complexes. -/
@[simp]
noncomputable def mapComposableArrows₄ (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    composableArrows₄ hS₁ i j k hij hjk ⟶ composableArrows₄ hS₂ i j k hij hjk :=
  homMk₄ (homologyMap φ.τ₃ i) (homologyMap φ.τ₁ j) (homologyMap φ.τ₂ j)
    (homologyMap φ.τ₃ j) (homologyMap φ.τ₁ k)
    (δ_naturality φ hS₁ hS₂ i j hij)
    (naturality' (mapComposableArrows₂ φ j) 0 1)
    (naturality' (mapComposableArrows₂ φ j) 1 2)
    (δ_naturality φ hS₁ hS₂ j k hjk)

include hS₁ hS₂ in
lemma isIso_homologyMap_τ₂ (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k)
    (h₀ : Epi (homologyMap φ.τ₃ i)) (h₁ : IsIso (homologyMap φ.τ₁ j))
    (h₃ : IsIso (homologyMap φ.τ₃ j)) (h₄ : Mono (homologyMap φ.τ₁ k)) :
    IsIso (homologyMap φ.τ₂ j) :=
  isIso_of_epi_of_isIso_of_isIso_of_mono
    (composableArrows₄_exact hS₁ i j k hij hjk)
    (composableArrows₄_exact hS₂ i j k hij hjk)
    (mapComposableArrows₄ φ hS₁ hS₂ i j k hij hjk) h₀ h₁ h₃ h₄

/-- The exact sequence
`H_i(X₂) ⟶ H_i(X₃) ⟶ H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃)` associated to a short exact
sequence of homological complexes. -/
@[simp]
noncomputable def composableArrows₄' (i j : ι) (hij : c.Rel i j) :
    ComposableArrows C 4 :=
  mk₄ (homologyMap S₁.g i) (hS₁.δ i j hij) (homologyMap S₁.f j) (homologyMap S₁.g j)

lemma composableArrows₄'_exact (i j : ι) (hij : c.Rel i j) :
    (composableArrows₄' hS₁ i j hij).Exact :=
  exact_of_δ₀ (hS₁.homology_exact₃ i j hij).exact_toComposableArrows
    (exact_of_δ₀ (hS₁.homology_exact₁ i j hij).exact_toComposableArrows
      (hS₁.homology_exact₂ j).exact_toComposableArrows)

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `composableArrows₄' hS₁ i j ⟶ composableArrows₄' hS₂ i j` induced
by a morphism of short exact sequences of homological complexes. -/
@[simp]
noncomputable def mapComposableArrows₄' (i j : ι) (hij : c.Rel i j) :
    composableArrows₄' hS₁ i j hij ⟶ composableArrows₄' hS₂ i j hij :=
  homMk₄ (homologyMap φ.τ₂ i) (homologyMap φ.τ₃ i) (homologyMap φ.τ₁ j)
    (homologyMap φ.τ₂ j) (homologyMap φ.τ₃ j)
    (naturality' (mapComposableArrows₂ φ i) 1 2)
    (δ_naturality φ hS₁ hS₂ i j hij)
    (naturality' (mapComposableArrows₂ φ j) 0 1)
    (naturality' (mapComposableArrows₂ φ j) 1 2)

include hS₁ hS₂ in
lemma isIso_homologyMap_τ₁ (i j : ι) (hij : c.Rel i j)
    (h₀ : Epi (homologyMap φ.τ₂ i)) (h₁ : IsIso (homologyMap φ.τ₃ i))
    (h₃ : IsIso (homologyMap φ.τ₂ j)) (h₄ : Mono (homologyMap φ.τ₃ j)) :
    IsIso (homologyMap φ.τ₁ j) :=
  isIso_of_epi_of_isIso_of_isIso_of_mono
    (composableArrows₄'_exact hS₁ i j hij)
    (composableArrows₄'_exact hS₂ i j hij)
    (mapComposableArrows₄' φ hS₁ hS₂ i j hij) h₀ h₁ h₃ h₄

end HomologicalComplex.HomologySequence

namespace CochainComplex

open HomologicalComplex HomologySequence

variable {C : Type*} [Category* C] [Abelian C]
  {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂ in
/-- Two out of three for quasi-isomorphisms of short exact sequences of cochain
complexes: if `τ₁` and `τ₃` are quasi-isomorphisms, then so is `τ₂`. -/
lemma quasiIso_τ₂_of_shortExact (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_τ₂ φ hS₁ hS₂ (j - 1) j (j + 1) (by simp) (by simp)
    inferInstance inferInstance inferInstance inferInstance

include hS₁ hS₂ in
/-- Two out of three for quasi-isomorphisms of short exact sequences of cochain
complexes: if `τ₂` and `τ₃` are quasi-isomorphisms, then so is `τ₁`. -/
lemma quasiIso_τ₁_of_shortExact (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₁ := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_τ₁ φ hS₁ hS₂ (j - 1) j (by simp)
    inferInstance inferInstance inferInstance inferInstance

end CochainComplex

/-! ## Isomorphisms in the bounded below derived category -/

namespace DerivedCategoryPlus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategoryPlus.{w} C]

/-- A morphism of bounded below cochain complexes becomes an isomorphism in the bounded
below derived category iff it is a quasi-isomorphism. -/
lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex.Plus C} (ψ : K ⟶ L) :
    IsIso ((Q C).map ψ) ↔ CochainComplex.Plus.quasiIso C ψ := by
  constructor
  · intro h
    have h' (n : ℤ) : IsIso ((CochainComplex.Plus.ι C ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map ψ) := by
      have : IsIso ((Q C ⋙ homologyFunctor C n).map ψ) :=
        inferInstanceAs (IsIso ((homologyFunctor C n).map ((Q C).map ψ)))
      rw [← NatIso.naturality_1 (homologyFunctorFactors C n) ψ]
      infer_instance
    have : QuasiIso ((CochainComplex.Plus.ι C).map ψ) := by
      rw [quasiIso_iff]
      intro n
      rw [quasiIsoAt_iff_isIso_homologyMap]
      exact h' n
    exact this
  · intro h
    exact Localization.inverts (Q C) (CochainComplex.Plus.quasiIso C) ψ h

end DerivedCategoryPlus

/-! ## Pushout of a short exact sequence -/

namespace CategoryTheory.ShortComplex

variable {A : Type u'} [Category.{v'} A] [Abelian A]

/-- The pushout of a short complex `X₁ ⟶ X₂ ⟶ X₃` along a morphism `X₁ ⟶ B`:
the short complex `B ⟶ B ⊔_{X₁} X₂ ⟶ X₃`. -/
@[simps]
noncomputable def pushoutShortComplex (S : ShortComplex A) {B : A} (f : S.X₁ ⟶ B) :
    ShortComplex A :=
  ShortComplex.mk (pushout.inl f S.f) (pushout.desc 0 S.g (by simp)) (by simp)

/-- The canonical morphism from a short complex to its pushout along a morphism out of
its first term. -/
@[simps]
noncomputable def toPushoutShortComplex (S : ShortComplex A) {B : A} (f : S.X₁ ⟶ B) :
    S ⟶ S.pushoutShortComplex f where
  τ₁ := f
  τ₂ := pushout.inr f S.f
  τ₃ := 𝟙 _
  comm₁₂ := pushout.condition
  comm₂₃ := by simp [pushoutShortComplex]

/-- The pushout of a short exact sequence along a morphism out of its first term is
short exact. -/
lemma ShortExact.pushoutShortComplex {S : ShortComplex A} (hS : S.ShortExact)
    {B : A} (f : S.X₁ ⟶ B) :
    (S.pushoutShortComplex f).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have sq : IsPushout f S.f (pushout.inl f S.f) (pushout.inr f S.f) :=
    IsPushout.of_hasPushout f S.f
  have hmono : Mono (S.pushoutShortComplex f).f := by
    dsimp [ShortComplex.pushoutShortComplex]
    infer_instance
  have hepi : Epi (S.pushoutShortComplex f).g := by
    dsimp [ShortComplex.pushoutShortComplex]
    exact epi_of_epi_fac (pushout.inr_desc 0 S.g _)
  have hexact : (S.pushoutShortComplex f).Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    obtain ⟨T', π, hπ, xB, x₂, hdec⟩ := sq.hom_eq_add_up_to_refinements x
    have hx₂ : x₂ ≫ S.g = 0 := by
      have h0 : π ≫ x ≫ (S.pushoutShortComplex f).g = 0 := by rw [hx, comp_zero]
      rw [← Category.assoc, hdec, Preadditive.add_comp, Category.assoc, Category.assoc] at h0
      simpa [ShortComplex.pushoutShortComplex] using h0
    obtain ⟨T'', π', hπ', x₁, hx₁⟩ := hS.exact.exact_up_to_refinements x₂ hx₂
    refine ⟨T'', π' ≫ π, epi_comp _ _, π' ≫ xB + x₁ ≫ f, ?_⟩
    have hw : S.f ≫ pushout.inr f S.f = f ≫ pushout.inl f S.f := sq.w.symm
    have hf : (S.pushoutShortComplex f).f = pushout.inl f S.f := rfl
    rw [hf, Preadditive.add_comp, Category.assoc, Category.assoc, hdec,
      Preadditive.comp_add]
    congr 1
    calc π' ≫ x₂ ≫ pushout.inr f S.f
        = (π' ≫ x₂) ≫ pushout.inr f S.f := by rw [Category.assoc]
      _ = (x₁ ≫ S.f) ≫ pushout.inr f S.f := by rw [hx₁]
      _ = x₁ ≫ S.f ≫ pushout.inr f S.f := by rw [Category.assoc]
      _ = x₁ ≫ f ≫ pushout.inl f S.f := by rw [hw]
      _ = (x₁ ≫ f) ≫ pushout.inl f S.f := (Category.assoc _ _ _).symm
  exact { exact := hexact, mono_f := hmono, epi_g := hepi }

end CategoryTheory.ShortComplex

/-! ## Cokernels of monomorphisms between injectives -/

section InjectiveCokernel

variable {A : Type u'} [Category.{v'} A] [Abelian A]

/-- In an abelian category, the cokernel of a monomorphism between injective objects is
injective. -/
lemma Injective.cokernel_of_mono {X Y : A} (f : X ⟶ Y) [Mono f] [Injective X]
    [Injective Y] : Injective (cokernel f) := by
  have hexact : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).Exact :=
    ShortComplex.exact_cokernel f
  let sp := ShortComplex.Splitting.ofExactOfRetraction _ hexact
    (Injective.factorThru (𝟙 X) f) (Injective.comp_factorThru (𝟙 X) f) inferInstance
  exact Retract.injective { i := sp.s, r := cokernel.π f, retract := sp.s_g }

end InjectiveCokernel

/-! ## The horseshoe lemma

Every short exact sequence of bounded below cochain complexes admits a componentwise
quasi-isomorphism to a short exact sequence of bounded below complexes of injectives.
The construction pushes out along a fibrant replacement (in the injective model
structure on `CochainComplex.Plus`) of the first term, then takes a fibrant replacement
of the middle term and the induced cokernel.
-/

section Horseshoe

open CochainComplex.Plus.modelCategoryQuillen HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

lemma CochainComplex.Plus.exists_fibrant_ses_resolution
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (h₁ : CochainComplex.plus C S.X₁) (h₂ : CochainComplex.plus C S.X₂) :
    ∃ (T : ShortComplex (CochainComplex C ℤ)) (Φ : S ⟶ T),
      T.ShortExact ∧
      (CochainComplex.plus C T.X₁ ∧ CochainComplex.plus C T.X₂ ∧
        CochainComplex.plus C T.X₃) ∧
      ((∀ n, Injective (T.X₁.X n)) ∧ (∀ n, Injective (T.X₂.X n)) ∧
        (∀ n, Injective (T.X₃.X n))) ∧
      (QuasiIso Φ.τ₁ ∧ QuasiIso Φ.τ₂ ∧ QuasiIso Φ.τ₃) := by
  have := hS.mono_f
  have := hS.epi_g
  -- fibrant replacement of the first term
  let M₁ : CochainComplex.Plus C := ⟨S.X₁, h₁⟩
  let R₁ : CochainComplex.Plus C := FibrantObject.HoCat.resolutionObj M₁
  let i₁ : M₁ ⟶ R₁ := FibrantObject.HoCat.iResolutionObj M₁
  have hi₁q : QuasiIso i₁.hom := by
    rw [← modelCategoryQuillen.weakEquivalence_iff]
    infer_instance
  -- the pushout of the short exact sequence along the fibrant replacement
  let S' := S.pushoutShortComplex i₁.hom
  have hS' : S'.ShortExact := hS.pushoutShortComplex i₁.hom
  let Φ' : S ⟶ S' := S.toPushoutShortComplex i₁.hom
  have hplusN : CochainComplex.plus C S'.X₂ := by
    refine (CochainComplex.plus C).prop_colimit (span i₁.hom S.f) (fun j => ?_)
    obtain (_ | (_ | _)) := j
    · exact h₁
    · exact R₁.2
    · exact h₂
  have hΦ'τ₂ : QuasiIso Φ'.τ₂ := by
    have h₁' : QuasiIso Φ'.τ₁ := hi₁q
    have h₃' : QuasiIso Φ'.τ₃ := by
      dsimp [Φ', CategoryTheory.ShortComplex.toPushoutShortComplex]
      infer_instance
    exact CochainComplex.quasiIso_τ₂_of_shortExact Φ' hS hS' h₁' h₃'
  -- fibrant replacement of the middle term of the pushout
  let M₂ : CochainComplex.Plus C := ⟨S'.X₂, hplusN⟩
  let R₂ : CochainComplex.Plus C := FibrantObject.HoCat.resolutionObj M₂
  let i₂ : M₂ ⟶ R₂ := FibrantObject.HoCat.iResolutionObj M₂
  have hi₂q : QuasiIso i₂.hom := by
    rw [← modelCategoryQuillen.weakEquivalence_iff]
    infer_instance
  have hinj₁ : ∀ n, Injective (R₁.obj.X n) := (modelCategoryQuillen.isFibrant_iff R₁).mp inferInstance
  have hinj₂ : ∀ n, Injective (R₂.obj.X n) := (modelCategoryQuillen.isFibrant_iff R₂).mp inferInstance
  -- the third term of the resolved sequence
  let inl' : R₁.obj ⟶ R₂.obj := S'.f ≫ i₂.hom
  have hmono_inl' : Mono inl' := by
    have : Mono S'.f := hS'.mono_f
    exact mono_comp _ _
  let T := ShortComplex.mk inl' (cokernel.π inl') (cokernel.condition inl')
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel inl' }
  -- the induced morphism on third terms
  have hw : S'.f ≫ i₂.hom ≫ cokernel.π inl' = 0 := by
    rw [← Category.assoc]
    exact cokernel.condition inl'
  obtain ⟨τ₃'', hτ₃''⟩ := CokernelCofork.IsColimit.desc' hS'.gIsCokernel
    (i₂.hom ≫ cokernel.π inl') hw
  let Φ'' : S' ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := i₂.hom
      τ₃ := τ₃''
      comm₁₂ := by simp [T, inl']
      comm₂₃ := hτ₃''.symm }
  have hΦ''τ₃ : QuasiIso Φ''.τ₃ := by
    have h₁'' : QuasiIso Φ''.τ₁ := by
      dsimp [Φ'']
      infer_instance
    have h₂'' : QuasiIso Φ''.τ₂ := hi₂q
    exact HomologySequence.quasiIso_τ₃ Φ'' hS' hT h₁'' h₂''
  -- degreewise injectivity of the cokernel
  have hinj₃ : ∀ n, Injective (T.X₃.X n) := by
    intro n
    have : Mono (inl'.f n) := by
      change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map inl')
      infer_instance
    have := hinj₁ n
    have := hinj₂ n
    have : Injective (cokernel (inl'.f n)) := Injective.cokernel_of_mono (inl'.f n)
    exact Injective.of_iso (PreservesCokernel.iso
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n) inl').symm this
  -- boundedness below of the three terms
  have hplus₃ : CochainComplex.plus C T.X₃ :=
    (CochainComplex.plus C).prop_colimit (parallelPair inl' 0) (fun j => by
      obtain (_ | _) := j
      · exact R₁.2
      · exact R₂.2)
  refine ⟨T, Φ' ≫ Φ'', hT, ⟨R₁.2, R₂.2, hplus₃⟩, ⟨hinj₁, hinj₂, hinj₃⟩, ?_, ?_, ?_⟩
  · have : QuasiIso Φ'.τ₁ := hi₁q
    have : QuasiIso Φ''.τ₁ := by
      dsimp [Φ'']
      infer_instance
    exact inferInstanceAs (QuasiIso (Φ'.τ₁ ≫ Φ''.τ₁))
  · have : QuasiIso Φ'.τ₂ := hΦ'τ₂
    have : QuasiIso Φ''.τ₂ := hi₂q
    exact inferInstanceAs (QuasiIso (Φ'.τ₂ ≫ Φ''.τ₂))
  · have : QuasiIso Φ'.τ₃ := by
      dsimp [Φ', CategoryTheory.ShortComplex.toPushoutShortComplex]
      infer_instance
    have : QuasiIso Φ''.τ₃ := hΦ''τ₃
    exact inferInstanceAs (QuasiIso (Φ'.τ₃ ≫ Φ''.τ₃))

end Horseshoe

/-! ## Transfer of `IsIso` for natural transformations along isomorphisms -/

section NatTransIsIso

variable {C : Type u'} [Category.{v'} C] {D : Type u} [Category.{v} D]

/-- If `e : X ⟶ Y` is an isomorphism, a natural transformation is an isomorphism at `X`
iff it is one at `Y`. -/
lemma NatTrans.isIso_app_iff_of_isIso {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ⟶ Y)
    [IsIso e] : IsIso (α.app X) ↔ IsIso (α.app Y) := by
  have nat : F.map e ≫ α.app Y = α.app X ≫ G.map e := α.naturality e
  constructor
  · intro h
    have : α.app Y = inv (F.map e) ≫ α.app X ≫ G.map e := by
      rw [← nat, IsIso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  · intro h
    have : α.app X = F.map e ≫ α.app Y ≫ inv (G.map e) := by
      rw [← Category.assoc, nat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [this]
    infer_instance

end NatTransIsIso

/-! ## Additive functors preserve short exact sequences of complexes of injectives -/

section MapShortExact

variable {A : Type u'} [Category.{v'} A] {B : Type u} [Category.{v} B]
  [Abelian A] [Abelian B] {ι : Type*} {c : ComplexShape ι}

open HomologicalComplex

/-- An additive functor preserves short exactness of short exact sequences of
homological complexes whose first term is degreewise injective (such sequences are
degreewise split). -/
lemma ShortComplex.ShortExact.map_mapHomologicalComplex
    {S : ShortComplex (HomologicalComplex A c)} (hS : S.ShortExact)
    (hinj : ∀ n, Injective (S.X₁.X n)) (F : A ⥤ B) [F.Additive] :
    (S.map (F.mapHomologicalComplex c)).ShortExact := by
  rw [shortExact_iff_degreewise_shortExact] at hS ⊢
  intro n
  have hn := hS n
  haveI : Mono ((S.map (eval A c n)).f) := hn.mono_f
  haveI : Injective ((S.map (eval A c n)).X₁) := hinj n
  -- the degreewise short exact sequence splits since its first term is injective
  let sp : (S.map (eval A c n)).Splitting :=
    ShortComplex.Splitting.ofExactOfRetraction _ hn.exact
      (Injective.factorThru (𝟙 _) ((S.map (eval A c n)).f))
      (Injective.comp_factorThru _ _) hn.epi_g
  exact ((sp.map F).shortExact)

end MapShortExact

end Preliminaries


/-! ## Complexes of injectives which are exact in low degrees

A bounded below complex of injectives which is exact in all degrees `< n` admits a
contracting homotopy in low degrees; consequently its image under any additive functor
is exact in all degrees `≤ n - 2`. This is the key to the dévissage for complexes with
unbounded cohomology: the value of the derived pushforward in a fixed degree only
depends on a finite truncation.
-/

section LowDegree

open HomologicalComplex

variable {A : Type u'} [Category.{v'} A] [Abelian A]

/-- Any morphism into a zero object is epi. -/
lemma epi_of_isZero {P Q : A} (hQ : IsZero Q) (φ : P ⟶ Q) : Epi φ :=
  ⟨fun _ _ _ => hQ.eq_of_src _ _⟩

/-- A morphism `θ : K.X i ⟶ B` into an injective object which vanishes on the image of
the incoming differential factors through the outgoing differential, provided `K` is
exact at `i`. -/
lemma exists_comp_d_eq_of_exactAt {K : CochainComplex A ℤ} {i i' : ℤ} (hi' : i' = i + 1)
    (hK : K.ExactAt i) {B : A} [Injective B] (θ : K.X i ⟶ B)
    (hθ : K.d (i - 1) i ≫ θ = 0) :
    ∃ s : K.X i' ⟶ B, K.d i i' ≫ s = θ := by
  subst hi'
  -- descend to the opcycles
  have hmono : Mono (K.fromOpcycles i (i + 1)) := by
    have h : (ComplexShape.up ℤ).next i = i + 1 := CochainComplex.next i
    rw [← h]
    exact (ShortComplex.exact_iff_mono_fromOpcycles (K.sc i)).mp hK
  refine ⟨Injective.factorThru (K.descOpcycles θ (i - 1) (by simp) hθ)
    (K.fromOpcycles i (i + 1)), ?_⟩
  rw [← K.p_fromOpcycles i (i + 1), Category.assoc,
    Injective.comp_factorThru, p_descOpcycles]

/-- A bounded below complex of injectives which is exact in all degrees `< n` admits
partial contracting homotopies in degrees `≤ n - 1`. -/
lemma exists_contraction_of_exact_of_injective (K : CochainComplex A ℤ) (a : ℤ)
    (hge : K.IsStrictlyGE a) (hinj : ∀ i, Injective (K.X i)) (n : ℤ)
    (hex : ∀ i, i < n → K.ExactAt i) (j : ℤ) (hj : j ≤ n - 1) :
    ∀ (i : ℤ), i = j + 1 →
      ∃ (t : K.X j ⟶ K.X (j - 1)) (t' : K.X i ⟶ K.X j),
        t ≫ K.d (j - 1) j + K.d j i ≫ t' = 𝟙 (K.X j) := by
  haveI := hge
  suffices h : ∀ (k : ℕ) (j : ℤ), j ≤ n - 1 → j < a + k → ∀ (i : ℤ), i = j + 1 →
      ∃ (t : K.X j ⟶ K.X (j - 1)) (t' : K.X i ⟶ K.X j),
        t ≫ K.d (j - 1) j + K.d j i ≫ t' = 𝟙 (K.X j) by
    exact h (j - a + 1).toNat j hj (by omega)
  intro k
  induction k with
  | zero =>
    intro j hjn hja i hi
    exact ⟨0, 0, (K.isZero_of_isStrictlyGE a j (by omega)).eq_of_src _ _⟩
  | succ k ih =>
    intro j hjn hja i hi
    subst hi
    by_cases hj' : j < a + k
    · exact ih j hjn hj' _ rfl
    · -- construct the next step of the contraction from the previous one
      obtain ⟨t, t', E⟩ := ih (j - 1) (by omega) (by omega) j (by ring)
      -- `E : t ≫ K.d (j - 1 - 1) (j - 1) + K.d (j - 1) j ≫ t' = 𝟙 (K.X (j - 1))`
      have hdt' : K.d (j - 1) j ≫ t' = 𝟙 (K.X (j - 1)) - t ≫ K.d (j - 1 - 1) (j - 1) := by
        rw [← E]
        abel
      set θ : K.X j ⟶ K.X j := 𝟙 (K.X j) - t' ≫ K.d (j - 1) j with hθdef
      have hθ : K.d (j - 1) j ≫ θ = 0 := by
        rw [hθdef, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hdt',
          Preadditive.sub_comp, Category.id_comp, Category.assoc,
          HomologicalComplex.d_comp_d, comp_zero, sub_zero, sub_self]
      haveI : Injective (K.X j) := hinj j
      obtain ⟨s, hs⟩ := exists_comp_d_eq_of_exactAt rfl (hex j (by omega)) θ hθ
      exact ⟨t', s, by rw [hs, hθdef]; abel⟩

/-- **Low-degree exactness of images of resolutions.** If `K` is a bounded below
complex of injectives which is exact in all degrees `< n`, then for any additive
functor `F`, the complex `F(K)` is exact in all degrees `≤ n - 2`. -/
lemma exactAt_mapHomologicalComplex_of_exact_lowDegree
    {B : Type u} [Category.{v} B] [Abelian B] (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) (a : ℤ) (hge : K.IsStrictlyGE a)
    (hinj : ∀ i, Injective (K.X i)) (n : ℤ) (hex : ∀ i, i < n → K.ExactAt i)
    (m : ℤ) (hm : m ≤ n - 2) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt m := by
  obtain ⟨t, t', E⟩ := exists_contraction_of_exact_of_injective K a hge hinj n hex m
    (by omega) (m + 1) rfl
  set L := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K with hL
  have EF : F.map t ≫ L.d (m - 1) m + L.d m (m + 1) ≫ F.map t' = 𝟙 (L.X m) := by
    have h := congrArg F.map E
    rw [F.map_add, F.map_comp, F.map_comp, F.map_id] at h
    exact h
  rw [HomologicalComplex.exactAt_iff' L (m - 1) m (m + 1) (by simp) (by simp)]
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  have hx' : x ≫ L.d m (m + 1) = 0 := hx
  refine ⟨T, 𝟙 T, inferInstance, x ≫ F.map t, ?_⟩
  have h2 : x ≫ (F.map t ≫ L.d (m - 1) m) + x ≫ (L.d m (m + 1) ≫ F.map t') = x := by
    rw [← Preadditive.comp_add, EF, Category.comp_id]
  have h3 : x ≫ (L.d m (m + 1) ≫ F.map t') = 0 := by
    rw [← Category.assoc, hx', zero_comp]
  calc 𝟙 T ≫ x = x := by rw [Category.id_comp]
    _ = x ≫ (F.map t ≫ L.d (m - 1) m) := by rw [← h2, h3, add_zero]
    _ = (x ≫ F.map t) ≫ L.d (m - 1) m := by rw [Category.assoc]

/-- An exact functor between abelian categories preserves exactness of cochain
complexes in each degree. -/
lemma exactAt_mapHomologicalComplex_of_exactAt
    {B : Type u} [Category.{v} B] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) {i : ℤ} (hK : K.ExactAt i) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt i :=
  ShortComplex.Exact.map hK F

end LowDegree

/-! ## The derived base change transformation on fibrant complexes -/

namespace AlgebraicGeometry.Scheme

open CochainComplex.Plus.modelCategoryQuillen

variable {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X'.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S'.smallEtaleTopology Ab.{u + 1})]

/- Cache several heavy type class instances on the sheaf categories, to avoid
deterministic time-outs in later searches. -/

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
noncomputable instance : Abelian (Sheaf X.smallEtaleTopology Ab.{u + 1}) := inferInstance

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
noncomputable instance : Abelian (Sheaf X'.smallEtaleTopology Ab.{u + 1}) := inferInstance

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
noncomputable instance : Abelian (Sheaf S'.smallEtaleTopology Ab.{u + 1}) := inferInstance

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
noncomputable instance :
    EnoughInjectives (Sheaf X.smallEtaleTopology Ab.{u + 1}) := inferInstance

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
noncomputable instance :
    EnoughInjectives (Sheaf X'.smallEtaleTopology Ab.{u + 1}) := inferInstance

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
noncomputable instance : HasFiniteLimits
    (CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) := inferInstance

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
noncomputable instance : HasFiniteLimits
    (CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})) := inferInstance

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
noncomputable instance : HasLimitsOfShape (Discrete PEmpty.{1})
    (CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) := inferInstance

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
noncomputable instance : HasLimitsOfShape (Discrete PEmpty.{1})
    (CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})) := inferInstance

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
noncomputable instance : HasTerminal
    (CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) := inferInstance

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 4000000 in
noncomputable instance : HasTerminal
    (CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})) := inferInstance

/-- The class of bounded below complexes of abelian sheaves on the small étale site of
`X` on which the derived base change transformation is an isomorphism. -/
def BaseChangeIso
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) : Prop :=
  IsIso ((derivedBaseChangeNatTrans f g f' g' w).app
    ((DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).obj M))

/-- The class `BaseChangeIso` is invariant under quasi-isomorphisms. -/
lemma baseChangeIso_iff_of_quasiIso
    {M N : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})} (ψ : M ⟶ N)
    (hψ : QuasiIso ψ.hom) :
    BaseChangeIso f g f' g' w M ↔ BaseChangeIso f g f' g' w N := by
  haveI : IsIso ((DerivedCategoryPlus.Q
      (Sheaf X.smallEtaleTopology Ab.{u + 1})).map ψ) :=
    (DerivedCategoryPlus.isIso_Q_map_iff_quasiIso ψ).mpr hψ
  exact NatTrans.isIso_app_iff_of_isIso (derivedBaseChangeNatTrans f g f' g' w)
    ((DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).map ψ)

/-- On a fibrant bounded below complex (i.e., a bounded below complex of injectives),
the left unit of the derived base change transformation is an isomorphism. -/
lemma isIso_derivedBaseChangeUnitLeft_app
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) [IsFibrant M] :
    IsIso ((derivedBaseChangeUnitLeft f g).app M) := by
  dsimp only [derivedBaseChangeUnitLeft]
  rw [NatTrans.comp_app, NatTrans.comp_app]
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app]
  haveI := (etalePushforward f).isIso_rightDerivedPlusUnit_app (FibrantObject.mk M)
  infer_instance

/-- The comparison morphism `g^* f_* M ⟶ f'_* J` of bounded below complexes attached
to a replacement `j : g'^* M ⟶ J`. If `M` is fibrant and `j` is a fibrant replacement,
the derived base change transformation at `Q.obj M` is an isomorphism iff this concrete
morphism of complexes is a quasi-isomorphism. -/
noncomputable def baseChangeComparison
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    {J : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})}
    (j : (etalePullback g').mapCochainComplexPlus.obj M ⟶ J) :
    (etalePushforward f ⋙ etalePullback g).mapCochainComplexPlus.obj M ⟶
      (etalePushforward f').mapCochainComplexPlus.obj J :=
  (NatTrans.mapCochainComplexPlus (etaleBaseChangeNatTrans f g f' g' w)).app M ≫
    (Functor.mapCochainComplexPlusComp (etalePullback g')
      (etalePushforward f')).hom.app M ≫
    (etalePushforward f').mapCochainComplexPlus.map j

/-- **Factorization of the derived base change transformation on fibrant objects**:
for a fibrant bounded below complex `M` on `X_ét` and a fibrant replacement
`j : g'^* M ⟶ J`, the value of the derived base change transformation at `Q.obj M`
equals, up to composition with isomorphisms on both sides, the image under `Q` of the
concrete comparison morphism `g^* f_* M ⟶ f'_* J`. -/
lemma exists_fac_derivedBaseChangeNatTrans_app
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) [IsFibrant M]
    {J : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})} [IsFibrant J]
    (j : (etalePullback g').mapCochainComplexPlus.obj M ⟶ J) (hj : QuasiIso j.hom) :
    ∃ (uL : (DerivedCategoryPlus.Q _).obj
        ((etalePushforward f ⋙ etalePullback g).mapCochainComplexPlus.obj M) ⟶
        (derivedPushforward f ⋙ derivedPullback g).obj ((DerivedCategoryPlus.Q _).obj M))
      (tail : (DerivedCategoryPlus.Q _).obj
        ((etalePushforward f').mapCochainComplexPlus.obj J) ⟶
        (derivedPullback g' ⋙ derivedPushforward f').obj ((DerivedCategoryPlus.Q _).obj M)),
      IsIso uL ∧ IsIso tail ∧
      uL ≫ (derivedBaseChangeNatTrans f g f' g' w).app ((DerivedCategoryPlus.Q _).obj M) =
        (DerivedCategoryPlus.Q _).map (baseChangeComparison f g f' g' w M j) ≫ tail := by
  -- Step 1: the factorization property of the right derived descent
  have fac : (derivedBaseChangeUnitLeft f g).app M ≫
      (derivedBaseChangeNatTrans f g f' g' w).app ((DerivedCategoryPlus.Q _).obj M) =
        (derivedBaseChangeUnitRight f g f' g' w).app M :=
    Functor.rightDerived_fac_app _ (derivedBaseChangeUnitLeft f g)
      (CochainComplex.Plus.quasiIso _) _ (derivedBaseChangeUnitRight f g f' g' w) M
  -- Step 2: the left unit is invertible on fibrant objects
  haveI hL : IsIso ((derivedBaseChangeUnitLeft f g).app M) :=
    isIso_derivedBaseChangeUnitLeft_app f g M
  -- Step 3: unfold the right unit
  have happ : (derivedBaseChangeUnitRight f g f' g' w).app M =
      (DerivedCategoryPlus.Q _).map
        ((NatTrans.mapCochainComplexPlus (etaleBaseChangeNatTrans f g f' g' w)).app M) ≫
      (DerivedCategoryPlus.Q _).map
        ((Functor.mapCochainComplexPlusComp (etalePullback g')
          (etalePushforward f')).hom.app M) ≫
      ((etalePushforward f').rightDerivedPlusUnit).app
        ((etalePullback g').mapCochainComplexPlus.obj M) ≫
      (derivedPushforward f').map
        (((etalePullback g').mapDerivedCategoryPlusFactors).inv.app M) := by
    dsimp only [derivedBaseChangeUnitRight]
    rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app]
    simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app]
  -- Step 4: replace the unit at `g'^* M` using naturality along `j`
  haveI huJ : IsIso (((etalePushforward f').rightDerivedPlusUnit).app J) := by
    haveI := (etalePushforward f').isIso_rightDerivedPlusUnit_app (FibrantObject.mk J)
    exact this
  haveI hQj : IsIso ((DerivedCategoryPlus.Q _).map j) :=
    (DerivedCategoryPlus.isIso_Q_map_iff_quasiIso j).mpr hj
  have hunit : ((etalePushforward f').rightDerivedPlusUnit).app
      ((etalePullback g').mapCochainComplexPlus.obj M) =
      ((DerivedCategoryPlus.Q _).map ((etalePushforward f').mapCochainComplexPlus.map j) ≫
        ((etalePushforward f').rightDerivedPlusUnit).app J) ≫
        inv ((derivedPushforward f').map ((DerivedCategoryPlus.Q _).map j)) := by
    refine (IsIso.eq_comp_inv _).mpr ?_
    exact (((etalePushforward f').rightDerivedPlusUnit).naturality j).symm
  -- Step 5: assemble
  have hcomp : (DerivedCategoryPlus.Q _).map (baseChangeComparison f g f' g' w M j) =
      (DerivedCategoryPlus.Q _).map
        ((NatTrans.mapCochainComplexPlus (etaleBaseChangeNatTrans f g f' g' w)).app M) ≫
      (DerivedCategoryPlus.Q _).map
        ((Functor.mapCochainComplexPlusComp (etalePullback g')
          (etalePushforward f')).hom.app M) ≫
      (DerivedCategoryPlus.Q _).map
        ((etalePushforward f').mapCochainComplexPlus.map j) := by
    simp only [baseChangeComparison, Functor.map_comp]
  have hEq : (derivedBaseChangeUnitRight f g f' g' w).app M =
      (DerivedCategoryPlus.Q _).map (baseChangeComparison f g f' g' w M j) ≫
      (((etalePushforward f').rightDerivedPlusUnit).app J ≫
        inv ((derivedPushforward f').map ((DerivedCategoryPlus.Q _).map j)) ≫
        (derivedPushforward f').map
          (((etalePullback g').mapDerivedCategoryPlusFactors).inv.app M)) := by
    rw [happ, hunit, hcomp]
    simp only [Category.assoc]
  exact ⟨(derivedBaseChangeUnitLeft f g).app M, _, hL, inferInstance, fac.trans hEq⟩

/-- **Unfolding of the derived base change transformation on fibrant objects**: for a
fibrant bounded below complex `M` on `X_ét` and a fibrant replacement `j : g'^* M ⟶ J`,
the derived base change transformation is an isomorphism at `Q.obj M` iff the concrete
comparison morphism `g^* f_* M ⟶ f'_* J` is a quasi-isomorphism. -/
lemma baseChangeIso_iff_quasiIso_baseChangeComparison
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) [IsFibrant M]
    {J : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})} [IsFibrant J]
    (j : (etalePullback g').mapCochainComplexPlus.obj M ⟶ J) (hj : QuasiIso j.hom) :
    BaseChangeIso f g f' g' w M ↔
      QuasiIso (baseChangeComparison f g f' g' w M j).hom := by
  obtain ⟨uL, tail, hu, ht, heq⟩ :=
    exists_fac_derivedBaseChangeNatTrans_app f g f' g' w M j hj
  have h1 : BaseChangeIso f g f' g' w M ↔
      IsIso ((DerivedCategoryPlus.Q _).map (baseChangeComparison f g f' g' w M j) ≫
        tail) := by
    unfold BaseChangeIso
    rw [← heq, isIso_comp_left_iff]
  rw [h1, isIso_comp_right_iff]
  exact DerivedCategoryPlus.isIso_Q_map_iff_quasiIso _

/-- Per-degree version of
`baseChangeIso_iff_quasiIso_baseChangeComparison`: on a fibrant complex, the induced
map on the `q`-th homology of the derived base change transformation is an isomorphism
iff the `q`-th homology of the concrete comparison morphism is. -/
lemma isIso_homologyMap_baseChangeComparison_iff
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1})) [IsFibrant M]
    {J : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1})} [IsFibrant J]
    (j : (etalePullback g').mapCochainComplexPlus.obj M ⟶ J) (hj : QuasiIso j.hom)
    (q : ℤ) :
    IsIso ((DerivedCategoryPlus.homologyFunctor
        (Sheaf S'.smallEtaleTopology Ab.{u + 1}) q).map
      ((derivedBaseChangeNatTrans f g f' g' w).app ((DerivedCategoryPlus.Q _).obj M))) ↔
    IsIso (HomologicalComplex.homologyMap
      (baseChangeComparison f g f' g' w M j).hom q) := by
  obtain ⟨uL, tail, hu, ht, heq⟩ :=
    exists_fac_derivedBaseChangeNatTrans_app f g f' g' w M j hj
  have h2 : (DerivedCategoryPlus.homologyFunctor _ q).map uL ≫
      (DerivedCategoryPlus.homologyFunctor _ q).map
        ((derivedBaseChangeNatTrans f g f' g' w).app ((DerivedCategoryPlus.Q _).obj M)) =
      (DerivedCategoryPlus.homologyFunctor _ q).map
        ((DerivedCategoryPlus.Q _).map (baseChangeComparison f g f' g' w M j)) ≫
      (DerivedCategoryPlus.homologyFunctor _ q).map tail := by
    rw [← Functor.map_comp, heq, Functor.map_comp]
  haveI : IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map uL) := inferInstance
  haveI : IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map tail) := inferInstance
  rw [← isIso_comp_left_iff ((DerivedCategoryPlus.homologyFunctor _ q).map uL), h2,
    isIso_comp_right_iff]
  have key : IsIso ((DerivedCategoryPlus.Q _ ⋙
      DerivedCategoryPlus.homologyFunctor _ q).map
        (baseChangeComparison f g f' g' w M j)) ↔
      IsIso ((CochainComplex.Plus.ι _ ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q).map
          (baseChangeComparison f g f' g' w M j)) := by
    rw [← NatIso.naturality_1 (DerivedCategoryPlus.homologyFunctorFactors _ q)
      (baseChangeComparison f g f' g' w M j), isIso_comp_left_iff, isIso_comp_right_iff]
  exact key

/-- The induced maps on homology of the derived base change transformation transfer
along isomorphisms in the derived category. -/
lemma isIso_homologyMap_derivedBaseChangeNatTrans_app_iff_of_isIso
    {K₁ K₂ : DerivedCategoryPlus (Sheaf X.smallEtaleTopology Ab.{u + 1})} (e : K₁ ⟶ K₂)
    [IsIso e] (q : ℤ) :
    IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map
      ((derivedBaseChangeNatTrans f g f' g' w).app K₁)) ↔
    IsIso ((DerivedCategoryPlus.homologyFunctor _ q).map
      ((derivedBaseChangeNatTrans f g f' g' w).app K₂)) :=
  NatTrans.isIso_app_iff_of_isIso
    (Functor.whiskerRight (derivedBaseChangeNatTrans f g f' g' w)
      (DerivedCategoryPlus.homologyFunctor _ q)) e

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
      exact Φ.comm₁₂.symm)
  have sq₂₃ := baseChangeComparison_naturality f g f' g' w
    (M₁ := ⟨T.X₂, p₂⟩) (M₂ := ⟨T.X₃, p₃⟩) (ObjectProperty.homMk T.g)
    (J₁ := ⟨U'.X₂, q₂⟩) (J₂ := ⟨U'.X₃, q₃⟩) (ObjectProperty.homMk U'.g) j₂ j₃
    (by
      apply (CochainComplex.Plus.fullyFaithfulι _).map_injective
      exact Φ.comm₂₃.symm)
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
      haveI := hΦ₃
      exact (HomologicalComplex.exactAt_iff_of_quasiIsoAt Φ.τ₃ i).mp hUi

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

/-! ## Two-term acyclic complexes and short exact sequences of singles -/

section SingleDouble

open HomologicalComplex ZeroObject

variable {A : Type u'} [Category.{v'} A] [Abelian A]

/-- Any morphism between zero objects is an isomorphism. -/
lemma isIso_of_isZero_of_isZero {P Q : A} (hP : IsZero P) (hQ : IsZero Q) (φ : P ⟶ Q) :
    IsIso φ :=
  ⟨0, hP.eq_of_src _ _, hQ.eq_of_src _ _⟩

/-- A short complex whose first term is zero and whose second map is an isomorphism is
short exact. -/
lemma CategoryTheory.ShortComplex.shortExact_of_isZero_X₁_of_isIso_g
    (T : ShortComplex A) (h₁ : IsZero T.X₁) (hg : IsIso T.g) : T.ShortExact := by
  have hmono : Mono T.f := ⟨fun _ _ _ => h₁.eq_of_tgt _ _⟩
  have hepi : Epi T.g := inferInstance
  have hexact : T.Exact := (T.exact_iff_mono (h₁.eq_of_src _ _)).mpr inferInstance
  exact { exact := hexact, mono_f := hmono, epi_g := hepi }

/-- A short complex whose third term is zero and whose first map is an isomorphism is
short exact. -/
lemma CategoryTheory.ShortComplex.shortExact_of_isIso_f_of_isZero_X₃
    (T : ShortComplex A) (hf : IsIso T.f) (h₃ : IsZero T.X₃) : T.ShortExact := by
  have hmono : Mono T.f := inferInstance
  have hepi : Epi T.g := ⟨fun _ _ _ => h₃.eq_of_src _ _⟩
  have hexact : T.Exact := (T.exact_iff_epi (h₃.eq_of_tgt _ _)).mpr inferInstance
  exact { exact := hexact, mono_f := hmono, epi_g := hepi }

variable (F : A) (n : ℤ)

/-- The two-term complex `⋯ ⟶ 0 ⟶ F ⟶ F ⟶ 0 ⟶ ⋯` (identity differential) in degrees
`n` and `n + 1`. -/
noncomputable abbrev idDouble : CochainComplex A ℤ :=
  HomologicalComplex.double (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)

lemma idDouble_plus : CochainComplex.plus A (idDouble F n) := by
  refine ⟨n, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact isZero_double_X _ _ i (by lia) (by lia)

/-- The two-term complex `idDouble` is acyclic. -/
lemma idDouble_exactAt (i : ℤ) : (idDouble F n).ExactAt i := by
  by_cases hi₀ : i = n
  · subst hi₀
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
    refine (ShortComplex.exact_iff_mono _
      (double_d_eq_zero₀ (𝟙 F) _ (n - 1) n (by lia))).mpr ?_
    rw [HomologicalComplex.double_d (𝟙 F) _ (by lia)]
    infer_instance
  · by_cases hi₁ : i = n + 1
    · subst hi₁
      rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
      refine (ShortComplex.exact_iff_epi _
        (double_d_eq_zero₀ (𝟙 F) _ (n + 1) (n + 2) (by lia))).mpr ?_
      rw [HomologicalComplex.double_d (𝟙 F) _ (by lia)]
      infer_instance
    · exact HomologicalComplex.ExactAt.of_isZero _ (isZero_double_X _ _ i hi₀ hi₁)

/-- The short exact sequence `0 ⟶ single (n+1) F ⟶ idDouble F n ⟶ single n F ⟶ 0`. -/
noncomputable def singleDoubleSES : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk
    (HomologicalComplex.mkHomFromSingle
      ((doubleXIso₁ (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)
        (by lia)).inv)
      (fun k hk => by
        rw [double_d_eq_zero₀ (𝟙 F) _ (n + 1) k (by lia), comp_zero]))
    (HomologicalComplex.mkHomFromDouble _ (by lia)
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n F).inv) 0
      (by simp) (fun k _ => zero_comp))
    (by
      ext k
      by_cases hk : k = n + 1
      · subst hk
        simp
      · exact (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) (n + 1) F k hk).eq_of_src _ _)

@[simp] lemma singleDoubleSES_X₁ :
    (singleDoubleSES F n).X₁ =
      (HomologicalComplex.single A (ComplexShape.up ℤ) (n + 1)).obj F := rfl

@[simp] lemma singleDoubleSES_X₂ : (singleDoubleSES F n).X₂ = idDouble F n := rfl

@[simp] lemma singleDoubleSES_X₃ :
    (singleDoubleSES F n).X₃ =
      (HomologicalComplex.single A (ComplexShape.up ℤ) n).obj F := rfl

lemma singleDoubleSES_shortExact : (singleDoubleSES F n).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro k
  by_cases hk₁ : k = n + 1
  · subst hk₁
    refine ShortComplex.shortExact_of_isIso_f_of_isZero_X₃ _ ?_ ?_
    · have : ((singleDoubleSES F n).f).f (n + 1) =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (n + 1) F).hom ≫
            (doubleXIso₁ (𝟙 F) _ (by lia)).inv :=
        HomologicalComplex.mkHomFromSingle_f _ _
      change IsIso (((singleDoubleSES F n).f).f (n + 1))
      rw [this]
      infer_instance
    · exact HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) n F (n + 1) (by lia)
  · by_cases hk₀ : k = n
    · subst hk₀
      refine ShortComplex.shortExact_of_isZero_X₁_of_isIso_g _ ?_ ?_
      · exact HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) (n + 1) F n (by lia)
      · have : ((singleDoubleSES F n).g).f n =
            (doubleXIso₀ (𝟙 F) _).hom ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n F).inv :=
          HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _
        change IsIso (((singleDoubleSES F n).g).f n)
        rw [this]
        infer_instance
    · refine ShortComplex.shortExact_of_isZero_X₁_of_isIso_g _ ?_ ?_
      · exact HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) (n + 1) F k hk₁
      · exact isIso_of_isZero_of_isZero
          (isZero_double_X _ _ k hk₀ hk₁)
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n F k hk₀) _

end SingleDouble

/-! ## Singles in all degrees, acyclic complexes, and the dévissage -/


namespace AlgebraicGeometry.Scheme

open CochainComplex.Plus.modelCategoryQuillen HomologicalComplex ZeroObject

variable {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X'.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S'.smallEtaleTopology Ab.{u + 1})]

/-- The single-sheaf hypothesis of the dévissage: the derived base change
transformation is an isomorphism on every locally torsion abelian sheaf placed in
degree `0`. -/
def SingleBaseChangeHyp : Prop :=
  ∀ (F : Sheaf X.smallEtaleTopology Ab.{u + 1}), Sheaf.IsLocallyTorsion F →
    IsIso ((derivedBaseChangeNatTrans f g f' g' w).app
      ((DerivedCategoryPlus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))

/-- The derived base change transformation is an isomorphism on acyclic complexes,
assuming the single-sheaf hypothesis. -/
lemma baseChangeIso_of_acyclic (H : SingleBaseChangeHyp f g f' g' w)
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hM : ∀ i, M.obj.ExactAt i) : BaseChangeIso f g f' g' w M := by
  have h0 : BaseChangeIso f g f' g' w
      ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj 0, ⟨0, inferInstance⟩⟩ :=
    H 0 (Sheaf.isLocallyTorsion_of_isZero (isZero_zero _))
  refine (baseChangeIso_iff_of_quasiIso f g f' g' w
    (ObjectProperty.homMk (0 : M.obj ⟶ _)) ?_).mpr h0
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_exactAt _ i (hM i)]
  by_cases hi : i = 0
  · subst hi
    exact HomologicalComplex.ExactAt.of_isZero _
      (IsZero.of_iso (isZero_zero _) (HomologicalComplex.singleObjXSelf _ 0 0))
  · exact HomologicalComplex.ExactAt.of_isZero _
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

/-- The derived base change transformation is an isomorphism on all singles of locally
torsion sheaves, in any degree, assuming the single-sheaf hypothesis in degree `0`. -/
lemma baseChangeIso_single (H : SingleBaseChangeHyp f g f' g' w)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) (hF : Sheaf.IsLocallyTorsion F) :
    ∀ (n : ℤ), BaseChangeIso f g f' g' w
      ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj F, ⟨n, inferInstance⟩⟩ := by
  -- both induction steps go through the short exact sequence `singleDoubleSES F n`
  have hdouble : ∀ n : ℤ, BaseChangeIso f g f' g' w ⟨idDouble F n, idDouble_plus F n⟩ :=
    fun n => baseChangeIso_of_acyclic f g f' g' w H _ (idDouble_exactAt F n)
  have hup : ∀ n : ℤ, BaseChangeIso f g f' g' w
      ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj F, ⟨n, inferInstance⟩⟩ →
      BaseChangeIso f g f' g' w
        ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) (n + 1)).obj F,
          ⟨n + 1, inferInstance⟩⟩ := by
    intro n hn
    exact baseChangeIso_X₁ f g f' g' w (singleDoubleSES F n)
      (singleDoubleSES_shortExact F n) ⟨n + 1, inferInstance⟩ (idDouble_plus F n)
      ⟨n, inferInstance⟩ (hdouble n) hn
  have hdown : ∀ n : ℤ, BaseChangeIso f g f' g' w
      ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) (n + 1)).obj F,
        ⟨n + 1, inferInstance⟩⟩ →
      BaseChangeIso f g f' g' w
        ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj F, ⟨n, inferInstance⟩⟩ := by
    intro n hn
    exact baseChangeIso_X₃ f g f' g' w (singleDoubleSES F n)
      (singleDoubleSES_shortExact F n) ⟨n + 1, inferInstance⟩ (idDouble_plus F n)
      ⟨n, inferInstance⟩ hn (hdouble n)
  intro n
  induction n using Int.induction_on with
  | hz => exact H F hF
  | hp k ih => exact hup k ih
  | hn k ih =>
    refine hdown (-(k + 1 : ℕ) : ℤ) ?_
    have e : (-(k + 1 : ℕ) : ℤ) + 1 = -(k : ℕ) := by push_cast; ring
    rw [e]
    exact ih

/-- Peeling off the top cohomological degree: if `K` is cohomologically bounded above
by `b` with locally torsion homology and the canonical truncation `τ_{≤ b - 1} K`
satisfies `BaseChangeIso`, then so does `K`. The cokernel of `τ_{≤ b-1} K ⟶ K` is
quasi-isomorphic to a single in degree `b`. -/
lemma baseChangeIso_of_truncLE (H : SingleBaseChangeHyp f g f' g' w)
    (K : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ)
    (p : CochainComplex.plus _ K) (b : ℤ) [K.IsLE b]
    (hT : ∀ n, Sheaf.IsLocallyTorsion (K.homology n))
    (h₁ : ∀ (p₁ : CochainComplex.plus _ (K.truncLE (b - 1))),
      BaseChangeIso f g f' g' w ⟨K.truncLE (b - 1), p₁⟩) :
    BaseChangeIso f g f' g' w ⟨K, p⟩ := by
  obtain ⟨a, ha⟩ := id p
  haveI := ha
  -- the short exact sequence `0 ⟶ τ_{≤ b-1} K ⟶ K ⟶ X₃ ⟶ 0`
  have hSq : (K.shortComplexTruncLE (b - 1)).ShortExact :=
    K.shortComplexTruncLE_shortExact (b - 1)
  -- the third term is quasi-isomorphic to `τ_{≥ b} K`
  let ρ : (K.shortComplexTruncLE (b - 1)).X₃ ⟶ K.truncGE b :=
    K.shortComplexTruncLEX₃ToTruncGE (b - 1) b (by lia)
  haveI hρ : QuasiIso ρ := by
    dsimp [ρ]
    infer_instance
  -- `τ_{≥ b} K` is cohomologically concentrated in degree `b`
  haveI : (K.truncGE b).IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    haveI := K.quasiIsoAt_πTruncGE b i (by lia)
    exact (HomologicalComplex.exactAt_iff_of_quasiIsoAt (K.πTruncGE b) i).mp
      (K.exactAt_of_isLE b i hi)
  -- its truncation `τ_{≤ b}` is concentrated in degree `b` and isomorphic to a single
  obtain ⟨W, ⟨eY⟩⟩ := CochainComplex.exists_iso_single ((K.truncGE b).truncLE b) b
  -- `W` is locally torsion, being isomorphic to `H^b K`
  have hW : Sheaf.IsLocallyTorsion W := by
    haveI := K.quasiIsoAt_πTruncGE b b (le_refl b)
    haveI := (K.truncGE b).quasiIsoAt_ιTruncLE b b (le_refl b)
    have hiso₁ : IsIso (HomologicalComplex.homologyMap (K.πTruncGE b) b) := by
      rw [← quasiIsoAt_iff_isIso_homologyMap]
      infer_instance
    have hiso₂ : IsIso (HomologicalComplex.homologyMap ((K.truncGE b).ιTruncLE b) b) := by
      rw [← quasiIsoAt_iff_isIso_homologyMap]
      infer_instance
    refine Sheaf.IsLocallyTorsion.of_iso ?_ (hT b)
    exact (asIso (HomologicalComplex.homologyMap (K.πTruncGE b) b)) ≪≫
      (asIso (HomologicalComplex.homologyMap ((K.truncGE b).ιTruncLE b) b)).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) b).mapIso eY ≪≫
      (HomologicalComplex.homologyFunctorSingleIso
        (Sheaf X.smallEtaleTopology Ab.{u + 1}) (ComplexShape.up ℤ) b).app W
  -- plus-ness of all objects involved
  have pY : CochainComplex.plus _ ((K.truncGE b).truncLE b) := ⟨b, inferInstance⟩
  have pG : CochainComplex.plus _ (K.truncGE b) := ⟨b, inferInstance⟩
  have p₃ : CochainComplex.plus _ (K.shortComplexTruncLE (b - 1)).X₃ :=
    (CochainComplex.plus _).prop_colimit (parallelPair (K.ιTruncLE (b - 1)) 0) (fun j => by
      obtain (_ | _) := j
      · exact ⟨a, inferInstance⟩
      · exact ⟨a, ha⟩)
  -- transfer `BaseChangeIso` along the chain of quasi-isomorphisms
  have hsingle : BaseChangeIso f g f' g' w
      ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj W, ⟨b, inferInstance⟩⟩ :=
    baseChangeIso_single f g f' g' w H W hW b
  have hY : BaseChangeIso f g f' g' w ⟨(K.truncGE b).truncLE b, pY⟩ :=
    (baseChangeIso_iff_of_quasiIso f g f' g' w
      (M := ⟨(K.truncGE b).truncLE b, pY⟩)
      (N := ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj W, ⟨b, inferInstance⟩⟩)
      (ObjectProperty.homMk eY.hom) inferInstance).mpr hsingle
  have hG : BaseChangeIso f g f' g' w ⟨K.truncGE b, pG⟩ :=
    (baseChangeIso_iff_of_quasiIso f g f' g' w
      (M := ⟨(K.truncGE b).truncLE b, pY⟩) (N := ⟨K.truncGE b, pG⟩)
      (ObjectProperty.homMk ((K.truncGE b).ιTruncLE b)) inferInstance).mp hY
  have h₃ : BaseChangeIso f g f' g' w ⟨(K.shortComplexTruncLE (b - 1)).X₃, p₃⟩ :=
    (baseChangeIso_iff_of_quasiIso f g f' g' w
      (M := ⟨(K.shortComplexTruncLE (b - 1)).X₃, p₃⟩) (N := ⟨K.truncGE b, pG⟩)
      (ObjectProperty.homMk ρ) hρ).mpr hG
  -- conclude by the two-out-of-three property
  have p₁ : CochainComplex.plus _ (K.truncLE (b - 1)) := ⟨a, inferInstance⟩
  exact baseChangeIso_X₂ f g f' g' w (K.shortComplexTruncLE (b - 1)) hSq
    p₁ p p₃ (h₁ p₁) h₃

/-- The bounded dévissage: the derived base change transformation is an isomorphism on
every bounded below complex with locally torsion homology which is moreover
cohomologically bounded above, assuming the single-sheaf hypothesis. -/
lemma baseChangeIso_of_isLE (H : SingleBaseChangeHyp f g f' g' w)
    (K : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ)
    (p : CochainComplex.plus _ K) (b : ℤ) (hb : K.IsLE b)
    (hT : ∀ n, Sheaf.IsLocallyTorsion (K.homology n)) :
    BaseChangeIso f g f' g' w ⟨K, p⟩ := by
  obtain ⟨a, ha⟩ := id p
  suffices h : ∀ (k : ℕ) (K : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ)
      (a b : ℤ), K.IsStrictlyGE a → K.IsLE b →
      (∀ n, Sheaf.IsLocallyTorsion (K.homology n)) → (b - a).toNat ≤ k →
      ∀ (p : CochainComplex.plus _ K), BaseChangeIso f g f' g' w ⟨K, p⟩ by
    exact h (b - a).toNat K a b ha hb hT le_rfl p
  intro k
  induction k with
  | zero =>
    intro K a b hge hle hT hk p
    haveI := hge
    haveI := hle
    have hba : b ≤ a := by omega
    by_cases hlt : b < a
    · -- `K` is acyclic
      refine baseChangeIso_of_acyclic f g f' g' w H _ (fun i => ?_)
      by_cases hia : i < a
      · exact K.exactAt_of_isGE a i hia
      · exact K.exactAt_of_isLE b i (by omega)
    · -- `b = a`: the truncation `τ_{≤ b - 1} K` is acyclic
      refine baseChangeIso_of_truncLE f g f' g' w H K p b hT (fun p₁ => ?_)
      refine baseChangeIso_of_acyclic f g f' g' w H _ (fun i => ?_)
      by_cases hib : b - 1 < i
      · exact (K.truncLE (b - 1)).exactAt_of_isLE (b - 1) i hib
      · haveI := K.quasiIsoAt_ιTruncLE (b - 1) i (by omega)
        exact (HomologicalComplex.exactAt_iff_of_quasiIsoAt (K.ιTruncLE (b - 1)) i).mpr
          (K.exactAt_of_isGE a i (by omega))
  | succ k ih =>
    intro K a b hge hle hT hk p
    haveI := hge
    haveI := hle
    by_cases hlt : b < a
    · refine baseChangeIso_of_acyclic f g f' g' w H _ (fun i => ?_)
      by_cases hia : i < a
      · exact K.exactAt_of_isGE a i hia
      · exact K.exactAt_of_isLE b i (by omega)
    · refine baseChangeIso_of_truncLE f g f' g' w H K p b hT (fun p₁ => ?_)
      haveI : (K.truncLE (b - 1)).IsLE (b - 1) := by
        rw [CochainComplex.isLE_iff]
        intro i hi
        exact (K.truncLE (b - 1)).exactAt_of_isLE (b - 1) i hi
      refine ih (K.truncLE (b - 1)) a (b - 1) inferInstance inferInstance ?_ (by omega) p₁
      intro n
      by_cases hn : n ≤ b - 1
      · haveI := K.quasiIsoAt_ιTruncLE (b - 1) n hn
        have hiso : IsIso (HomologicalComplex.homologyMap (K.ιTruncLE (b - 1)) n) := by
          rw [← quasiIsoAt_iff_isIso_homologyMap]
          infer_instance
        exact Sheaf.IsLocallyTorsion.of_iso
          (asIso (HomologicalComplex.homologyMap (K.ιTruncLE (b - 1)) n)).symm (hT n)
      · exact Sheaf.isLocallyTorsion_of_isZero
          (((K.truncLE (b - 1)).exactAt_of_isLE (b - 1) n (by omega)).isZero_homology)

/-- **Dévissage in `K` for the proper base change theorem, bounded case**: if the
derived base change transformation is an isomorphism on every locally torsion abelian
sheaf placed in degree `0`, then it is an isomorphism on every complex with locally
torsion cohomology which is moreover cohomologically bounded above. -/
theorem isIso_derivedBaseChangeNatTrans_app_of_singleFunctor_of_isLE
    (H : ∀ (F : Sheaf X.smallEtaleTopology Ab.{u + 1}), Sheaf.IsLocallyTorsion F →
      IsIso ((derivedBaseChangeNatTrans f g f' g' w).app
        ((DerivedCategoryPlus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F)))
    (K : DerivedCategoryPlus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : ∀ n : ℤ, Sheaf.IsLocallyTorsion
      ((DerivedCategoryPlus.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K))
    (b : ℤ)
    (hb : ∀ n : ℤ, b ≤ n → IsZero
      ((DerivedCategoryPlus.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K)) :
    IsIso ((derivedBaseChangeNatTrans f g f' g' w).app K) := by
  haveI : (DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).EssSurj :=
    Localization.essSurj _ (CochainComplex.Plus.quasiIso _)
  obtain ⟨M, ⟨e⟩⟩ : ∃ M, Nonempty
      ((DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).obj M ≅ K) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ K⟩⟩
  rw [← NatTrans.isIso_app_iff_of_isIso (derivedBaseChangeNatTrans f g f' g' w) e.hom]
  have hfac : ∀ n : ℤ, (DerivedCategoryPlus.homologyFunctor
      (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K ≅ M.obj.homology n := fun n =>
    (DerivedCategoryPlus.homologyFunctor _ n).mapIso e.symm ≪≫
      (DerivedCategoryPlus.homologyFunctorFactors _ n).app M
  have hT : ∀ n, Sheaf.IsLocallyTorsion (M.obj.homology n) := fun n =>
    Sheaf.IsLocallyTorsion.of_iso (hfac n) (hK n)
  have hle : M.obj.IsLE (b - 1) := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hb i (by omega)).of_iso (hfac i).symm
  exact baseChangeIso_of_isLE f g f' g' w H M.obj M.2 (b - 1) hle hT

/-- **Dévissage in `K` for the proper base change theorem.** If the derived base
change transformation `Rf_* ⋙ g^* ⟶ g'^* ⋙ Rf'_*` is an isomorphism on every locally
torsion abelian sheaf placed in degree `0` of the bounded below derived category, then
it is an isomorphism on every bounded below complex with locally torsion cohomology
sheaves. -/
theorem isIso_derivedBaseChangeNatTrans_app_of_singleFunctor
    (H : ∀ (F : Sheaf X.smallEtaleTopology Ab.{u + 1}), Sheaf.IsLocallyTorsion F →
      IsIso ((derivedBaseChangeNatTrans f g f' g' w).app
        ((DerivedCategoryPlus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F)))
    (K : DerivedCategoryPlus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : ∀ n : ℤ, Sheaf.IsLocallyTorsion
      ((DerivedCategoryPlus.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K)) :
    IsIso ((derivedBaseChangeNatTrans f g f' g' w).app K) := by
  -- replace `K` by `Q.obj M` for a bounded below complex `M`
  haveI : (DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).EssSurj :=
    Localization.essSurj _ (CochainComplex.Plus.quasiIso _)
  obtain ⟨M, ⟨e⟩⟩ : ∃ M, Nonempty
      ((DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).obj M ≅ K) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ K⟩⟩
  rw [← NatTrans.isIso_app_iff_of_isIso (derivedBaseChangeNatTrans f g f' g' w) e.hom]
  have hfacM : ∀ n : ℤ, (DerivedCategoryPlus.homologyFunctor
      (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K ≅ M.obj.homology n := fun n =>
    (DerivedCategoryPlus.homologyFunctor _ n).mapIso e.symm ≪≫
      (DerivedCategoryPlus.homologyFunctorFactors _ n).app M
  -- replace `M` by a fibrant complex `R` (a bounded below complex of injectives)
  let R : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}) :=
    FibrantObject.HoCat.resolutionObj M
  let iR : M ⟶ R := FibrantObject.HoCat.iResolutionObj M
  have hiR : QuasiIso iR.hom := by
    rw [← modelCategoryQuillen.weakEquivalence_iff]
    infer_instance
  show BaseChangeIso f g f' g' w M
  rw [baseChangeIso_iff_of_quasiIso f g f' g' w iR hiR]
  -- the homology of `R` is locally torsion
  have hTR : ∀ n, Sheaf.IsLocallyTorsion (R.obj.homology n) := by
    intro n
    have hiso : IsIso (HomologicalComplex.homologyMap iR.hom n) := by
      rw [← quasiIsoAt_iff_isIso_homologyMap]
      infer_instance
    exact Sheaf.IsLocallyTorsion.of_iso
      (hfacM n ≪≫ asIso (HomologicalComplex.homologyMap iR.hom n)) (hK n)
  -- choose a fibrant replacement of `g'^* R` and reduce to a quasi-isomorphism claim
  let J : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1}) :=
    FibrantObject.HoCat.resolutionObj ((etalePullback g').mapCochainComplexPlus.obj R)
  let jJ : (etalePullback g').mapCochainComplexPlus.obj R ⟶ J :=
    FibrantObject.HoCat.iResolutionObj _
  have hjJ : QuasiIso jJ.hom := by
    rw [← modelCategoryQuillen.weakEquivalence_iff]
    infer_instance
  rw [baseChangeIso_iff_quasiIso_baseChangeComparison f g f' g' w R jJ hjJ]
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  -- reformulate via the homology of the derived transformation at `Q.obj R`
  rw [← isIso_homologyMap_baseChangeComparison_iff f g f' g' w R jJ hjJ q]
  -- the truncation short exact sequence at level `q + 2`
  have hSq : (R.obj.shortComplexTruncLE (q + 2)).ShortExact :=
    R.obj.shortComplexTruncLE_shortExact (q + 2)
  obtain ⟨a, ha⟩ := id R.2
  haveI := ha
  have p₁ : CochainComplex.plus _ (R.obj.truncLE (q + 2)) := ⟨a, inferInstance⟩
  -- the first term satisfies `BaseChangeIso` by the bounded dévissage
  have hX₁ : BaseChangeIso f g f' g' w ⟨R.obj.truncLE (q + 2), p₁⟩ := by
    haveI : (R.obj.truncLE (q + 2)).IsLE (q + 2) := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      exact (R.obj.truncLE (q + 2)).exactAt_of_isLE (q + 2) i hi
    refine baseChangeIso_of_isLE f g f' g' w H _ p₁ (q + 2) inferInstance (fun n => ?_)
    by_cases hn : n ≤ q + 2
    · haveI := R.obj.quasiIsoAt_ιTruncLE (q + 2) n hn
      have hiso : IsIso (HomologicalComplex.homologyMap (R.obj.ιTruncLE (q + 2)) n) := by
        rw [← quasiIsoAt_iff_isIso_homologyMap]
        infer_instance
      exact Sheaf.IsLocallyTorsion.of_iso
        (asIso (HomologicalComplex.homologyMap (R.obj.ιTruncLE (q + 2)) n)).symm (hTR n)
    · exact Sheaf.isLocallyTorsion_of_isZero
        (((R.obj.truncLE (q + 2)).exactAt_of_isLE (q + 2) n (by omega)).isZero_homology)
  -- the third term is exact in degrees `< q + 3`
  have hX₃exact : ∀ i, i < q + 3 → (R.obj.shortComplexTruncLE (q + 2)).X₃.ExactAt i := by
    intro i hi
    haveI : QuasiIso (R.obj.shortComplexTruncLEX₃ToTruncGE (q + 2) (q + 3) (by lia)) := by
      infer_instance
    refine (HomologicalComplex.exactAt_iff_of_quasiIsoAt
      (R.obj.shortComplexTruncLEX₃ToTruncGE (q + 2) (q + 3) (by lia)) i).mpr ?_
    exact (R.obj.truncGE (q + 3)).exactAt_of_isGE (q + 3) i hi
  -- resolve the truncation sequence by a fibrant one
  obtain ⟨T', Φ, hT', ⟨q₁', q₂', q₃'⟩, ⟨k₁', k₂', k₃'⟩, m₁, m₂, m₃⟩ :=
    CochainComplex.Plus.exists_fibrant_ses_resolution
      (R.obj.shortComplexTruncLE (q + 2)) hSq p₁ R.2
  -- the ladder attached to the fibrant resolution
  obtain ⟨R₁, R₂, Ψ, hR₁, hR₂, -, hdeg, hvan⟩ := exists_ladder_of_fibrant f g f' g' w
    T' hT' q₁' q₂' q₃' k₁' k₂' k₃'
  -- vanishing of the third column in the relevant degrees
  have hvan' : ∀ r, r ≤ q + 1 → (R₁.X₃.ExactAt r ∧ R₂.X₃.ExactAt r) := by
    refine fun r hr => hvan (q + 3) (fun i hi => ?_) r (by omega)
    haveI := m₃
    exact (HomologicalComplex.exactAt_iff_of_quasiIsoAt Φ.τ₃ i).mp (hX₃exact i hi)
  -- transfer of the per-degree statements from the truncation sequence to `T'`
  have htr₁ : ∀ r, IsIso ((DerivedCategoryPlus.homologyFunctor _ r).map
      ((derivedBaseChangeNatTrans f g f' g' w).app
        ((DerivedCategoryPlus.Q _).obj (⟨T'.X₁, q₁'⟩ : CochainComplex.Plus _)))) := by
    intro r
    have hBCI : BaseChangeIso f g f' g' w ⟨T'.X₁, q₁'⟩ :=
      (baseChangeIso_iff_of_quasiIso f g f' g' w (ObjectProperty.homMk Φ.τ₁) m₁).mp hX₁
    haveI : IsIso ((derivedBaseChangeNatTrans f g f' g' w).app
        ((DerivedCategoryPlus.Q _).obj (⟨T'.X₁, q₁'⟩ : CochainComplex.Plus _))) := hBCI
    infer_instance
  -- the five lemma in degree `q`
  have hτ₂ : IsIso (HomologicalComplex.homologyMap Ψ.τ₂ q) := by
    refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₂ Ψ hR₁ hR₂
      (q - 1) q (q + 1) (by simp) (by simp) ?_ ?_ ?_ ?_
    · -- `Epi` in degree `q - 1`: the target homology vanishes
      exact epi_of_isZero ((hvan' (q - 1) (by omega)).2.isZero_homology) _
    · exact ((hdeg q).1).mp (htr₁ q)
    · -- `IsIso` in degree `q`: both homologies vanish
      exact isIso_of_isZero_of_isZero
        ((hvan' q (by omega)).1.isZero_homology)
        ((hvan' q (by omega)).2.isZero_homology) _
    · haveI : IsIso (HomologicalComplex.homologyMap Ψ.τ₁ (q + 1)) :=
        ((hdeg (q + 1)).1).mp (htr₁ (q + 1))
      infer_instance
  -- transfer back to the comparison morphism for `R`
  have h₂' := ((hdeg q).2.1).mpr hτ₂
  haveI : IsIso ((DerivedCategoryPlus.Q
      (Sheaf X.smallEtaleTopology Ab.{u + 1})).map (ObjectProperty.homMk Φ.τ₂ :
        (⟨(R.obj.shortComplexTruncLE (q + 2)).X₂, R.2⟩ : CochainComplex.Plus _) ⟶
          ⟨T'.X₂, q₂'⟩)) :=
    (DerivedCategoryPlus.isIso_Q_map_iff_quasiIso _).mpr m₂
  exact (isIso_homologyMap_derivedBaseChangeNatTrans_app_iff_of_isIso f g f' g' w
    ((DerivedCategoryPlus.Q _).map (ObjectProperty.homMk Φ.τ₂ :
      (⟨(R.obj.shortComplexTruncLE (q + 2)).X₂, R.2⟩ : CochainComplex.Plus _) ⟶
        ⟨T'.X₂, q₂'⟩)) q).mpr h₂'

end AlgebraicGeometry.Scheme
