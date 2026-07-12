/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Homology.Double
import Proetale.Etale.ProperBaseChange

/-!
# Homological preliminaries for the proper base change dévissage

Generic abelian-category and cochain-complex lemmas supporting the dévissage of the
proper base change theorem (`Proetale/Etale/ProperBaseChangeDevissage.lean`):
five-lemma variants for the homology sequence, quasi-isomorphism saturation on the
bounded below derived category, a model-categorical horseshoe lemma, partial
contracting homotopies of low-degree-exact complexes of injectives, and the two-term
acyclic complexes linking consecutive singles.
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
lemma CategoryTheory.ShortComplex.ShortExact.map_mapHomologicalComplex
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
    have h : (ComplexShape.up ℤ).next i = i + 1 := CochainComplex.next ℤ i
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
  rw [HomologicalComplex.exactAt_iff'
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) (m - 1) m (m + 1)
      (by simp) (by simp),
    ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  have hx' : x ≫ F.map (K.d m (m + 1)) = 0 := hx
  refine ⟨T, 𝟙 T, inferInstance, x ≫ F.map t, ?_⟩
  have EF : F.map t ≫ F.map (K.d (m - 1) m) + F.map (K.d m (m + 1)) ≫ F.map t' =
      𝟙 (F.obj (K.X m)) := by
    have h := congrArg F.map E
    rw [F.map_add, F.map_comp, F.map_comp, F.map_id] at h
    exact h
  have h2 := congrArg (fun s => x ≫ s) EF
  simp only [Preadditive.comp_add] at h2
  have h4 : x ≫ 𝟙 (F.obj (K.X m)) = x := Category.comp_id x
  rw [h4] at h2
  rw [← Category.assoc x (F.map (K.d m (m + 1))) (F.map t'), hx', zero_comp,
    add_zero] at h2
  show 𝟙 T ≫ x = (x ≫ F.map t) ≫ F.map (K.d (m - 1) m)
  rw [Category.id_comp, Category.assoc]
  exact h2.symm

/-- An exact functor between abelian categories preserves exactness of cochain
complexes in each degree. -/
lemma exactAt_mapHomologicalComplex_of_exactAt
    {B : Type u} [Category.{v} B] [Abelian B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) {i : ℤ} (hK : K.ExactAt i) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt i :=
  ShortComplex.Exact.map hK F

end LowDegree

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
  · rw [hi₀]
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
    refine (ShortComplex.exact_iff_mono _
      (double_d_eq_zero₀ (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (n - 1) n
        (by lia))).mpr ?_
    show Mono ((idDouble F n).d n (n + 1))
    rw [HomologicalComplex.double_d (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)
      (by lia)]
    infer_instance
  · by_cases hi₁ : i = n + 1
    · subst hi₁
      rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
        (by simp <;> omega)]
      refine (ShortComplex.exact_iff_epi _
        (double_d_eq_zero₀ (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (n + 1)
          (n + 2) (by lia))).mpr ?_
      show Epi ((idDouble F n).d n (n + 1))
      rw [HomologicalComplex.double_d (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)
        (by lia)]
      infer_instance
    · exact HomologicalComplex.ExactAt.of_isZero (isZero_double_X _ _ i hi₀ hi₁)

/-- The short exact sequence `0 ⟶ single (n+1) F ⟶ idDouble F n ⟶ single n F ⟶ 0`. -/
noncomputable def singleDoubleSES : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk
    (HomologicalComplex.mkHomFromSingle
      ((doubleXIso₁ (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)
        (by lia)).inv)
      (fun k hk => by
        rw [double_d_eq_zero₀ (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (n + 1) k (by lia), comp_zero]))
    (HomologicalComplex.mkHomFromDouble (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (by lia)
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n F).inv) 0
      (by simp) (fun k _ => zero_comp))
    (by
      apply HomologicalComplex.hom_ext
      intro k
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
            (doubleXIso₁ (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (by lia)).inv :=
        HomologicalComplex.mkHomFromSingle_f
          ((doubleXIso₁ (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (by lia)).inv)
          (fun k hk => by
            rw [double_d_eq_zero₀ (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)
              (n + 1) k (by lia), comp_zero])
      change IsIso (((singleDoubleSES F n).f).f (n + 1))
      rw [this]
      infer_instance
    · exact HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) n F (n + 1) (by lia)
  · by_cases hk₀ : k = n
    · rw [hk₀]
      refine ShortComplex.shortExact_of_isZero_X₁_of_isIso_g _ ?_ ?_
      · exact HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) (n + 1) F n (by lia)
      · have : ((singleDoubleSES F n).g).f n =
            (doubleXIso₀ (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)).hom ≫
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n F).inv :=
          HomologicalComplex.mkHomFromDouble_f₀
            (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (by lia)
            ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n F).inv) 0
            (by simp) (fun k _ => zero_comp)
        change IsIso (((singleDoubleSES F n).g).f n)
        rw [this]
        infer_instance
    · refine ShortComplex.shortExact_of_isZero_X₁_of_isIso_g _ ?_ ?_
      · exact HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) (n + 1) F k hk₁
      · exact isIso_of_isZero_of_isZero
          (isZero_double_X (𝟙 F) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) k hk₀ hk₁)
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n F k hk₀) _

end SingleDouble
