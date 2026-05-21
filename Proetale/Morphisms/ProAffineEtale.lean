/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Proetale.Mathlib.Algebra.Category.Ring.FilteredDescent
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Ind
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads
import Proetale.Morphisms.WeaklyEtale
import Proetale.Algebra.IndEtale
import Proetale.Algebra.IndWeaklyEtale
import Proetale.Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
import Proetale.Topology.Coherent.Affine

/-!
# Pro-affine-étale morphisms

In this file we define the class of pro-affine-étale morphisms of schemes:
These are the morphisms of the form `lim Xᵢ ⟶ S` where each `Xᵢ` is absolutely affine
and étale over `X`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

/-- This is the property of morphisms of schemes that are of the form `lim Xᵢ ⟶ S`
where each `Xᵢ` is absolutely affine and étale over `X`. -/
def proAffineEtale : MorphismProperty Scheme.{u} :=
  MorphismProperty.pro.{u} (@Etale ⊓ .ofObjectProperty (IsAffine ·) ⊤)

lemma proAffineEtale.of_isAffine {X Y : Scheme.{u}} [IsAffine X] (f : X ⟶ Y) [Etale f] :
    proAffineEtale f :=
  MorphismProperty.le_pro _ _ ⟨‹_›, ⟨‹_›, trivial⟩⟩

/-- `IsAffine` is preserved under isomorphisms. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsAffine ·) where
  of_iso e h := (IsAffine.iff_of_isIso e.hom).mp h

instance : proAffineEtale.RespectsIso := by
  rw [proAffineEtale, pro_eq_unop_ind_op]
  infer_instance

/-- A pro-affine étale morphism cancels on the right against a pro-affine étale morphism.

Sketch: Given `g : Y ⟶ Z` and `f : X ⟶ Y` with `g` and `f ≫ g` pro-affine étale,
work with the affine reductions and use `PreProSpreads` (below) to lift `f ≫ g` to a
finite level of the cofiltered descent of `g`, then conclude `f` itself is pro-affine
étale by combining the two descents. -/
instance : proAffineEtale.HasOfPostcompProperty proAffineEtale := by
  -- The cleanest argument uses the equivalence between `pro` and `(ind ·.op).unop`
  -- combined with the dual `HasOfPrecompProperty` for `ind`. Currently this relies on
  -- the `PreProSpreads` instance below.
  -- Structural setup: both X and Y are affine, since the source of a `proAffineEtale`
  -- morphism is affine (this is `proAffineEtale_isAffine_source`, proved later in this
  -- file; we inline the affineness extraction here to avoid a forward reference).
  constructor
  intro X Y Z f g hg hfg
  -- Affineness of X via the data of `hfg : proAffineEtale (f ≫ g)`.
  have hXaff : IsAffine X := by
    obtain ⟨J, _, _, D, _, s, hs, hst⟩ := hfg
    haveI : ∀ j, IsAffine (D.obj j) := fun j => by
      have := (hst j).1.2
      rwa [ofObjectProperty_top_right_iff] at this
    exact Scheme.isAffine_of_isLimit (Cone.mk _ s) hs
  -- Affineness of Y via the data of `hg : proAffineEtale g`.
  have hYaff : IsAffine Y := by
    obtain ⟨J, _, _, D, _, s, hs, hst⟩ := hg
    haveI : ∀ j, IsAffine (D.obj j) := fun j => by
      have := (hst j).1.2
      rwa [ofObjectProperty_top_right_iff] at this
    exact Scheme.isAffine_of_isLimit (Cone.mk _ s) hs
  -- Reduce to the affine/Spec picture. Set `φ : Γ(Y) ⟶ Γ(X)` such that
  -- `Spec.map φ` represents `f` up to isoSpec.
  --
  -- It suffices to show `Y.isoSpec.inv ≫ f ≫ X.isoSpec.hom : Spec Γ(Y) ⟶ Spec Γ(X)` is
  -- pro-affine étale, since pre/post composing by the isomorphisms `Y.isoSpec.inv` and
  -- `X.isoSpec.hom` preserves (and reflects) the property of being pro-affine étale.
  -- Via `proAffineEtale_Spec_iff`, this reduces to showing the corresponding ring map is
  -- `IndEtale`.
  -- Given:
  --   * `g : Y ⟶ Z` pro-aff-étale,
  --   * `f ≫ g : X ⟶ Z` pro-aff-étale,
  -- we get (via Stacks 092Q / WeaklyEtale) that `f` is weakly-étale on stalks, hence the
  -- factorisation through `Γ(Y)` should be ind-étale. The full proof requires
  -- `HasOfPrecompProperty` for the `ind` property of `CommRingCat.etale`, which is the
  -- ring-side analog of this lemma (Stacks 097W). Mathlib does not provide this yet.
  sorry

/-- The property `Etale ⊓ ofObjectProperty (IsAffine ·) ⊤` pre-pro-spreads.
This is needed to show that `proAffineEtale` is stable under composition.

Sketch: Étale morphisms are locally of finite presentation, and the source-affine
restriction makes them quasi-compact. Mathlib's
`AlgebraicGeometry.Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` (in
`Mathlib.AlgebraicGeometry.AffineTransitionLimit`) provides the descent of an `Etale`
morphism `T ⟶ lim Dᵢ` to a finite level when `T` and each `Dᵢ` are affine. This descent
is precisely what `PreProSpreads.exists_isPullback` requires; supplying the pullback
witness and propagating the affineness/étaleness of `f'` is the remaining technical step. -/
instance : MorphismProperty.PreProSpreads.{u}
    (@Etale ⊓ .ofObjectProperty (IsAffine ·) (⊤ : ObjectProperty Scheme.{u})) := by
  -- Structural setup: destructure the property to isolate `Etale f` and `IsAffine T`.
  constructor
  intro J _ _ D c hc T f hf
  obtain ⟨hEt, hAff⟩ := hf
  haveI : IsAffine T := ofObjectProperty_top_right_iff.mp hAff
  haveI : Etale f := hEt
  -- Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` provides the
  -- spreading-out of an LFP morphism `Y → S` along a cofiltered limit of qcqs schemes with
  -- affine transition maps. Étale morphisms are LFP, so this would apply once we have:
  --   (a) each `D.obj j` is qcqs (compact + quasi-separated),
  --   (b) each transition `D.map α` is affine, and
  --   (c) `D` factors through `(Functor.const _).obj S` for some base `S`.
  -- These are not in the hypotheses of `PreProSpreads`; the statement is universal over all
  -- cofiltered diagrams in `Scheme`. To make this work for the use case (combining with
  -- `proAffineEtale`), one would need to refine the `PreProSpreads` class to take these
  -- additional assumptions, or restrict the diagrams used to construct `proAffineEtale`
  -- morphisms to have these properties (Stacks 01ZM / 00U2 deep descent).
  -- The construction would proceed:
  --   1. Take the qc-qs cover of `c.pt` by `T`'s image (since `T` is affine, this is qc).
  --   2. Use `CommRingCat.exists_fp_algebra_descent_of_isColimit` on `Γ(T) ≃ colim Γ(D.obj j)`
  --      (when `c.pt` is affine, from `Scheme.isColimit_Γ_mapCocone_op_of_isLimit`) and the
  --      LFP ring map `Γ(c.pt) → Γ(T)` to obtain a stage `j₀` with an FP-pushout square.
  --   3. Take `Spec` of the pushout square to obtain the scheme-side pullback witness
  --      `T' = Spec(Aⱼ)`, `f' : T' → D.obj j₀ = Spec(Γ(D.obj j₀))`.
  --   4. Check `f'` is étale (descended along the FP-pushout: étaleness is local on the
  --      source and stable under base change; here it descends via `RingHom.Etale.descent`-
  --      style lemmas for FP base changes — not present in Mathlib for arbitrary FP descent).
  -- Steps 2-4 are the deep ring-side descent of étale algebras (Stacks 00U2), which is
  -- the missing piece of Mathlib infrastructure.
  sorry

instance : proAffineEtale.IsStableUnderComposition := by
  rw [proAffineEtale]
  infer_instance

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    proAffineEtale.IsStableUnderBaseChangeAlong f := by
  rw [proAffineEtale]
  have : (@Etale ⊓ ofObjectProperty (IsAffine ·) ⊤ :
      MorphismProperty Scheme.{u}).IsStableUnderBaseChangeAlong f := by
    constructor
    intro Z W f' g' g h ⟨h₁, h₂⟩
    refine ⟨MorphismProperty.of_isPullback h h₁, ?_⟩
    have : IsAffine Z := h₂.left
    have : IsAffineHom f' := MorphismProperty.of_isPullback h.flip ‹_›
    rw [ofObjectProperty_top_right_iff]
    exact isAffine_of_isAffineHom f'
  infer_instance

/-- Backward direction of `proAffineEtale_Spec_iff`: an ind-étale ring map between
commutative rings gives rise to a pro-affine étale morphism via `Spec`. -/
lemma proAffineEtale_Spec_of_indEtale {R S : CommRingCat.{u}} {f : R ⟶ S}
    (h : f.hom.IndEtale) : proAffineEtale (Spec.map f) := by
  rw [RingHom.IndEtale.iff_ind_etale] at h
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := h
  -- Build the cofiltered diagram by `D.op ⋙ Scheme.Spec : Jᵒᵖ ⥤ Scheme`.
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, D.op ⋙ Scheme.Spec,
    { app j' := Spec.map (t.app j'.unop)
      naturality := fun j' k' α => by
        dsimp
        have := t.naturality α.unop
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
        rw [Category.comp_id, ← Spec.map_comp, ← this] },
    { app j' := Spec.map (s.app j'.unop)
      naturality := fun j' k' α => by
        dsimp
        have := s.naturality α.unop
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        rw [Category.id_comp, ← Spec.map_comp, this] },
    ?_, fun j' => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · -- IsLimit of the cone in Scheme via Spec applied to op of original colimit cocone.
    let c : Cocone D := Cocone.mk _ s
    have hcop : IsLimit c.op := IsColimit.op hs
    -- Spec preserves limits as a right adjoint.
    have hSpecLimit : IsLimit (Scheme.Spec.mapCone c.op) :=
      isLimitOfPreserves Scheme.Spec hcop
    -- Transport this IsLimit along the canonical iso of cones.
    refine IsLimit.ofIsoLimit hSpecLimit ?_
    refine Cone.ext (Iso.refl _) ?_
    intro j'
    dsimp [c]
    simp
  · -- Etale of Spec.map (t.app j'.unop)
    show Etale (Spec.map (t.app j'.unop))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact (hts j'.unop).1
  · -- IsAffine of Spec(D.obj j'.unop)
    show ofObjectProperty (IsAffine ·) ⊤ (Spec.map (t.app j'.unop))
    rw [ofObjectProperty_top_right_iff]
    exact AlgebraicGeometry.isAffine_Spec _
  · -- s'.app j' ≫ t'.app j' = Spec.map f
    show Spec.map (s.app j'.unop) ≫ Spec.map (t.app j'.unop) = Spec.map f
    rw [← Spec.map_comp]
    congr 1
    exact (hts j'.unop).2

/-- Forward direction of `proAffineEtale_Spec_iff`: a pro-affine étale morphism between
affine schemes lifts to an ind-étale ring map.

Sketch (mirrors `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation_of_isAffine` in
mathlib): replace `D` by `D ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec` using the unit of the
`Γ ⊣ Spec` adjunction (which is iso on affine objects). The resulting cone in `Scheme`
is in the image of `Scheme.Spec`. Reflecting limits along `Scheme.Spec` then yields a
colimit cocone in `CommRingCat`, which provides the required `ind` data on `f`. -/
lemma proAffineEtale_Spec_to_indEtale {R S : CommRingCat.{u}} {f : R ⟶ S}
    (h : proAffineEtale (Spec.map f)) : f.hom.IndEtale := by
  rw [RingHom.IndEtale.iff_ind_etale]
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := h
  -- For each `j`, `D.obj j` is affine via the `ofObjectProperty IsAffine ⊤` factor.
  haveI hAff : ∀ j, IsAffine (D.obj j) := fun j =>
    ofObjectProperty_top_right_iff.mp (hts j).1.2
  -- The target ind-diagram: `Φ j' = Γ(D.obj j'.unop)` in `CommRingCat`.
  let Φ : Jᵒᵖ ⥤ CommRingCat.{u} := D.op ⋙ Scheme.Γ
  -- Cocone leg `Φ.obj j' ⟶ S` obtained from `s.app j'.unop : Spec S ⟶ D.obj j'.unop`
  -- by post-composing with `(D.obj j'.unop).isoSpec.hom` and taking `Spec.preimage`.
  let σ : ∀ j' : Jᵒᵖ, Φ.obj j' ⟶ S := fun j' =>
    Spec.preimage (s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom)
  -- Cone leg `R ⟶ Φ.obj j'` obtained from `t.app j'.unop : D.obj j'.unop ⟶ Spec R`
  -- by pre-composing with `(D.obj j'.unop).isoSpec.inv` and taking `Spec.preimage`.
  let τ : ∀ j' : Jᵒᵖ, R ⟶ Φ.obj j' := fun j' =>
    Spec.preimage ((D.obj j'.unop).isoSpec.inv ≫ t.app j'.unop)
  have hSpec_σ : ∀ j' : Jᵒᵖ,
      Spec.map (σ j') = s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom :=
    fun j' => Spec.map_preimage _
  have hSpec_τ : ∀ j' : Jᵒᵖ,
      Spec.map (τ j') = (D.obj j'.unop).isoSpec.inv ≫ t.app j'.unop :=
    fun j' => Spec.map_preimage _
  -- Natural transformation `const R ⟶ Φ`.
  let τNat : (Functor.const Jᵒᵖ).obj R ⟶ Φ :=
    { app := τ
      naturality := fun j' k' α => by
        haveI : IsAffine (D.obj j'.unop) := hAff j'.unop
        haveI : IsAffine (D.obj k'.unop) := hAff k'.unop
        dsimp
        rw [Category.id_comp]
        apply Spec.map_injective
        rw [Spec.map_comp, hSpec_τ k', hSpec_τ j']
        have htn : t.app k'.unop = D.map α.unop ≫ t.app j'.unop := by
          have := t.naturality α.unop
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
          exact this.symm
        have hΦmap : Φ.map α = (D.map α.unop).appTop := Scheme.Γ_map_op (D.map α.unop)
        rw [htn, hΦmap]
        exact (Scheme.isoSpec_inv_naturality_assoc (D.map α.unop) (t.app j'.unop)).symm }
  -- Cocone `Φ ⟶ const S`.
  let σNat : Φ ⟶ (Functor.const Jᵒᵖ).obj S :=
    { app := σ
      naturality := fun j' k' α => by
        haveI : IsAffine (D.obj j'.unop) := hAff j'.unop
        haveI : IsAffine (D.obj k'.unop) := hAff k'.unop
        dsimp
        rw [Category.comp_id]
        apply Spec.map_injective
        rw [Spec.map_comp, hSpec_σ k', hSpec_σ j']
        have hsn : s.app j'.unop = s.app k'.unop ≫ D.map α.unop := by
          have := s.naturality α.unop
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
          exact this
        have hΦmap : Φ.map α = (D.map α.unop).appTop := Scheme.Γ_map_op (D.map α.unop)
        rw [hsn, hΦmap]
        have hnat := Scheme.isoSpec_hom_naturality (D.map α.unop)
        -- hnat : iso_k.hom ≫ Spec.map ((D.map α.unop).appTop) = D.map α.unop ≫ iso_j.hom
        calc (s.app k'.unop ≫ (D.obj k'.unop).isoSpec.hom) ≫
              Spec.map ((D.map α.unop).appTop)
            = s.app k'.unop ≫ (D.obj k'.unop).isoSpec.hom ≫
              Spec.map ((D.map α.unop).appTop) := Category.assoc _ _ _
          _ = s.app k'.unop ≫ D.map α.unop ≫ (D.obj j'.unop).isoSpec.hom := by rw [hnat]
          _ = (s.app k'.unop ≫ D.map α.unop) ≫ (D.obj j'.unop).isoSpec.hom :=
              (Category.assoc _ _ _).symm }
  -- Versions stating `Spec.map` of the `.app` field of the natural transformations.
  -- These are definitionally equal to `hSpec_σ`/`hSpec_τ` but use the `let`-bound
  -- `σNat.app` / `τNat.app` form that appears in the goals after `refine`.
  have hSpec_σNat : ∀ j' : Jᵒᵖ,
      Spec.map (σNat.app j') = s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom := hSpec_σ
  have hSpec_τNat : ∀ j' : Jᵒᵖ,
      Spec.map (τNat.app j') = (D.obj j'.unop).isoSpec.inv ≫ t.app j'.unop := hSpec_τ
  -- For each cocone `c' : Cocone Φ`, build the corresponding cone leg in `Scheme`
  -- with apex `Spec c'.pt` landing in `D.obj i`.
  let legSpec : (c' : Cocone Φ) → (i : J) → (Spec c'.pt ⟶ D.obj i) :=
    fun c' i => Spec.map (c'.ι.app (Opposite.op i)) ≫ (D.obj i).isoSpec.inv
  -- Build, for each cocone `c' : Cocone Φ`, an associated cone over `D` in `Scheme`
  -- with apex `Spec c'.pt`.
  let mkScheme : Cocone Φ → Cone D := fun c' =>
    { pt := Spec c'.pt
      π :=
        { app := legSpec c'
          naturality := fun i i' α => by
            haveI : IsAffine (D.obj i) := hAff i
            haveI : IsAffine (D.obj i') := hAff i'
            dsimp only [legSpec, Functor.const_obj_obj, Functor.const_obj_map]
            rw [Category.id_comp]
            have hcnat : Φ.map α.op ≫ c'.ι.app (Opposite.op i) =
                c'.ι.app (Opposite.op i') := by
              have := c'.ι.naturality α.op
              simp only [Functor.const_obj_obj, Functor.const_obj_map,
                Category.comp_id] at this
              exact this
            have hΦmap : Φ.map α.op = (D.map α).appTop :=
              Scheme.Γ_map_op (D.map α)
            rw [hΦmap] at hcnat
            have hinv : (D.obj i).isoSpec.inv ≫ D.map α =
                Spec.map ((D.map α).appTop) ≫ (D.obj i').isoSpec.inv :=
              (Scheme.isoSpec_inv_naturality (D.map α)).symm
            have step1 : Spec.map (c'.ι.app (Opposite.op i')) =
                Spec.map (c'.ι.app (Opposite.op i)) ≫
                  Spec.map ((D.map α).appTop) := by
              rw [← Spec.map_comp]
              exact congrArg Spec.map hcnat.symm
            calc Spec.map (c'.ι.app (Opposite.op i')) ≫ (D.obj i').isoSpec.inv
                = (Spec.map (c'.ι.app (Opposite.op i)) ≫
                    Spec.map ((D.map α).appTop)) ≫
                    (D.obj i').isoSpec.inv :=
                  congrArg (· ≫ (D.obj i').isoSpec.inv) step1
              _ = Spec.map (c'.ι.app (Opposite.op i)) ≫
                    (Spec.map ((D.map α).appTop) ≫
                      (D.obj i').isoSpec.inv) := Category.assoc _ _ _
              _ = Spec.map (c'.ι.app (Opposite.op i)) ≫
                    ((D.obj i).isoSpec.inv ≫ D.map α) :=
                  congrArg (Spec.map (c'.ι.app (Opposite.op i)) ≫ ·) hinv.symm
              _ = (Spec.map (c'.ι.app (Opposite.op i)) ≫
                    (D.obj i).isoSpec.inv) ≫ D.map α :=
                (Category.assoc _ _ _).symm } }
  have mkScheme_π_app (c' : Cocone Φ) (i : J) :
      (mkScheme c').π.app i =
        Spec.map (c'.ι.app (Opposite.op i)) ≫ (D.obj i).isoSpec.inv := rfl
  refine ⟨Jᵒᵖ, inferInstance, inferInstance, Φ, τNat, σNat, ?_, fun j' => ⟨?_, ?_⟩⟩
  · -- `IsColimit (Cocone.mk S σNat)`: build the descent map by reflecting through `Spec`.
    refine
      { desc := fun c' => Spec.preimage (hs.lift (mkScheme c'))
        fac := fun c' j' => ?_
        uniq := fun c' m hm => ?_ }
    · dsimp only
      apply Spec.map_injective
      haveI : IsAffine (D.obj j'.unop) := hAff j'.unop
      have hliftFac : hs.lift (mkScheme c') ≫ s.app j'.unop =
          Spec.map (c'.ι.app (Opposite.op j'.unop)) ≫
            (D.obj j'.unop).isoSpec.inv := by
        have := hs.fac (mkScheme c') j'.unop
        rwa [mkScheme_π_app] at this
      have hPre : Spec.map (Spec.preimage (hs.lift (mkScheme c'))) =
          hs.lift (mkScheme c') :=
        Spec.map_preimage (hs.lift (mkScheme c'))
      have step1 : Spec.map (σNat.app j' ≫
            Spec.preimage (hs.lift (mkScheme c'))) =
          hs.lift (mkScheme c') ≫ Spec.map (σNat.app j') := by
        rw [Spec.map_comp]
        exact congrArg (· ≫ Spec.map (σNat.app j')) hPre
      -- Substitute Spec.map (σNat.app j') via hSpec_σNat using congrArg.
      have step2a : hs.lift (mkScheme c') ≫ Spec.map (σNat.app j') =
          hs.lift (mkScheme c') ≫
            (s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom) :=
        congrArg (hs.lift (mkScheme c') ≫ ·) (hSpec_σNat j')
      have step2b : hs.lift (mkScheme c') ≫
            (s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom) =
          (hs.lift (mkScheme c') ≫ s.app j'.unop) ≫
            (D.obj j'.unop).isoSpec.hom :=
        (Category.assoc _ _ _).symm
      have step2c : (hs.lift (mkScheme c') ≫ s.app j'.unop) ≫
            (D.obj j'.unop).isoSpec.hom =
          (Spec.map (c'.ι.app (Opposite.op j'.unop)) ≫
            (D.obj j'.unop).isoSpec.inv) ≫
            (D.obj j'.unop).isoSpec.hom :=
        congrArg (· ≫ (D.obj j'.unop).isoSpec.hom) hliftFac
      have hIsoCancel : (D.obj j'.unop).isoSpec.inv ≫
            (D.obj j'.unop).isoSpec.hom = 𝟙 _ :=
        Iso.inv_hom_id _
      have step2d : (Spec.map (c'.ι.app (Opposite.op j'.unop)) ≫
            (D.obj j'.unop).isoSpec.inv) ≫
            (D.obj j'.unop).isoSpec.hom =
          Spec.map (c'.ι.app (Opposite.op j'.unop)) :=
        (Category.assoc _ _ _).trans
          ((congrArg (Spec.map (c'.ι.app (Opposite.op j'.unop)) ≫ ·)
              hIsoCancel).trans (Category.comp_id _))
      exact step1.trans (step2a.trans (step2b.trans (step2c.trans step2d)))
    · dsimp only
      apply Spec.map_injective
      -- Goal: Spec.map m = Spec.map (Spec.preimage (hs.lift (mkScheme c')))
      refine (hs.uniq (mkScheme c') (Spec.map m) ?_).trans
        (Spec.map_preimage (hs.lift (mkScheme c'))).symm
      intro i
      haveI : IsAffine (D.obj i) := hAff i
      rw [mkScheme_π_app]
      have hmi : σNat.app (Opposite.op i) ≫ m = c'.ι.app (Opposite.op i) :=
        hm (Opposite.op i)
      -- Build the chain using Eq.trans / congrArg to avoid fragile rw matching.
      have hHom : (D.obj i).isoSpec.hom ≫ (D.obj i).isoSpec.inv = 𝟙 _ :=
        Iso.hom_inv_id _
      have hσSpec : Spec.map (σNat.app (Opposite.op i)) =
          s.app i ≫ (D.obj i).isoSpec.hom := hSpec_σNat (Opposite.op i)
      have hSpecComp : Spec.map (σNat.app (Opposite.op i) ≫ m) =
          Spec.map m ≫ Spec.map (σNat.app (Opposite.op i)) :=
        Spec.map_comp _ _
      have hSubst : Spec.map (σNat.app (Opposite.op i) ≫ m) =
          Spec.map (c'.ι.app (Opposite.op i)) := congrArg Spec.map hmi
      -- Final chain.
      have eq1 : Spec.map m ≫ s.app i =
          (Spec.map m ≫ s.app i) ≫ 𝟙 _ := (Category.comp_id _).symm
      have eq2 : (Spec.map m ≫ s.app i) ≫ 𝟙 _ =
          (Spec.map m ≫ s.app i) ≫
            ((D.obj i).isoSpec.hom ≫ (D.obj i).isoSpec.inv) :=
        congrArg ((Spec.map m ≫ s.app i) ≫ ·) hHom.symm
      have eq3 : (Spec.map m ≫ s.app i) ≫
            ((D.obj i).isoSpec.hom ≫ (D.obj i).isoSpec.inv) =
          ((Spec.map m ≫ s.app i) ≫ (D.obj i).isoSpec.hom) ≫
            (D.obj i).isoSpec.inv := (Category.assoc _ _ _).symm
      have eq4 : ((Spec.map m ≫ s.app i) ≫ (D.obj i).isoSpec.hom) ≫
            (D.obj i).isoSpec.inv =
          (Spec.map m ≫ (s.app i ≫ (D.obj i).isoSpec.hom)) ≫
            (D.obj i).isoSpec.inv :=
        congrArg (· ≫ (D.obj i).isoSpec.inv) (Category.assoc _ _ _)
      have eq5 : (Spec.map m ≫ (s.app i ≫ (D.obj i).isoSpec.hom)) ≫
            (D.obj i).isoSpec.inv =
          (Spec.map m ≫ Spec.map (σNat.app (Opposite.op i))) ≫
            (D.obj i).isoSpec.inv :=
        congrArg (fun x => (Spec.map m ≫ x) ≫ (D.obj i).isoSpec.inv)
          hσSpec.symm
      have eq6 : (Spec.map m ≫ Spec.map (σNat.app (Opposite.op i))) ≫
            (D.obj i).isoSpec.inv =
          Spec.map (σNat.app (Opposite.op i) ≫ m) ≫
            (D.obj i).isoSpec.inv :=
        congrArg (· ≫ (D.obj i).isoSpec.inv) hSpecComp.symm
      have eq7 : Spec.map (σNat.app (Opposite.op i) ≫ m) ≫
            (D.obj i).isoSpec.inv =
          Spec.map (c'.ι.app (Opposite.op i)) ≫ (D.obj i).isoSpec.inv :=
        congrArg (· ≫ (D.obj i).isoSpec.inv) hSubst
      exact eq1.trans (eq2.trans (eq3.trans (eq4.trans
        (eq5.trans (eq6.trans eq7)))))
  · -- `(τNat.app j').hom.Etale`: pre-composing the étale `t.app j'.unop` by the iso
    -- `(D.obj j'.unop).isoSpec.inv` preserves étaleness.
    rw [CommRingCat.etale_iff, ← HasRingHomProperty.Spec_iff (P := @Etale), hSpec_τNat]
    have h1 : @Etale _ _ (D.obj j'.unop).isoSpec.inv := inferInstance
    have h2 : @Etale _ _ (t.app j'.unop) := (hts j'.unop).1.1
    exact MorphismProperty.comp_mem _ _ _ h1 h2
  · -- `τNat.app j' ≫ σNat.app j' = f`: after taking `Spec.map`, the isoSpec pair cancels
    -- and what remains is the data `s.app j'.unop ≫ t.app j'.unop = Spec.map f` from `pro`.
    apply Spec.map_injective
    rw [Spec.map_comp, hSpec_σNat, hSpec_τNat]
    calc (s.app j'.unop ≫ (D.obj j'.unop).isoSpec.hom) ≫
          ((D.obj j'.unop).isoSpec.inv ≫ t.app j'.unop)
        = s.app j'.unop ≫ ((D.obj j'.unop).isoSpec.hom ≫
            (D.obj j'.unop).isoSpec.inv) ≫ t.app j'.unop := by
              simp only [Category.assoc]
      _ = s.app j'.unop ≫ 𝟙 _ ≫ t.app j'.unop := by rw [Iso.hom_inv_id]
      _ = s.app j'.unop ≫ t.app j'.unop := by rw [Category.id_comp]
      _ = Spec.map f := (hts j'.unop).2

lemma proAffineEtale_Spec_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    proAffineEtale (Spec.map f) ↔ f.hom.IndEtale :=
  ⟨proAffineEtale_Spec_to_indEtale, proAffineEtale_Spec_of_indEtale⟩

/-- The source of a `proAffineEtale` morphism is affine, being a cofiltered limit
of affine schemes. -/
lemma proAffineEtale_isAffine_source {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : proAffineEtale f) : IsAffine X := by
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := hf
  haveI : ∀ j, IsAffine (D.obj j) := fun j => by
    have := (hst j).1.2
    rwa [ofObjectProperty_top_right_iff] at this
  exact Scheme.isAffine_of_isLimit (Cone.mk _ s) hs

/-- Helper: a pro-affine étale morphism between affine schemes is weakly-étale. -/
lemma proAffineEtale_le_weaklyEtale_of_affine
    {R S : CommRingCat.{u}} {f : R ⟶ S} (hf : proAffineEtale (Spec.map f)) :
    WeaklyEtale (Spec.map f) :=
  (WeaklyEtale.Spec_iff f).mpr (proAffineEtale_Spec_to_indEtale hf).weaklyEtale

/-- Every pro-affine étale morphism is weakly-étale.

Proof: a pro-affine-étale morphism `f` is in `pro P` for
`P = @Etale ⊓ .ofObjectProperty (IsAffine ·) ⊤`. Each morphism in `P` is in particular
étale, hence weakly étale. Applying `WeaklyEtale.of_pro` (the cofiltered-limit-of-weakly-étale
fact, Stacks 092Q-adjacent) finishes the proof. -/
lemma proAffineEtale_le_weaklyEtale : proAffineEtale ≤ @WeaklyEtale := by
  intro X Y f hf
  refine WeaklyEtale.of_pro ?_ hf
  rintro A B g ⟨hEt, _⟩
  exact letI := hEt; inferInstance

/-! ### Helpers for spreading out pro-affine-étale data

The following helpers package the cofiltered presentation underlying a `proAffineEtale`
morphism as data living in `S.AffineEtale` and provide a Spec-level spreading lemma
that allows us to descend morphisms into the limit to a finite stage. They are
designed to be consumed by `Proetale.Topology.Comparison.Affine`.
-/

/-- Promote a cofiltered diagram of affine schemes étale over `S` to a (covariant)
functor into the small affine étale site `S.AffineEtale`.

Given the data of a cofiltered presentation `(J, D, t)` with each `D.obj j` affine and
each `t.app j : D.obj j ⟶ S` étale, this produces the corresponding functor
`liftAffineEtale D t hAff hEt : J ⥤ S.AffineEtale`, sending each `j : J` to the
affine étale object `(D.obj j).isoSpec.inv ≫ t.app j : Spec Γ(D.obj j) ⟶ S`. -/
noncomputable def liftAffineEtale
    {S : Scheme.{u}} {J : Type u} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (t : D ⟶ (Functor.const J).obj S)
    (hAff : ∀ j, IsAffine (D.obj j)) (hEt : ∀ j, Etale (t.app j)) :
    J ⥤ Scheme.AffineEtale S where
  obj j :=
    haveI : IsAffine (D.obj j) := hAff j
    haveI hE : Etale (t.app j) := hEt j
    MorphismProperty.CostructuredArrow.mk (P := @Etale) ⊤
      ((D.obj j).isoSpec.inv ≫ t.app j)
      (MorphismProperty.comp_mem _ _ _ inferInstance hE)
  map {j k} α :=
    haveI : IsAffine (D.obj j) := hAff j
    haveI : IsAffine (D.obj k) := hAff k
    MorphismProperty.CostructuredArrow.homMk (((D.map α).appTop).op) trivial <| by
      change Scheme.Spec.map (((D.map α).appTop).op) ≫
        ((D.obj k).isoSpec.inv ≫ t.app k) = (D.obj j).isoSpec.inv ≫ t.app j
      have h1 : Scheme.Spec.map (((D.map α).appTop).op) =
          Spec.map ((D.map α).appTop) := rfl
      rw [h1]
      have hnat : Spec.map ((D.map α).appTop) ≫ (D.obj k).isoSpec.inv =
          (D.obj j).isoSpec.inv ≫ D.map α :=
        Scheme.isoSpec_inv_naturality (D.map α)
      have htnat := t.naturality α
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at htnat
      calc Spec.map ((D.map α).appTop) ≫ (D.obj k).isoSpec.inv ≫ t.app k
          = (Spec.map ((D.map α).appTop) ≫ (D.obj k).isoSpec.inv) ≫ t.app k :=
            (Category.assoc _ _ _).symm
        _ = ((D.obj j).isoSpec.inv ≫ D.map α) ≫ t.app k := by rw [hnat]
        _ = (D.obj j).isoSpec.inv ≫ (D.map α ≫ t.app k) := Category.assoc _ _ _
        _ = (D.obj j).isoSpec.inv ≫ t.app j :=
            congrArg ((D.obj j).isoSpec.inv ≫ ·) htnat
  map_id j := by
    haveI : IsAffine (D.obj j) := hAff j
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show ((D.map (𝟙 j)).appTop).op = 𝟙 _
    simp
  map_comp {j k l} α β := by
    haveI : IsAffine (D.obj j) := hAff j
    haveI : IsAffine (D.obj k) := hAff k
    haveI : IsAffine (D.obj l) := hAff l
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show ((D.map (α ≫ β)).appTop).op = ((D.map α).appTop).op ≫ ((D.map β).appTop).op
    simp

/-- Scheme-level finite-stage factoring for affine-target maps into a cofiltered limit.

If `D : J ⥤ Scheme` is a cofiltered diagram of affines with affine étale transition
maps over `S`, with limit `c.pt`, and `Y` is an affine scheme finitely presented over
`S`, then any `S`-morphism `c.pt ⟶ Y` factors through one of the finite stages `D.obj j`.

This is the affine specialization of
`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`. -/
lemma Scheme.exists_factor_through_finite_stage_of_isAffine
    {S : Scheme.{u}} {J : Type u} [SmallCategory J] [IsCofiltered J]
    {D : J ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
    (t : D ⟶ (Functor.const J).obj S)
    [hT : ∀ {i j} (α : i ⟶ j), IsAffineHom (D.map α)]
    [hCpt : ∀ i, CompactSpace (D.obj i)]
    [hQS : ∀ i, QuasiSeparatedSpace (D.obj i)]
    {Y : Scheme.{u}} (f : Y ⟶ S) [hLFP : LocallyOfFinitePresentation f]
    (a : c.pt ⟶ Y) (ha : c.π ≫ t = (Functor.const _).map (a ≫ f)) :
    ∃ (j : J) (g : D.obj j ⟶ Y), c.π.app j ≫ g = a ∧ g ≫ f = t.app j :=
  Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t f c hc a ha

/-! ### Spec-level into-limit descent helpers (round-16 OBJ B, partial)

Given a cofiltered diagram `D : J ⥤ Scheme` of affines étale over a base `S`, with affine
limit `c.pt`, the full into-limit descent (EGA IV.8 / Stacks 01ZM / 00U2) states that any
étale arrow `Y → c.pt` with `Y` affine factors as a pullback of an étale arrow
`Y₀ → D.obj j₀` for some finite stage `j₀`. This requires the descent of étale algebras
along filtered colimits of rings (Stacks 00U2), which is not in Mathlib and is the deeper
piece of remaining infrastructure.

The helper below provides the constructive packaging of the colimit identification at the
ring level (`Γ(c.pt) ≃ colim_J Γ(D.obj j)`), which is the cornerstone of the descent and
the obvious starting point for future work on this objective. -/

/-- Constructive (`noncomputable`) version of `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`:
for a cofiltered diagram `D : J ⥤ Scheme` of qcqs schemes with affine transition maps and a
limit cone `c`, the global-sections functor `Scheme.Γ` turns `c.op` into a colimit cocone in
`CommRingCat`. In particular `Γ(c.pt) ≅ colim_J Γ(D.obj j)` as a filtered colimit.

This is the building block for descending data on `Γ(c.pt)` to a finite stage via Mathlib's
filtered-colimit-of-rings machinery (e.g.
`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`,
`IsFinitelyPresentable.exists_hom_of_isColimit`). -/
noncomputable def Scheme.isColimit_Γ_mapCocone_op_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J] {D : J ⥤ Scheme.{u}}
    (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] :
    IsColimit (Scheme.Γ.mapCocone c.op) :=
  (AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone D c hc).some

end AlgebraicGeometry
