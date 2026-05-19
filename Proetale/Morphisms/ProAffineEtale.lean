/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Ind
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads
import Proetale.Morphisms.WeaklyEtale
import Proetale.Algebra.IndEtale
import Proetale.Algebra.IndWeaklyEtale
import Proetale.Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty

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
  -- Outline:
  --   constructor
  --   intro J _ _ D c hc T f ⟨hEt, hAff⟩
  --   -- T is affine via `hAff` (the `ofObjectProperty IsAffine ⊤` factor).
  --   -- Each `D.obj j` need not be affine, but the limit `c.pt` is some scheme.
  --   -- Apply `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` to descend
  --   -- `f : T ⟶ c.pt` (locally of FP since etale) to a finite level `j` with
  --   -- `f' : T' ⟶ D.obj j`. Verify that `f'` is etale (`HasRingHomProperty.descent` /
  --   -- direct construction) and that `T'` can be chosen affine.
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

end AlgebraicGeometry
