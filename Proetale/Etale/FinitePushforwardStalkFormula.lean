/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.FinitePushforwardCofinality
import Proetale.Etale.FinitePushforwardStalkProduct

/-!
# The stalk formula for pushforwards along finite morphisms

This file completes stage D of the program towards the sheaf-level half of the proper
base change dévissage for finite morphisms (blueprint `lemma:pbc-finite`), assembling
the results of `Proetale.Etale.FinitePushforwardStalkProduct` and
`Proetale.Etale.FinitePushforwardCofinality` into **the stalk formula**: for a finite
morphism `f : Y ⟶ X`, a geometric point `x : Spec Ω ⟶ X` and an abelian sheaf `F` on
the small étale site of `Y`, the stalk of `f_* F` at `x` is the finite product of the
stalks of `F` at the geometric points of `Y` over `x`, i.e.
`(f_* F)_x̄ ≅ ∏_{ȳ ↦ x̄} F_ȳ`. This closes the goal stated in the module docstring of
`Proetale.Etale.FinitePushforwardStalk`.

## Main results

- `AlgebraicGeometry.Scheme.Etale.colimitSummandSheafDiagramIsoSheafFiber`: the colimit
  of the sections of `F` over the split summand system of a distinguished index is the
  stalk of `F` at the lifted geometric point, by the cofinality of the summand system
  (`AlgebraicGeometry.Scheme.Etale.initial_summandFunctor`), with the leg
  characterization
  `AlgebraicGeometry.Scheme.Etale.ι_colimitSummandSheafDiagramIsoSheafFiber_hom`.
- `AlgebraicGeometry.Scheme.Etale.pushforwardStalkToStalk_eq`: the comparison map from
  the stalk of the pushforward to the stalk at a lift factors as the product
  decomposition of `Proetale.Etale.FinitePushforwardStalkProduct` followed by the
  projection to the distinguished factor and the cofinality isomorphism.
- `AlgebraicGeometry.Scheme.Etale.isIso_pushforwardStalkToPiStalk_of_data`: **the stalk
  formula with explicit splitting data**: given a splitting stage `p₁` carrying the
  complete orthogonal family of idempotents indexed by the maximal ideals of the fiber
  sections, and for each maximal ideal a compatible character with its associated lift,
  the comparison map `AlgebraicGeometry.Scheme.Etale.pushforwardStalkToPiStalk` is an
  isomorphism for every abelian sheaf `F`.
- `AlgebraicGeometry.Scheme.Etale.exists_forall_isIso_pushforwardStalkToPiStalk`: **the
  stalk formula** (blueprint `lemma:pbc-finite`, sheaf-level half): for a finite
  morphism `f` there is a family of lifts of `x` to `Y`, indexed by the maximal ideals
  of the fiber sections and with values in the algebraic closure of `Ω`, such that the
  comparison map to the product of stalks is an isomorphism for every abelian sheaf.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme.Etale

attribute [local instance] finite_maximalSpectrum_fiberSections

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X) (p₁ : (geometricPoint x).fiber.Elements)

section SummandColimit

variable {ι : Type u} (es : ι → Γ(((Over.pullback @Etale ⊤ f).obj p₁.1).left, ⊤)) (i : ι)
  {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
  (σ : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))
  (y : Spec (CommRingCat.of Ω') ⟶ Y) (hy : y ≫ f = σ ≫ x)
  (χ : fiberSections f x →+* Ω')
  (heval : fiberSectionsToStrictLocalization f x σ y hy ≫ strictLocalizationEval y =
    CommRingCat.ofHom χ)
  (hi : χ ((toFiberSections f x p₁).hom (es i)) ≠ 0)
  (F : Sheaf Y.smallEtaleTopology Ab.{u + 1})

/-- The summand sheaf diagram of the distinguished index is the restriction of the
stalk colimit diagram of `F` at the lifted geometric point along the summand system,
definitionally. -/
lemma summandFunctor_op_comp_eq :
    (summandFunctor f x p₁ es i σ y hy χ heval hi).op ⋙
        ((CategoryOfElements.π (geometricPoint y).fiber).op ⋙ F.obj) =
      summandSheafDiagram f x p₁ es F i :=
  rfl

variable [IsFinite f] [Fintype ι]

/-- **The summand sections colimit is the stalk at the lifted point**: the colimit of
the sections of `F` over the split summand system of the distinguished index compares
isomorphically to the stalk of `F` at the lifted geometric point `y`, by the
cofinality of the summand system among the étale neighbourhoods of `y`
(`AlgebraicGeometry.Scheme.Etale.initial_summandFunctor`). -/
noncomputable def colimitSummandSheafDiagramIsoSheafFiber
    (m : MaximalSpectrum (fiberSections f x)) (hker : RingHom.ker χ = m.asIdeal)
    (hnot : (toFiberSections f x p₁).hom (es i) ∉ m.asIdeal)
    (hmem : ∀ m' : MaximalSpectrum (fiberSections f x), m' ≠ m →
      (toFiberSections f x p₁).hom (es i) ∈ m'.asIdeal)
    (hes : CompleteOrthogonalIdempotents es) :
    colimit (summandSheafDiagram f x p₁ es F i) ≅ (geometricPoint y).sheafFiber.obj F :=
  haveI : (summandFunctor f x p₁ es i σ y hy χ heval hi).Initial :=
    initial_summandFunctor f x p₁ es i σ y hy χ heval hi m hker hnot hmem hes
  asIso (colimit.pre ((CategoryOfElements.π (geometricPoint y).fiber).op ⋙ F.obj)
    (summandFunctor f x p₁ es i σ y hy χ heval hi).op)

/-- The leg characterization of the cofinality isomorphism: on the summand at a stage
`g`, it is the canonical germ map of the étale neighbourhood given by the summand with
its lifted geometric point. -/
lemma ι_colimitSummandSheafDiagramIsoSheafFiber_hom
    (m : MaximalSpectrum (fiberSections f x)) (hker : RingHom.ker χ = m.asIdeal)
    (hnot : (toFiberSections f x p₁).hom (es i) ∉ m.asIdeal)
    (hmem : ∀ m' : MaximalSpectrum (fiberSections f x), m' ≠ m →
      (toFiberSections f x p₁).hom (es i) ∈ m'.asIdeal)
    (hes : CompleteOrthogonalIdempotents es) (g : SummandIndex x p₁) :
    colimit.ι (summandSheafDiagram f x p₁ es F i) (op g) ≫
        (colimitSummandSheafDiagramIsoSheafFiber f x p₁ es i σ y hy χ heval hi F m hker
          hnot hmem hes).hom =
      (geometricPoint y).toPresheafFiber (summand f x p₁ es i g)
        (summandPoint f x p₁ es i σ y hy χ heval hi g) F.obj :=
  colimit.ι_pre ((CategoryOfElements.π (geometricPoint y).fiber).op ⋙ F.obj)
    (summandFunctor f x p₁ es i σ y hy χ heval hi).op (op g)

/-- **The comparison map to the stalk at a lift factors through the distinguished
summand factor**: the map from the stalk of the pushforward to the stalk of `F` at the
lifted geometric point is the product decomposition of
`Proetale.Etale.FinitePushforwardStalkProduct` followed by the projection to the
distinguished factor and the cofinality isomorphism. -/
theorem pushforwardStalkToStalk_eq
    (m : MaximalSpectrum (fiberSections f x)) (hker : RingHom.ker χ = m.asIdeal)
    (hnot : (toFiberSections f x p₁).hom (es i) ∉ m.asIdeal)
    (hmem : ∀ m' : MaximalSpectrum (fiberSections f x), m' ≠ m →
      (toFiberSections f x p₁).hom (es i) ∈ m'.asIdeal)
    (hes : CompleteOrthogonalIdempotents es) :
    pushforwardStalkToStalk f x σ y hy F =
      (pushforwardStalkIsoColimitPiSummand f x p₁ es F hes).hom ≫
        Pi.π (fun j => colimit (summandSheafDiagram f x p₁ es F j)) i ≫
        (colimitSummandSheafDiagramIsoSheafFiber f x p₁ es i σ y hy χ heval hi F m hker
          hnot hmem hes).hom := by
  rw [← cancel_epi (pushforwardStalkIsoColimitPullbackStage f x p₁ F).inv]
  refine colimit.hom_ext fun G => ?_
  obtain ⟨g⟩ := G
  have hleg : colimit.ι (pullbackStageSheafDiagram f x p₁ F) (op g) ≫
      (pushforwardStalkIsoColimitPullbackStage f x p₁ F).inv =
      toPushforwardStalk f x F (stage x p₁ g).1 (stage x p₁ g).2 := by
    rw [Iso.comp_inv_eq]
    exact (toPushforwardStalk_pushforwardStalkIsoColimitPullbackStage_hom f x p₁ F g).symm
  simp only [reassoc_of% hleg]
  have h1 : toPushforwardStalk f x F (stage x p₁ g).1 (stage x p₁ g).2 ≫
      pushforwardStalkToStalk f x σ y hy F =
      (geometricPoint y).toPresheafFiber
        ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
        (pullbackFiberLift f x σ y hy (stage x p₁ g).1 (stage x p₁ g).2) F.obj :=
    toPushforwardStalk_pushforwardStalkToStalk f x σ y hy F _ _
  have h2 := congrArg
    (· ≫ (colimitSummandSheafDiagramIsoSheafFiber f x p₁ es i σ y hy χ heval hi F m
      hker hnot hmem hes).hom)
    (toPushforwardStalk_pushforwardStalkIsoColimitPiSummand_hom_π f x p₁ es F hes g i)
  simp only [Category.assoc] at h2
  have h4 : F.obj.map ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj
        (stage x p₁ g).1) (esAt f x p₁ es g)).inj i).op ≫
      colimit.ι (summandSheafDiagram f x p₁ es F i) (op g) ≫
      (colimitSummandSheafDiagramIsoSheafFiber f x p₁ es i σ y hy χ heval hi F m hker
        hnot hmem hes).hom =
      F.obj.map ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj
        (stage x p₁ g).1) (esAt f x p₁ es g)).inj i).op ≫
      (geometricPoint y).toPresheafFiber (summand f x p₁ es i g)
        (summandPoint f x p₁ es i σ y hy χ heval hi g) F.obj := by
    rw [ι_colimitSummandSheafDiagramIsoSheafFiber_hom f x p₁ es i σ y hy χ heval hi F m
      hker hnot hmem hes g]
  have h5 : F.obj.map ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj
        (stage x p₁ g).1) (esAt f x p₁ es g)).inj i).op ≫
      (geometricPoint y).toPresheafFiber (summand f x p₁ es i g)
        (summandPoint f x p₁ es i σ y hy χ heval hi g) F.obj =
      (geometricPoint y).toPresheafFiber
        ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
        ((geometricPoint y).fiber.map
          ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
            (esAt f x p₁ es g)).inj i)
          (summandPoint f x p₁ es i σ y hy χ heval hi g)) F.obj :=
    (geometricPoint y).toPresheafFiber_w
      ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
        (esAt f x p₁ es g)).inj i)
      (summandPoint f x p₁ es i σ y hy χ heval hi g) F.obj
  have h6 : (geometricPoint y).toPresheafFiber
      ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
      ((geometricPoint y).fiber.map ((cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj
          (stage x p₁ g).1) (esAt f x p₁ es g)).inj i)
        (summandPoint f x p₁ es i σ y hy χ heval hi g)) F.obj =
      (geometricPoint y).toPresheafFiber
        ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1)
        (pullbackFiberLift f x σ y hy (stage x p₁ g).1 (stage x p₁ g).2) F.obj :=
    congrArg (fun t => (geometricPoint y).toPresheafFiber
      ((Over.pullback @Etale ⊤ f).obj (stage x p₁ g).1) t F.obj)
      (summandPoint_inj f x p₁ es i σ y hy χ heval hi g)
  exact h1.trans (((h2.trans h4).trans (h5.trans h6)).symm)

end SummandColimit

section StalkFormula

variable {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
  (σ : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))

/-- **The stalk formula with explicit splitting data**: let `f : Y ⟶ X` be a finite
morphism, `x : Spec Ω ⟶ X` a geometric point, `p₁` a splitting stage carrying a
complete orthogonal family of idempotents `es` indexed by the maximal ideals of the
fiber sections (as produced by
`AlgebraicGeometry.Scheme.Etale.exists_elements_isColimit_cofanOfIdempotents`), and for
each maximal ideal `m` a character `χ m` with kernel `m` and an associated lift `y m`
of `x` satisfying the evaluation compatibility. Then the comparison map from the stalk
of `f_* F` at `x` to the product of the stalks of `F` at the lifts is an isomorphism
for every abelian sheaf `F`. -/
theorem isIso_pushforwardStalkToPiStalk_of_data [IsFinite f]
    [Fintype (MaximalSpectrum (fiberSections f x))]
    (es : MaximalSpectrum (fiberSections f x) →
      Γ(((Over.pullback @Etale ⊤ f).obj p₁.1).left, ⊤))
    (hes : CompleteOrthogonalIdempotents es)
    (hnot : ∀ m, (toFiberSections f x p₁).hom (es m) ∉ m.asIdeal)
    (hmem : ∀ m m' : MaximalSpectrum (fiberSections f x), m' ≠ m →
      (toFiberSections f x p₁).hom (es m) ∈ m'.asIdeal)
    (y : MaximalSpectrum (fiberSections f x) → (Spec (CommRingCat.of Ω') ⟶ Y))
    (hy : ∀ m, y m ≫ f = σ ≫ x)
    (χ : (m : MaximalSpectrum (fiberSections f x)) → (fiberSections f x →+* Ω'))
    (hker : ∀ m, RingHom.ker (χ m) = m.asIdeal)
    (heval : ∀ m, fiberSectionsToStrictLocalization f x σ (y m) (hy m) ≫
      strictLocalizationEval (y m) = CommRingCat.ofHom (χ m))
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    IsIso (pushforwardStalkToPiStalk f x σ y hy F) := by
  have hi : ∀ m, (χ m) ((toFiberSections f x p₁).hom (es m)) ≠ 0 := by
    intro m h0
    have hm : (toFiberSections f x p₁).hom (es m) ∈ RingHom.ker (χ m) :=
      RingHom.mem_ker.mpr h0
    rw [hker m] at hm
    exact hnot m hm
  have key : pushforwardStalkToPiStalk f x σ y hy F =
      (pushforwardStalkIsoColimitPiSummand f x p₁ es F hes).hom ≫
        Limits.Pi.map fun m => (colimitSummandSheafDiagramIsoSheafFiber f x p₁ es m σ
          (y m) (hy m) (χ m) (heval m) (hi m) F m (hker m) (hnot m) (hmem m) hes).hom := by
    refine Pi.hom_ext _ _ fun m => ?_
    rw [pushforwardStalkToPiStalk_π, Category.assoc]
    simp only [Limits.Pi.map_π]
    exact pushforwardStalkToStalk_eq f x p₁ es m σ (y m) (hy m) (χ m) (heval m) (hi m)
      F m (hker m) (hnot m) (hmem m) hes
  rw [key]
  infer_instance

end StalkFormula

/-- **The stalk formula for pushforwards along finite morphisms** (the sheaf-level
half of blueprint `lemma:pbc-finite`): for a finite morphism `f : Y ⟶ X` and a
geometric point `x : Spec Ω ⟶ X`, there is a family of lifts of `x` to `Y`, indexed by
the (finitely many) maximal ideals of the fiber sections over the strict localization
and with values in the algebraic closure of `Ω`, such that for every abelian sheaf `F`
on the small étale site of `Y` the comparison map
`AlgebraicGeometry.Scheme.Etale.pushforwardStalkToPiStalk` is an isomorphism:
`(f_* F)_x̄ ≅ ∏_{ȳ ↦ x̄} F_ȳ`. -/
theorem exists_forall_isIso_pushforwardStalkToPiStalk [IsFinite f] :
    ∃ (y : MaximalSpectrum (fiberSections f x) →
        (Spec (CommRingCat.of (AlgebraicClosure Ω)) ⟶ Y))
      (hy : ∀ m, y m ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))) ≫ x),
      ∀ F : Sheaf Y.smallEtaleTopology Ab.{u + 1},
        IsIso (pushforwardStalkToPiStalk f x
          (Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))) y hy F) := by
  classical
  haveI : Fintype (MaximalSpectrum (fiberSections f x)) := Fintype.ofFinite _
  obtain ⟨p₁, es, hes, hnot, hmem, -⟩ := exists_elements_isColimit_cofanOfIdempotents f x
  obtain ⟨p₀, hp₀⟩ := exists_elements_isAffine x
  choose χ hy hker heval using
    fun m => exists_ringHom_fiberSectionsToStrictLocalization_eval f x p₀ hp₀ m
  exact ⟨fun m => liftOfRingHom f x p₀ hp₀ (χ m), hy, fun F =>
    isIso_pushforwardStalkToPiStalk_of_data f x p₁
      (Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))) es hes hnot
      hmem (fun m => liftOfRingHom f x p₀ hp₀ (χ m)) hy χ hker heval F⟩

end AlgebraicGeometry.Scheme.Etale
