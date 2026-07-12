/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.FinitePushforwardStalk
import Proetale.Etale.StrictLocalization

/-!
# Splitting the fiber of a finite morphism over the strict localization

This file carries out the first two stages of the remaining program for the sheaf-level
half of the proper base change dévissage for finite morphisms (blueprint
`lemma:pbc-finite`), continuing `Proetale.Etale.FinitePushforwardStalk`.

Let `f : Y ⟶ X` be a morphism of schemes and `x : Spec Ω ⟶ X` a geometric point.

## The fiber sections over the strict localization

- `AlgebraicGeometry.Scheme.Etale.fiberSectionsDiagram` /
  `AlgebraicGeometry.Scheme.Etale.fiberSections`: the filtered colimit
  `S = colim_{(U, u)} Γ(U ×_X Y)` of the section rings of the fibers over the étale
  neighbourhoods of `x`; this is the ring of sections of the base change of `f` to the
  strict localization of `X` at `x`.
- `AlgebraicGeometry.Scheme.Etale.strictLocalizationToFiberSections`: the canonical
  algebra structure of the fiber sections over the strict localization, induced by the
  first projections `U ×_X Y ⟶ U`.

## Stage A: module-finiteness (for finite `f`)

- `AlgebraicGeometry.Scheme.Etale.module_finite_fiberSections`: for finite `f`, the
  fiber sections are a finite module over the strict localization. Over an affine étale
  neighbourhood `U₀` the sections `Γ(U₀ ×_X Y)` are a finite `Γ(U₀)`-module
  (`AlgebraicGeometry.Scheme.Hom.finite_appTop` after base change), the transition
  squares of the diagram are pushouts of rings
  (`AlgebraicGeometry.isPushout_appTop_of_isPullback` applied to the pasting of pullback
  squares), so generators at one affine stage span every finer affine stage
  (`Algebra.IsPushout.span_range_algebraMap_eq_top`) and hence the colimit.

## Stage B: splitting the fiber and descending the idempotents (for finite `f`)

- `AlgebraicGeometry.Scheme.Etale.finite_maximalSpectrum_fiberSections` and
  `AlgebraicGeometry.Scheme.Etale.bijective_pi_localization_fiberSections`: the fiber
  sections split into finitely many local factors, indexed by the maximal ideals
  (Stacks 04GG (10), via
  `AlgebraicGeometry.Scheme.Etale.finite_maximalSpectrum_and_bijective_pi_localization_of_finite`).
- `AlgebraicGeometry.Scheme.Etale.exists_completeOrthogonalIdempotents_fiberSections`:
  the splitting is realized by a complete orthogonal family of idempotents indexed by
  the maximal spectrum.
- `AlgebraicGeometry.Scheme.Etale.exists_elements_completeOrthogonalIdempotents`: the
  idempotent family descends to a single étale neighbourhood stage
  (`CommRingCat.exists_orthogonal_idempotents_of_isColimit`).
- `AlgebraicGeometry.Scheme.Etale.basicOpenSummand` /
  `AlgebraicGeometry.Scheme.Etale.cofanOfIdempotents` /
  `AlgebraicGeometry.Scheme.Etale.isColimitCofanOfIdempotents`: a complete orthogonal
  family of idempotent sections on an object `V` of the small étale site decomposes `V`
  as the finite disjoint union of the corresponding basic open subschemes.
- `AlgebraicGeometry.Scheme.Etale.sheafObjProdIsoOfCompleteOrthogonalIdempotents`: the
  induced product decomposition of the sections of an abelian sheaf.
- `AlgebraicGeometry.Scheme.Etale.exists_elements_isColimit_cofanOfIdempotents`: the
  combination — for finite `f` there is an étale neighbourhood `(U, u)` of `x` such that
  `U ×_X Y` decomposes in the small étale site of `Y` as a finite disjoint union indexed
  by the maximal ideals of the fiber sections, via idempotents mapping to the canonical
  splitting family.

## Remaining stages towards `lemma:pbc-finite`

Stage C (not yet formalized) identifies the localization of the fiber sections at the
maximal ideal `m` with the strict localization of `Y` at a geometric point `y_m` over
`x` (with values in an algebraically closed extension `Ω'` of `Ω`; the extension is
necessary — see the `Spec k^(1/p) ⟶ Spec k` example in the module docstring of
`Proetale.Etale.FinitePushforwardStalk`), and deduces that the split summands over the
shrinking neighbourhoods are cofinal among the étale neighbourhoods of `y_m`. Stage D
assembles `AlgebraicGeometry.Scheme.Etale.pushforwardStalkToPiStalk` being an
isomorphism from additivity and the commutation of filtered colimits with finite
products.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

section SpanTransfer

/-- Generators of `R'` as an `R`-module map to generators of the pushout
`S' = S ⊗[R] R'` as an `S`-module. -/
theorem Algebra.IsPushout.span_range_algebraMap_eq_top
    (R S R' S' : Type*) [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra S S'] [Algebra R S']
    [IsScalarTower R R' S'] [IsScalarTower R S S'] [h : Algebra.IsPushout R S R' S']
    {ι : Type*} {t : ι → R'} (ht : Submodule.span R (Set.range t) = ⊤) :
    Submodule.span S (Set.range fun i => algebraMap R' S' (t i)) = ⊤ := by
  have key : ∀ m ∈ Submodule.span R (Set.range t),
      algebraMap R' S' m ∈ Submodule.span S (Set.range fun i => algebraMap R' S' (t i)) := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R S S', ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hy
  rw [Submodule.eq_top_iff']
  intro z
  refine h.out.inductionOn z _ (Submodule.zero_mem _)
    (fun m => key m (ht.symm ▸ Submodule.mem_top))
    (fun s n hn => Submodule.smul_mem _ _ hn)
    (fun n₁ n₂ h₁ h₂ => Submodule.add_mem _ h₁ h₂)

/-- The image under a ring homomorphism of an element of a module span lies in the span
of the image, provided the scalars are transported along a compatible homomorphism. -/
private lemma mem_span_image_of_ringHom_comm {R₁ R₂ B₁ B₂ : Type*} [CommRing R₁]
    [CommRing R₂] [CommRing B₁] [CommRing B₂] [Algebra R₁ B₁] [Algebra R₂ B₂]
    (φ : R₁ →+* R₂) (π : B₁ →+* B₂)
    (hcomm : ∀ r, π (algebraMap R₁ B₁ r) = algebraMap R₂ B₂ (φ r))
    {M : Set B₁} {b : B₁} (hb : b ∈ Submodule.span R₁ M) :
    π b ∈ Submodule.span R₂ (π '' M) := by
  induction hb using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [Algebra.smul_def, map_mul, hcomm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hy

end SpanTransfer

namespace AlgebraicGeometry.Scheme.Etale

/-!
### Disjoint union decompositions from idempotents

A complete orthogonal family of idempotent global sections of an object `V` of the small
étale site decomposes `V` as the finite disjoint union of the corresponding basic open
subschemes, which are étale over the base since they are open in `V`.
-/

section CofanOfIdempotents

variable {S : Scheme.{u}} (V : S.Etale) {ι : Type u} (ε : ι → Γ(V.left, ⊤))

/-- The basic open subscheme of an idempotent section of `V`, as an object of the small
étale site: it is open in `V`, hence étale over the base. -/
noncomputable def basicOpenSummand (i : ι) : S.Etale :=
  MorphismProperty.Over.mk _ ((V.left.basicOpen (ε i)).ι ≫ V.hom)
    (by haveI : Etale V.hom := V.prop; infer_instance)

/-- The cofan on the basic open subschemes of a family of sections of `V`, given by the
open immersions. For a complete orthogonal family of idempotents it is a colimit cofan,
see `AlgebraicGeometry.Scheme.Etale.isColimitCofanOfIdempotents`. -/
noncomputable def cofanOfIdempotents : Cofan (basicOpenSummand V ε) :=
  Cofan.mk V fun i => MorphismProperty.Over.homMk (V.left.basicOpen (ε i)).ι rfl trivial

variable [Fintype ι]

/-- **A complete orthogonal family of idempotent sections decomposes an étale scheme as
a finite disjoint union**: the basic open subschemes of the idempotents are pairwise
disjoint and covering, so they exhibit `V` as their coproduct in the small étale
site. -/
noncomputable def isColimitCofanOfIdempotents (hε : CompleteOrthogonalIdempotents ε) :
    IsColimit (cofanOfIdempotents V ε) := by
  -- the basic opens cover `V` because the idempotents generate the unit ideal
  have hcov : ⨆ i, ((V.left.basicOpen (ε i)).ι).opensRange = ⊤ := by
    have hspan : Ideal.span (Set.range ε) = ⊤ := by
      rw [Ideal.eq_top_iff_one, ← hε.complete]
      exact Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨i, rfl⟩
    have h1 : (⨆ b ∈ Set.range ε, V.left.basicOpen b) = ⊤ :=
      iSup_basicOpen_of_span_eq_top (X := V.left) ⊤ (Set.range ε) hspan
    rw [iSup_range] at h1
    simpa only [Scheme.Opens.opensRange_ι] using h1
  -- the basic opens are pairwise disjoint because the idempotents are orthogonal
  have hdisj : Pairwise (Function.onFun Disjoint
      fun i => ((V.left.basicOpen (ε i)).ι).opensRange) := by
    intro i j hij
    simp only [Function.onFun, Scheme.Opens.opensRange_ι]
    rw [disjoint_iff, ← Scheme.basicOpen_mul, hε.ortho hij, Scheme.basicOpen_zero]
  have hsc := (nonempty_isColimit_cofanMk_of
    (fun i => (V.left.basicOpen (ε i)).ι) hcov hdisj).some
  exact isColimitOfIsColimitCofanMkObj (Etale.forget S ⋙ CategoryTheory.Over.forget S)
    (basicOpenSummand V ε)
    (fun i => MorphismProperty.Over.homMk (V.left.basicOpen (ε i)).ι rfl trivial) hsc

/-- The sections of an abelian sheaf on the small étale site over an object carrying a
complete orthogonal family of idempotents decompose as the finite product of the
sections over the basic open summands. -/
noncomputable def sheafObjProdIsoOfCompleteOrthogonalIdempotents
    (F : Sheaf S.smallEtaleTopology Ab.{u + 1}) (hε : CompleteOrthogonalIdempotents ε) :
    F.obj.obj (op V) ≅ ∏ᶜ fun i => F.obj.obj (op (basicOpenSummand V ε i)) :=
  sheafObjProdIsoOfIsColimit F (isColimitCofanOfIdempotents V ε hε)

end CofanOfIdempotents

/-!
### The fiber sections over the strict localization
-/

section FiberSections

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X)

/-- The diagram of the section rings `Γ(U ×_X Y)` of the fibers of `f` over the étale
neighbourhoods `(U, u)` of the geometric point `x`. Its filtered colimit is the ring of
sections of the base change of `f` to the strict localization of `X` at `x`. -/
noncomputable def fiberSectionsDiagram :
    ((geometricPoint x).fiber.Elements)ᵒᵖ ⥤ CommRingCat.{u} :=
  (CategoryOfElements.π (geometricPoint x).fiber ⋙ Over.pullback @Etale ⊤ f ⋙
    Etale.forget Y ⋙ CategoryTheory.Over.forget Y).op ⋙ Scheme.Γ

/-- The ring of sections of the fiber of `f` over the strict localization of `X` at
`x`, as the filtered colimit of the section rings `Γ(U ×_X Y)` over the étale
neighbourhoods `(U, u)` of `x`. -/
noncomputable def fiberSections : CommRingCat.{u} :=
  colimit (fiberSectionsDiagram f x)

/-- The canonical map from the sections of the fiber over an étale neighbourhood stage
to the fiber sections over the strict localization. -/
noncomputable def toFiberSections (p : (geometricPoint x).fiber.Elements) :
    (fiberSectionsDiagram f x).obj (op p) ⟶ fiberSections f x :=
  colimit.ι (fiberSectionsDiagram f x) (op p)

@[reassoc, elementwise]
lemma toFiberSections_w {p q : (geometricPoint x).fiber.Elements} (g : p ⟶ q) :
    (fiberSectionsDiagram f x).map (op g) ≫ toFiberSections f x p =
      toFiberSections f x q :=
  colimit.w (fiberSectionsDiagram f x) (op g)

/-- Every element of the fiber sections comes from some étale neighbourhood stage. -/
lemma exists_toFiberSections_eq (z : fiberSections f x) :
    ∃ (p : (geometricPoint x).fiber.Elements)
      (a : (fiberSectionsDiagram f x).obj (op p)),
      (toFiberSections f x p).hom a = z := by
  obtain ⟨⟨p⟩, a, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget CommRingCat)
      (colimit.isColimit (fiberSectionsDiagram f x))) z
  exact ⟨p, a, rfl⟩

/-- The first projections `U ×_X Y ⟶ U` induce a morphism of diagrams from the
neighbourhood sections to the fiber sections. -/
noncomputable def strictLocalizationDiagramToFiberSections :
    strictLocalizationDiagram x ⟶ fiberSectionsDiagram f x where
  app p := Scheme.Γ.map (pullback.fst p.unop.1.hom f).op
  naturality p q g := by
    change Scheme.Γ.map (g.unop.val.left).op ≫
        Scheme.Γ.map (pullback.fst q.unop.1.hom f).op =
      Scheme.Γ.map (pullback.fst p.unop.1.hom f).op ≫
        Scheme.Γ.map (((Over.pullback @Etale ⊤ f).map g.unop.val).left).op
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      pullback_map_left_fst]

/-- The canonical map from the strict localization to the fiber sections, induced by
the first projections `U ×_X Y ⟶ U`. This is the algebra structure of the fiber over
the strict localization. -/
noncomputable def strictLocalizationToFiberSections :
    strictLocalization x ⟶ fiberSections f x :=
  colimMap (strictLocalizationDiagramToFiberSections f x)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toStrictLocalization_strictLocalizationToFiberSections
    (p : (geometricPoint x).fiber.Elements) :
    toStrictLocalization x p ≫ strictLocalizationToFiberSections f x =
      Scheme.Γ.map (pullback.fst p.1.hom f).op ≫ toFiberSections f x p :=
  ι_colimMap _ _

noncomputable instance : Algebra (strictLocalization x) (fiberSections f x) :=
  (strictLocalizationToFiberSections f x).hom.toAlgebra

lemma algebraMap_fiberSections_eq :
    algebraMap (strictLocalization x) (fiberSections f x) =
      (strictLocalizationToFiberSections f x).hom :=
  rfl

/-!
### Stage A: module-finiteness of the fiber sections for finite morphisms
-/

/-- The transition square of the fiber diagram over a morphism of étale neighbourhoods
is a pullback of schemes. -/
private lemma isPullback_transition {p q : (geometricPoint x).fiber.Elements}
    (g : p ⟶ q) :
    IsPullback (((Over.pullback @Etale ⊤ f).map g.val).left) (pullback.fst p.1.hom f)
      (pullback.fst q.1.hom f) g.val.left := by
  refine IsPullback.of_right ?_ (pullback_map_left_fst f g.val)
    (IsPullback.of_hasPullback q.1.hom f).flip
  rw [pullback_map_left_snd, MorphismProperty.Over.w g.val]
  exact (IsPullback.of_hasPullback p.1.hom f).flip

/-- For a finite morphism `f` and a transition between affine étale neighbourhood
stages, the induced square of section rings is a pushout: the fiber sections at the
finer stage are the base change of the fiber sections at the coarser stage. -/
private lemma isPushout_transition [IsFinite f] {p q : (geometricPoint x).fiber.Elements}
    (g : p ⟶ q) [IsAffine p.1.left] [IsAffine q.1.left] :
    IsPushout ((pullback.fst q.1.hom f).appTop) (g.val.left.appTop)
      ((((Over.pullback @Etale ⊤ f).map g.val).left).appTop)
      ((pullback.fst p.1.hom f).appTop) := by
  haveI : IsAffine ((𝟭 Scheme.{u}).obj p.1.left) := ‹IsAffine p.1.left›
  haveI : IsAffine ((𝟭 Scheme.{u}).obj q.1.left) := ‹IsAffine q.1.left›
  haveI : IsAffine (pullback q.1.hom f) := inferInstance
  exact isPushout_appTop_of_isPullback (isPullback_transition f x g)

/-- **Module-finiteness of the fiber sections over the strict localization**: for a
finite morphism `f : Y ⟶ X`, the ring of sections of the fiber of `f` over the strict
localization of `X` at a geometric point is a finite module over the strict
localization. Generators are given by the images of module generators of
`Γ(U₀ ×_X Y)` over `Γ(U₀)` at any affine étale neighbourhood stage `U₀`. -/
instance module_finite_fiberSections [IsFinite f] :
    Module.Finite (strictLocalization x) (fiberSections f x) := by
  classical
  -- choose a base affine étale neighbourhood stage `p₀`
  obtain ⟨j₀⟩ : Nonempty (AffineEtale.Spec X ⋙ (geometricPoint x).fiber).Elements :=
    IsCofiltered.nonempty
  set A := CategoryOfElements.pre (AffineEtale.Spec X) (geometricPoint x).fiber with hA
  set p₀ : (geometricPoint x).fiber.Elements := A.obj j₀ with hp₀
  haveI h₀ : IsAffine p₀.1.left := inferInstanceAs (IsAffine (Spec (unop j₀.1.left)))
  haveI h₀' : IsAffine ((𝟭 Scheme.{u}).obj p₀.1.left) := h₀
  haveI hT₀ : IsAffine (pullback p₀.1.hom f) := inferInstance
  -- `Γ(U₀ ×_X Y)` is a finite module over `Γ(U₀)`; choose generators
  letI : Algebra (Scheme.Γ.obj (op p₀.1.left)) ((fiberSectionsDiagram f x).obj (op p₀)) :=
    ((pullback.fst p₀.1.hom f).appTop).hom.toAlgebra
  haveI hMF : Module.Finite (Scheme.Γ.obj (op p₀.1.left))
      ((fiberSectionsDiagram f x).obj (op p₀)) :=
    Scheme.Hom.finite_appTop (pullback.fst p₀.1.hom f)
  obtain ⟨n, t, ht⟩ := Module.Finite.exists_fin (R := Scheme.Γ.obj (op p₀.1.left))
    (M := (fiberSectionsDiagram f x).obj (op p₀))
  -- the images of the generators in the fiber sections
  set s : Fin n → fiberSections f x := fun i => (toFiberSections f x p₀).hom (t i) with hs
  refine ⟨⟨Finset.univ.image s, ?_⟩⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, eq_top_iff]
  rintro z -
  -- represent `z` at an affine stage refining both its stage and `p₀`
  obtain ⟨p, a, rfl⟩ := exists_toFiberSections_eq f x z
  obtain ⟨w⟩ : Nonempty (CostructuredArrow A p) := by
    haveI := Functor.Initial.out (F := A) p
    infer_instance
  set j₂ := IsCofiltered.min w.left j₀ with hj₂
  set p₂ : (geometricPoint x).fiber.Elements := A.obj j₂ with hp₂
  haveI h₂ : IsAffine p₂.1.left := inferInstanceAs (IsAffine (Spec (unop j₂.1.left)))
  haveI h₂' : IsAffine ((𝟭 Scheme.{u}).obj p₂.1.left) := h₂
  set e₁ : p₂ ⟶ p := A.map (IsCofiltered.minToLeft w.left j₀) ≫ w.hom with he₁
  set e₀ : p₂ ⟶ p₀ := A.map (IsCofiltered.minToRight w.left j₀) with he₀
  set a₂ : ((fiberSectionsDiagram f x).obj (op p₂) : Type u) :=
    ((fiberSectionsDiagram f x).map (op e₁)).hom a with ha₂
  have hza : (toFiberSections f x p₂).hom a₂ = (toFiberSections f x p).hom a :=
    toFiberSections_w_apply f x e₁ a
  -- the transition square over `e₀` is a pushout of rings
  have hpo := isPushout_transition f x e₀
  letI : Algebra (Scheme.Γ.obj (op p₀.1.left)) (Scheme.Γ.obj (op p₂.1.left)) :=
    (e₀.val.left.appTop).hom.toAlgebra
  letI : Algebra ((fiberSectionsDiagram f x).obj (op p₀))
      ((fiberSectionsDiagram f x).obj (op p₂)) :=
    ((((Over.pullback @Etale ⊤ f).map e₀.val).left).appTop).hom.toAlgebra
  letI : Algebra (Scheme.Γ.obj (op p₂.1.left)) ((fiberSectionsDiagram f x).obj (op p₂)) :=
    ((pullback.fst p₂.1.hom f).appTop).hom.toAlgebra
  letI : Algebra (Scheme.Γ.obj (op p₀.1.left)) ((fiberSectionsDiagram f x).obj (op p₂)) :=
    (((pullback.fst p₀.1.hom f).appTop ≫
      (((Over.pullback @Etale ⊤ f).map e₀.val).left).appTop)).hom.toAlgebra
  haveI : IsScalarTower (Scheme.Γ.obj (op p₀.1.left))
      ((fiberSectionsDiagram f x).obj (op p₀)) ((fiberSectionsDiagram f x).obj (op p₂)) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : IsScalarTower (Scheme.Γ.obj (op p₀.1.left)) (Scheme.Γ.obj (op p₂.1.left))
      ((fiberSectionsDiagram f x).obj (op p₂)) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      congrArg (fun φ => CommRingCat.Hom.hom φ r) hpo.w
  haveI hAP : Algebra.IsPushout (Scheme.Γ.obj (op p₀.1.left))
      (Scheme.Γ.obj (op p₂.1.left)) ((fiberSectionsDiagram f x).obj (op p₀))
      ((fiberSectionsDiagram f x).obj (op p₂)) :=
    CommRingCat.isPushout_iff_isPushout.mp (by exact hpo.flip)
  -- the generators span the sections at the common stage
  have hspan₂ : Submodule.span (Scheme.Γ.obj (op p₂.1.left))
      (Set.range fun i =>
        algebraMap ((fiberSectionsDiagram f x).obj (op p₀))
          ((fiberSectionsDiagram f x).obj (op p₂)) (t i)) = ⊤ :=
    Algebra.IsPushout.span_range_algebraMap_eq_top _ _ _ _ ht
  -- push the span into the colimit
  have hcomm : ∀ r : Scheme.Γ.obj (op p₂.1.left),
      (toFiberSections f x p₂).hom
        (algebraMap (Scheme.Γ.obj (op p₂.1.left))
          ((fiberSectionsDiagram f x).obj (op p₂)) r) =
      algebraMap (strictLocalization x) (fiberSections f x)
        ((toStrictLocalization x p₂).hom r) := fun r =>
    (toStrictLocalization_strictLocalizationToFiberSections_apply f x p₂ r).symm
  have h2 := mem_span_image_of_ringHom_comm ((toStrictLocalization x p₂).hom)
    ((toFiberSections f x p₂).hom) hcomm (hspan₂.symm ▸ Submodule.mem_top (x := a₂))
  rw [← hza]
  refine Submodule.span_mono ?_ h2
  rintro - ⟨-, ⟨i, rfl⟩, rfl⟩
  exact ⟨i, (toFiberSections_w_apply f x e₀ (t i)).symm⟩

/-!
### Stage B: splitting the fiber and descending the idempotents
-/

/-- For a finite morphism, the fiber sections over the strict localization have only
finitely many maximal ideals. -/
theorem finite_maximalSpectrum_fiberSections [IsFinite f] :
    Finite (MaximalSpectrum (fiberSections f x)) :=
  (finite_maximalSpectrum_and_bijective_pi_localization_of_finite x (fiberSections f x)).1

/-- **The fiber of a finite morphism over the strict localization splits into local
factors**: the canonical map to the product of the localizations at the (finitely many)
maximal ideals is bijective. -/
theorem bijective_pi_localization_fiberSections [IsFinite f] :
    Function.Bijective (Pi.ringHom
      (fun m : MaximalSpectrum (fiberSections f x) =>
        algebraMap (fiberSections f x) (Localization.AtPrime m.asIdeal))) :=
  (finite_maximalSpectrum_and_bijective_pi_localization_of_finite x (fiberSections f x)).2

/-- **The splitting idempotents of the fiber sections**: for a finite morphism, the
splitting of the fiber sections into local factors is realized by a complete orthogonal
family of idempotents indexed by the maximal spectrum, where the idempotent at `m`
avoids `m` and lies in every other maximal ideal. -/
theorem exists_completeOrthogonalIdempotents_fiberSections [IsFinite f]
    [Fintype (MaximalSpectrum (fiberSections f x))] :
    ∃ e : MaximalSpectrum (fiberSections f x) → fiberSections f x,
      CompleteOrthogonalIdempotents e ∧ (∀ m, e m ∉ m.asIdeal) ∧
      ∀ m m' : MaximalSpectrum (fiberSections f x), m' ≠ m → e m ∈ m'.asIdeal := by
  choose ε hidem hnot hmem using fun m : MaximalSpectrum (fiberSections f x) =>
    IsLocalRing.exists_isIdempotentElem_notMem_forall_mem_of_forall_retraction
      (fun B _ _ hB hq => exists_retraction_of_etale_of_exists_prime x B hB hq)
      (fiberSections f x) m.asIdeal
  obtain ⟨e, hco, hnot', hmem'⟩ :=
    MaximalSpectrum.exists_completeOrthogonalIdempotents ε hidem hnot
      fun m m' h => hmem m m'.asIdeal m'.isMaximal fun hh => h (MaximalSpectrum.ext hh)
  exact ⟨e, hco, hnot', hmem'⟩

/-- **Descent of the fiber splitting to an étale neighbourhood stage**: for a finite
morphism `f`, the complete orthogonal family of splitting idempotents of the fiber
sections descends to a complete orthogonal family of idempotents of `Γ(U ×_X Y)` for
some étale neighbourhood `(U, u)` of `x`. -/
theorem exists_elements_completeOrthogonalIdempotents [IsFinite f]
    [Fintype (MaximalSpectrum (fiberSections f x))] :
    ∃ e : MaximalSpectrum (fiberSections f x) → fiberSections f x,
      CompleteOrthogonalIdempotents e ∧ (∀ m, e m ∉ m.asIdeal) ∧
      (∀ m m' : MaximalSpectrum (fiberSections f x), m' ≠ m → e m ∈ m'.asIdeal) ∧
      ∃ (p : (geometricPoint x).fiber.Elements)
        (ε : MaximalSpectrum (fiberSections f x) →
          (fiberSectionsDiagram f x).obj (op p)),
        CompleteOrthogonalIdempotents ε ∧
        ∀ m, (toFiberSections f x p).hom (ε m) = e m := by
  obtain ⟨e, hco, hnot, hmem⟩ := exists_completeOrthogonalIdempotents_fiberSections f x
  obtain ⟨j, ε, hidem, horth, hsum, himg⟩ :=
    CommRingCat.exists_orthogonal_idempotents_of_isColimit
      (isColimitOfPreserves (CategoryTheory.forget CommRingCat)
        (colimit.isColimit (fiberSectionsDiagram f x)))
      e hco.idem hco.ortho hco.complete
  exact ⟨e, hco, hnot, hmem, j.unop, ε, ⟨⟨hidem, horth⟩, hsum⟩, fun m => himg m⟩

/-- **Splitting the fiber of a finite morphism at an étale neighbourhood stage**: for a
finite morphism `f : Y ⟶ X` and a geometric point `x` of `X`, there is an étale
neighbourhood `(U, u)` of `x` and a complete orthogonal family of idempotents of
`Γ(U ×_X Y)` indexed by the maximal ideals of the fiber sections over the strict
localization, whose images in the fiber sections are the canonical splitting
idempotents, and which decompose `U ×_X Y` as a finite disjoint union in the small
étale site of `Y`. -/
theorem exists_elements_isColimit_cofanOfIdempotents [IsFinite f]
    [Fintype (MaximalSpectrum (fiberSections f x))] :
    ∃ (p : (geometricPoint x).fiber.Elements)
      (ε : MaximalSpectrum (fiberSections f x) →
        Γ(((Over.pullback @Etale ⊤ f).obj p.1).left, ⊤))
      (_ : CompleteOrthogonalIdempotents ε),
      (∀ m, (toFiberSections f x p).hom (ε m) ∉ m.asIdeal) ∧
      (∀ m m' : MaximalSpectrum (fiberSections f x), m' ≠ m →
        (toFiberSections f x p).hom (ε m) ∈ m'.asIdeal) ∧
      Nonempty (IsColimit (cofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj p.1) ε)) := by
  obtain ⟨e, hco, hnot, hmem, p, ε, hε, himg⟩ :=
    exists_elements_completeOrthogonalIdempotents f x
  refine ⟨p, ε, hε, fun m => ?_, fun m m' h => ?_,
    ⟨isColimitCofanOfIdempotents ((Over.pullback @Etale ⊤ f).obj p.1) ε hε⟩⟩
  · rw [himg m]
    exact hnot m
  · rw [himg m]
    exact hmem m m' h

/-!
### Towards stage C: geometric points of `Y` over `x` from the fiber splitting

Every maximal ideal of the fiber sections gives a character with values in the
algebraic closure of `Ω` compatible with evaluation at the geometric point, and every
such character gives a geometric point of `Y` lying over `x` via the extension
`Spec Ω' ⟶ Spec Ω`. These are the lifts appearing in the comparison map
`AlgebraicGeometry.Scheme.Etale.pushforwardStalkToPiStalk`.
-/

section Lifts

/-- The top-level sections of the inverse of `isoSpec` are the inverse of `ΓSpecIso`. -/
private lemma isoSpec_inv_appTop' (Z : Scheme.{u}) [IsAffine Z] :
    Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
  rw [← Iso.comp_hom_eq_id (Scheme.ΓSpecIso Γ(Z, ⊤)), ← Scheme.toSpecΓ_appTop,
    ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop]

/-- There is an étale neighbourhood stage of `x` with affine underlying scheme. -/
lemma exists_elements_isAffine :
    ∃ p : (geometricPoint x).fiber.Elements, IsAffine p.1.left := by
  obtain ⟨j₀⟩ : Nonempty (AffineEtale.Spec X ⋙ (geometricPoint x).fiber).Elements :=
    IsCofiltered.nonempty
  exact ⟨(CategoryOfElements.pre (AffineEtale.Spec X) (geometricPoint x).fiber).obj j₀,
    inferInstanceAs (IsAffine (Spec (unop j₀.1.left)))⟩

/-- **Characters of the fiber sections at the maximal ideals**: for a finite morphism
`f`, every maximal ideal `m` of the fiber sections over the strict localization is the
kernel of a character with values in the algebraic closure of `Ω` extending the
evaluation of the strict localization at the geometric point. The algebraic closure is
necessary in general: the residue extension at `m` may be inseparable. -/
theorem exists_ringHom_ker_eq [IsFinite f] (m : MaximalSpectrum (fiberSections f x)) :
    ∃ χ : fiberSections f x →+* AlgebraicClosure Ω,
      RingHom.ker χ = m.asIdeal ∧
      χ.comp (strictLocalizationToFiberSections f x).hom =
        (algebraMap Ω (AlgebraicClosure Ω)).comp (strictLocalizationEval x).hom := by
  classical
  -- `m` lies over the maximal ideal of the strict localization
  have hover : m.asIdeal.comap
      (algebraMap (strictLocalization x) (fiberSections f x)) =
      IsLocalRing.maximalIdeal (strictLocalization x) :=
    IsLocalRing.comap_algebraMap_eq_maximalIdeal (fiberSections f x) m.asIdeal
  -- the residue fields
  letI K : Type u :=
    strictLocalization x ⧸ IsLocalRing.maximalIdeal (strictLocalization x)
  letI L : Type u := fiberSections f x ⧸ m.asIdeal
  letI : Field K := Ideal.Quotient.field _
  letI : Field L := Ideal.Quotient.field _
  letI : Algebra K L := Ideal.Quotient.algebraQuotientOfLEComap hover.ge
  haveI : IsScalarTower (strictLocalization x) K L :=
    IsScalarTower.of_algebraMap_eq fun a => (Ideal.quotientMap_mk).symm
  -- the residue extension is finite, hence algebraic
  haveI : Module.Finite (strictLocalization x) L :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ (strictLocalization x) m.asIdeal).toLinearMap
      (Ideal.Quotient.mkₐ_surjective (strictLocalization x) m.asIdeal)
  haveI : Module.Finite K L :=
    Module.Finite.of_restrictScalars_finite (strictLocalization x) K L
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  -- evaluation embeds the residue field of the strict localization into `Ω`
  letI evalK : K →+* Ω := Ideal.Quotient.lift _ (strictLocalizationEval x).hom
    fun a ha => (mem_maximalIdeal_strictLocalization_iff x a).mp ha
  letI : Algebra K (AlgebraicClosure Ω) :=
    ((algebraMap Ω (AlgebraicClosure Ω)).comp evalK).toAlgebra
  haveI : Module.IsTorsionFree K L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K L).injective
  haveI : Module.IsTorsionFree K (AlgebraicClosure Ω) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap K (AlgebraicClosure Ω)).injective
  -- embed the residue field at `m` into the algebraic closure over `K`
  letI e : L →ₐ[K] AlgebraicClosure Ω := IsAlgClosed.lift
  refine ⟨e.toRingHom.comp (Ideal.Quotient.mk m.asIdeal), ?_, ?_⟩
  · ext z
    simp only [RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    constructor
    · intro hz
      have h0 : Ideal.Quotient.mk m.asIdeal z = 0 :=
        e.toRingHom.injective (by simpa using hz)
      rwa [Ideal.Quotient.eq_zero_iff_mem] at h0
    · intro hz
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
  · ext a
    have h1 : Ideal.Quotient.mk m.asIdeal
        ((strictLocalizationToFiberSections f x).hom a) =
        algebraMap K L (Ideal.Quotient.mk _ a) := (Ideal.quotientMap_mk).symm
    calc (e.toRingHom.comp (Ideal.Quotient.mk m.asIdeal))
          ((strictLocalizationToFiberSections f x).hom a)
        = e (Ideal.Quotient.mk m.asIdeal
            ((strictLocalizationToFiberSections f x).hom a)) := rfl
      _ = e (algebraMap K L (Ideal.Quotient.mk _ a)) := by rw [h1]
      _ = algebraMap K (AlgebraicClosure Ω) (Ideal.Quotient.mk _ a) := e.commutes _
      _ = algebraMap Ω (AlgebraicClosure Ω) (evalK (Ideal.Quotient.mk _ a)) := rfl
      _ = algebraMap Ω (AlgebraicClosure Ω) ((strictLocalizationEval x).hom a) := by
            rw [Ideal.Quotient.lift_mk]

variable [IsFinite f]

/-- **The geometric point of `Y` associated to a character of the fiber sections**: a
character of the fiber sections with values in a field extension `Ω'` of `Ω` defines a
morphism `Spec Ω' ⟶ Y`, by evaluating the sections of the fiber over any affine étale
neighbourhood stage. -/
noncomputable def liftOfRingHom (p : (geometricPoint x).fiber.Elements)
    (hp : IsAffine p.1.left) {Ω' : Type u} [Field Ω'] (χ : fiberSections f x →+* Ω') :
    Spec (CommRingCat.of Ω') ⟶ Y :=
  haveI := hp
  haveI : IsAffine (pullback p.1.hom f) :=
    haveI : IsAffine ((𝟭 Scheme.{u}).obj p.1.left) := hp
    inferInstance
  Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)) ≫
    (pullback p.1.hom f).isoSpec.inv ≫ pullback.snd p.1.hom f

/-- **The geometric point associated to a character lies over `x`**: if the character
extends the evaluation of the strict localization along `ψ : Ω →+* Ω'`, then the
associated morphism `Spec Ω' ⟶ Y` lifts `x` along the extension `Spec Ω' ⟶ Spec Ω`. -/
theorem liftOfRingHom_comp (p : (geometricPoint x).fiber.Elements)
    (hp : IsAffine p.1.left) {Ω' : Type u} [Field Ω'] {ψ : Ω →+* Ω'}
    (χ : fiberSections f x →+* Ω')
    (hχ : χ.comp (strictLocalizationToFiberSections f x).hom =
      ψ.comp (strictLocalizationEval x).hom) :
    liftOfRingHom f x p hp χ ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ x := by
  haveI := hp
  haveI : IsAffine ((𝟭 Scheme.{u}).obj p.1.left) := hp
  haveI hT : IsAffine (pullback p.1.hom f) := inferInstance
  -- the ring-level identity: the character extends evaluation at the stage `p`
  have h1 : strictLocalizationToFiberSections f x ≫ CommRingCat.ofHom χ =
      strictLocalizationEval x ≫ CommRingCat.ofHom ψ := by
    ext a
    exact RingHom.congr_fun hχ a
  have hring : (pullback.fst p.1.hom f).appTop ≫
      CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom) =
      Scheme.Γ.map p.2.val.op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫
        CommRingCat.ofHom ψ := by
    calc (pullback.fst p.1.hom f).appTop ≫
          CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)
        = (Scheme.Γ.map (pullback.fst p.1.hom f).op ≫ toFiberSections f x p) ≫
            CommRingCat.ofHom χ := rfl
      _ = (toStrictLocalization x p ≫ strictLocalizationToFiberSections f x) ≫
            CommRingCat.ofHom χ := by
            rw [toStrictLocalization_strictLocalizationToFiberSections]
      _ = toStrictLocalization x p ≫ strictLocalizationEval x ≫ CommRingCat.ofHom ψ := by
            rw [Category.assoc, h1]
      _ = Scheme.Γ.map p.2.val.op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫
            CommRingCat.ofHom ψ := by
            rw [← Category.assoc, toStrictLocalization_strictLocalizationEval,
              Category.assoc]
  -- the key geometric identity: the lift composed with the projection is `ε ≫ u`
  have hkey : Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)) ≫
      (pullback p.1.hom f).isoSpec.inv ≫ pullback.fst p.1.hom f =
      Spec.map (CommRingCat.ofHom ψ) ≫ p.2.val := by
    apply ext_of_isAffine
    have e1 : (Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom))).appTop =
        (Scheme.ΓSpecIso Γ(pullback p.1.hom f, ⊤)).hom ≫
          CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom) ≫
          (Scheme.ΓSpecIso (CommRingCat.of Ω')).inv := by
      rw [← ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
    have e2 : (Spec.map (CommRingCat.ofHom ψ)).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom ψ ≫
          (Scheme.ΓSpecIso (CommRingCat.of Ω')).inv := by
      rw [← ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
      isoSpec_inv_appTop', e1, e2]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc, reassoc_of% hring]
    rfl
  -- conclude by the pullback square and the neighbourhood structure morphism
  change (Spec.map (CommRingCat.ofHom (χ.comp (toFiberSections f x p).hom)) ≫
    (pullback p.1.hom f).isoSpec.inv ≫ pullback.snd p.1.hom f) ≫ f = _
  rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc,
    ← Category.assoc, Category.assoc _ _ (pullback.fst p.1.hom f), hkey,
    Category.assoc]
  have hu : p.2.val ≫ p.1.hom = x := p.2.property
  rw [hu]

/-- **The lifts of `x` associated to the maximal ideals of the fiber sections**: for a
finite morphism `f : Y ⟶ X` and a geometric point `x : Spec Ω ⟶ X`, there is a family
of characters of the fiber sections with values in the algebraic closure `Ω'` of `Ω`,
whose kernels are exactly the maximal ideals of the fiber sections, such that the
associated geometric points of `Y` lift `x` along `Spec Ω' ⟶ Spec Ω`. This is the
family of lifts appearing in the comparison map
`AlgebraicGeometry.Scheme.Etale.pushforwardStalkToPiStalk`. -/
theorem exists_ringHom_liftOfRingHom_comp (p : (geometricPoint x).fiber.Elements)
    (hp : IsAffine p.1.left) :
    ∃ χ : (m : MaximalSpectrum (fiberSections f x)) →
        (fiberSections f x →+* AlgebraicClosure Ω),
      (∀ m, RingHom.ker (χ m) = m.asIdeal) ∧
      ∀ m, liftOfRingHom f x p hp (χ m) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))) ≫ x := by
  choose χ hker hcomp using fun m : MaximalSpectrum (fiberSections f x) =>
    exists_ringHom_ker_eq f x m
  exact ⟨χ, hker, fun m => liftOfRingHom_comp f x p hp (χ m) (hcomp m)⟩

end Lifts

end FiberSections

end AlgebraicGeometry.Scheme.Etale
