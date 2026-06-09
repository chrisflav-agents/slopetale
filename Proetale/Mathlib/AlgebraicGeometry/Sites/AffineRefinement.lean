/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Basic-open refinement of an open-immersion cover of an affine scheme

Given an affine scheme `X` covered by a family of open immersions `f i : Y i ⟶ X`,
we can find for each point `x ∈ X` a basic open `D(g x) ⊆ X` containing `x`
and contained in the range of some `f (i x)`, hence factoring through it.

This is used in the small affine pro-étale site to refine arbitrary open-immersion
Zariski covers of an affine pro-étale object into basic-open refinements lying in
the image of the inclusion `AffineProEt ⥤ ProEt`.
-/

universe v u

open CategoryTheory

namespace AlgebraicGeometry

/-- Pointwise basic-open refinement of an open-immersion cover of an affine scheme.

Given an affine scheme `X` and an open-immersion family `f i : Y i ⟶ X` whose
ranges cover `X`, for each point `x : X` we extract a chart index `i x : ι` and a
global section `g x : Γ(X, ⊤)` such that the basic open `D(g x) ⊆ X` contains `x`
and is contained in the range of `f (i x)`. -/
lemma exists_basicOpen_refinement_of_isAffine_cover
    {X : Scheme.{u}} [IsAffine X] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⋃ i, Set.range (f i).base = Set.univ) :
    ∃ (i : X → ι) (g : X → Γ(X, ⊤)),
      (∀ x : X, x ∈ X.basicOpen (g x)) ∧
      (∀ x : X, X.basicOpen (g x) ≤ (f (i x)).opensRange) := by
  choose i hi using fun x : X ↦ show ∃ j, x ∈ (f j).opensRange by
    have hx : x ∈ ⋃ j, Set.range (f j).base := hcov ▸ Set.mem_univ _
    obtain ⟨_, ⟨j, rfl⟩, hi⟩ := hx
    exact ⟨j, hi⟩
  choose g hle hg using fun x : X ↦
    (isAffineOpen_top X).exists_basicOpen_le (V := (f (i x)).opensRange) ⟨x, hi x⟩ trivial
  exact ⟨i, g, hg, hle⟩

/-- Variant of `exists_basicOpen_refinement_of_isAffine_cover` packaging the basic
opens as `Scheme` morphisms factoring through the cover. -/
lemma exists_basicOpen_lift_of_isAffine_cover
    {X : Scheme.{u}} [IsAffine X] {ι : Type v} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⋃ i, Set.range (f i).base = Set.univ) :
    ∃ (i : X → ι) (g : X → Γ(X, ⊤))
      (e : ∀ x, (X.basicOpen (g x) : Scheme) ⟶ Y (i x)),
      (∀ x : X, x ∈ X.basicOpen (g x)) ∧
      (∀ x : X, e x ≫ f (i x) = (X.basicOpen (g x)).ι) := by
  obtain ⟨i, g, hmem, hle⟩ := exists_basicOpen_refinement_of_isAffine_cover f hcov
  refine ⟨i, g, fun x ↦ IsOpenImmersion.lift (f (i x)) (X.basicOpen (g x)).ι ?_, hmem,
    fun x ↦ IsOpenImmersion.lift_fac _ _ _⟩
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
  exact_mod_cast hle x

end AlgebraicGeometry
