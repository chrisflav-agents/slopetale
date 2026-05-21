/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Proetale.Mathlib.CategoryTheory.NatIso

/-!
# Local properties of sheafs
-/

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category C] (K : GrothendieckTopology C)
variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable {J : Type*} [Category J]

namespace Sheaf

--structure IsLocal (P : ObjectProperty (Sheaf K A)) : Prop where
--  iff_of_coversTop (F : Sheaf K A) {ι : Type*} (X : ι → C) (h : K.CoversTop X) :
--    P F ↔ ∀ i, P (F.over (X i))

variable {ι : Type*} (X : ι → C) (hX : K.CoversTop X)
include hX

lemma foo (F : Sheaf K A) [HasColimitsOfShape J A] [(forget A).ReflectsIsomorphisms]
    (hF : ∀ i : ι, PreservesColimitsOfShape J (F.over (X i)).obj) :
    PreservesColimitsOfShape J F.obj := by
  constructor
  intro D
  constructor
  intro c hc
  constructor
  -- Strategy: reduce IsIso of the desc map to checking it locally on the cover X.
  -- Each local desc (under F.over (X i)) is an iso by hF i, and (forget A) reflects isos.
  -- We use sheaf property on the cover hX.cover c.pt.unop to globalize injectivity and
  -- surjectivity from the restrictions.
  --
  -- KEY OBSTRUCTION (round 2, 2026-05-18): the bijection approach via
  -- `ConcreteCategory.isIso_iff_bijective` reduces to bijectivity of `desc` viewed
  -- as a FunLike on underlying types. But the *underlying type* of
  -- `colim_A (D ⋙ F.obj)` is opaque without the additional hypothesis
  -- `[PreservesColimitsOfShape J (forget A)]` (compare
  -- `Mathlib/CategoryTheory/Sites/ConcreteSheafification.lean:202`, where this
  -- hypothesis is essential).  The current statement of `foo` is therefore
  -- under-hypothesised and the proof cannot be closed without amending it.
  -- See `task_results/Topology_LocalProperties.lean.md` for analysis.
  have : IsIso ((colimit.isColimit (D ⋙ F.obj)).desc (F.obj.mapCocone c)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    simp only [colimit.cocone_x, Functor.mapCocone_pt, colimit.isColimit_desc]
    -- Each `(F.over (X i)).obj` preserves colimits of shape J, so the analogous desc
    -- restricted to `op (Over.mk g)` for `g : Y ⟶ X i` is bijective.  We piece these
    -- together via `hX.cover c.pt.unop` and the sheaf property of `F`.
    refine ⟨?_, ?_⟩
    · -- Injectivity: use sheaf property on covering
      -- Plan: lift x₁ - x₂ to a morphism in A, then use F.2.hom_ext on the sieve
      -- `hX.cover c.pt.unop`. For each S.Arrow with `g : Y ⟶ X i` factoring through X i,
      -- the restriction to the over-sheaf `(F.over (X i)).obj` evaluated at `op (Over.mk g)`
      -- gives the desc map for the i-th over-sheaf, which is injective by `hF i` plus
      -- `(forget A).ReflectsIsomorphisms` and `ConcreteCategory.isIso_iff_bijective`.
      -- Conclude `x₁ = x₂` after restriction; gather via sheaf separatedness.
      --
      -- BLOCKED: needs an injectivity statement at element level, which requires
      -- describing elements of `colim_A (D ⋙ F.obj)` as `(j, x_j)` modulo
      -- equivalence — only possible if `(forget A).PreservesColimitsOfShape J`.
      -- Add this typeclass to the statement of `foo` (mirroring the API in
      -- `Sites/ConcreteSheafification.lean`) and the natural sheaf-separatedness
      -- argument closes injectivity.
      intro x₁ x₂ h
      sorry
    · -- Surjectivity: use sheaf amalgamation to construct preimage
      -- Plan: given y ∈ F.obj.obj c.pt, restrict to each X i via `F.obj.map I.f.op`.
      -- For each i, the desc map for `(F.over (X i)).obj` is surjective (by `hF i`),
      -- so we obtain `xᵢ` in the i-th colimit mapping to the i-th restriction of y.
      -- These xᵢ are compatible across overlaps; amalgamate via `F.2.amalgamate` on
      -- `hX.cover c.pt.unop` to obtain the preimage in `colim (D ⋙ F.obj)`.
      --
      -- BLOCKED: same root cause — building an *element* in `colim_A (...)` from
      -- local data requires `forget A` to preserve J-colims (so that elements
      -- have the form `colimit.ι _ j x_j`).  Without that, the surjectivity check
      -- has no foothold.  Same fix as injectivity: amend the statement of `foo`
      -- to include `[PreservesColimitsOfShape J (forget A)]`.
      intro y
      sorry
  exact .ofPointIso (colimit.isColimit _)

end Sheaf

lemma _root_.CategoryTheory.Sieve.le_pullback_coverByImage {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D)
    {X Y : D} (f : X ⟶ Y) :
    Sieve.coverByImage F X ≤ Sieve.pullback f (Sieve.coverByImage F Y) := by
  simp only [Sieve.coverByImage]
  intro Z g
  rintro ⟨⟨W, b, c, heq⟩⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩⟩
  · use W
  · use b
  · use c ≫ f
  · rw [reassoc_of% heq]

lemma _root_.CategoryTheory.Functor.IsCoverDense.of_coversTop {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) (J : GrothendieckTopology D) {ι : Type*} (X : ι → C)
    (hX : J.CoversTop (fun i ↦ F.obj (X i)))
    (H : ∀ i, (Over.post (X := X i) F).IsCoverDense (J.over _)) :
    F.IsCoverDense J := by
  constructor
  intro U
  let S := hX.cover U
  refine J.transitive S.2 _ ?_
  rintro Y f ⟨i, ⟨g⟩⟩
  refine J.superset_covering (CategoryTheory.Sieve.le_pullback_coverByImage _ _) ?_
  have := (H i).is_cover (Over.mk g)
  rw [GrothendieckTopology.mem_over_iff] at this
  dsimp at this
  refine J.superset_covering ?_ this
  intro W a ha
  rw [dsimp% Sieve.overEquiv_iff (Y := Over.mk g) _ a] at ha
  obtain ⟨⟨Z, v, w, huv⟩⟩ := ha
  refine ⟨⟨?_, ?_, ?_, ?_⟩⟩
  · use Z.left
  · use v.left
  · use w.left
  · exact congr($(huv).left)

lemma _root_.CategoryTheory.Functor.IsCoverDense.of_natIso {C D : Type*} [Category* C]
    [Category* D] {F G : C ⥤ D} {J : GrothendieckTopology D} (e : F ≅ G)
    [F.IsCoverDense J] : G.IsCoverDense J := by
  obtain ⟨hF⟩ := ‹F.IsCoverDense J›
  refine ⟨fun U => J.superset_covering ?_ (hF U)⟩
  rintro Y f ⟨⟨Z, ℓ, k, hfg⟩⟩
  refine ⟨⟨Z, ℓ ≫ e.hom.app Z, e.inv.app Z ≫ k, ?_⟩⟩
  simp [hfg]

lemma _root_.CategoryTheory.Functor.IsCoverDense.iff_of_natIso {C D : Type*} [Category* C]
    [Category* D] {F G : C ⥤ D} {J : GrothendieckTopology D} (e : F ≅ G) :
    F.IsCoverDense J ↔ G.IsCoverDense J :=
  ⟨fun _ => .of_natIso e, fun _ => .of_natIso e.symm⟩

lemma _root_.CategoryTheory.Functor.IsCoverDense.comp_iff_of_isCoverDense {C D E : Type*}
    [Category* C] [Category* D] [Category* E] {F : C ⥤ D} {G : D ⥤ E} {J : GrothendieckTopology E}
    [G.IsCoverDense J] [G.Full] [G.Faithful] :
    (F ⋙ G).IsCoverDense J ↔ F.IsCoverDense (G.inducedTopology J) := by
  refine ⟨fun ⟨h⟩ => ⟨fun U => J.superset_covering ?_ (h (G.obj U))⟩,
    fun ⟨h⟩ => ⟨fun U => ?_⟩⟩
  · -- forward direction
    rintro Y f ⟨⟨Z, lift, map, rfl⟩⟩
    refine ⟨F.obj Z, G.preimage map, lift, ⟨⟨Z, 𝟙 _, G.preimage map, ?_⟩⟩, by simp⟩
    simp
  · -- reverse direction: F cover-dense in induced ⟹ F⋙G cover-dense in J
    apply J.transitive (G.is_cover_of_isCoverDense J U)
    rintro Y _ ⟨⟨X, lift_b, map_b, rfl⟩⟩
    refine J.superset_covering ?_ (J.pullback_stable lift_b (h X))
    rintro V c ⟨T, k, h_c, ⟨⟨W, lift_a, map_a, hfac⟩⟩, hac⟩
    refine ⟨⟨W, h_c ≫ G.map lift_a, G.map map_a ≫ map_b, ?_⟩⟩
    rw [reassoc_of% hac, ← hfac, G.map_comp]
    simp

lemma _root_.CategoryTheory.Functor.IsCoverDense.comp_iff_of_isEquivalence {C D E : Type*}
    [Category* C] [Category* D] [Category* E] {F : C ⥤ D} {G : D ⥤ E}
    {J : GrothendieckTopology E} [F.IsEquivalence] :
    (F ⋙ G).IsCoverDense J ↔ G.IsCoverDense J := by
  refine ⟨fun ⟨h⟩ => ⟨fun U => J.superset_covering ?_ (h U)⟩,
    fun ⟨h⟩ => ⟨fun U => J.superset_covering ?_ (h U)⟩⟩
  · rintro Y f ⟨⟨Z, ℓ, k, hfg⟩⟩
    exact ⟨⟨F.obj Z, ℓ, k, hfg⟩⟩
  · rintro Y f ⟨⟨Z, ℓ, k, hfg⟩⟩
    refine ⟨⟨F.objPreimage Z, ℓ ≫ G.map (F.objObjPreimageIso Z).inv,
      G.map (F.objObjPreimageIso Z).hom ≫ k, ?_⟩⟩
    simp [← G.map_comp_assoc, hfg]

end CategoryTheory
