/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Sets.CompactOpenCovered

/-!
# Compact open covered sets

-/

universe w u v

section

variable {ι S : Type*} {X : ι → Type*}

lemma Set.forall_mem_iUnion_iff {X ι : Type*} {p : X → Prop}
    {s : ι → Set X} :
    (∀ t ∈ (⋃ i, s i), p t) ↔ ∀ (i : ι), ∀ x ∈ s i, p x := by
  simp
  tauto

end

open TopologicalSpace Opens

namespace IsCompactOpenCovered

variable {S ι : Type*} {X : ι → Type v} {f : ∀ i, X i → S} [∀ i, TopologicalSpace (X i)]

lemma comp {σ : ι → Type*} {Y : ∀ (i : ι) (k : σ i), Type*}
    (g : ∀ (i : ι) (k : σ i), Y i k → X i)
    [∀ i k, TopologicalSpace (Y i k)]
    {U : Set S} (hU : IsCompactOpenCovered f U)
    (hg : ∀ i k, Function.Surjective (g i k)) :
    IsCompactOpenCovered (fun (p : Σ (i : ι), σ i) ↦ f p.1 ∘ g p.1 p.2) U := by
  -- NOTE: this lemma is mathematically FALSE as stated — additional topological
  -- hypotheses (continuity of `g i k`, plus a properness/compactness condition)
  -- are required. Counterexample showing the statement can fail:
  --   take `ι = Unit`, `σ () = Unit`, `S = X () = {0,1}` with the discrete
  --   topology, `Y () () = {0,1,2}` with the *indiscrete* topology, `f = id`,
  --   `g 0 = g 2 = 0`, `g 1 = 1` (set-theoretically surjective).
  --   Then `U = {0}` is the image of the compact open `{0} ⊆ X` (witnessing
  --   `hU`), but the only compact opens of `Y () ()` are `∅` and the whole
  --   space, whose images under `f ∘ g` are `∅` and `{0,1}`; no finite union of
  --   these equals `{0}`.
  --
  -- We dispatch the easy `U = ∅` case below. The general case needs the
  -- statement to be strengthened (e.g. by adding `[∀ i k, Continuous (g i k)]`
  -- plus a `PrespectralSpace` / properness hypothesis, mirroring
  -- `IsCompactOpenCovered.of_comp` in Mathlib). The plan agent should adjust
  -- the signature.
  rcases eq_or_ne U ∅ with rfl | hU_ne
  · exact .empty
  obtain ⟨s, hs, V, hc, hunion⟩ := hU
  classical
  -- Partial structural attempt for reference. Assuming we had, for each
  -- `i ∈ s`, a choice `kᵢ : σ i` together with a compact open
  -- `W i hi : Opens (Y i (kᵢ i))` satisfying
  -- `(f i ∘ g i (kᵢ i)) '' W i hi = f i '' (V i hi)`, the proof would be:
  --   refine ⟨(fun i ↦ ⟨i, kᵢ i⟩) '' s, hs.image _,
  --     fun p hp ↦ (W _ _),
  --     fun p hp ↦ (compactness of W _ _),
  --     ?_⟩;
  --   simp_rw [Set.image_image] at *; rw [← hunion]; ext x; ...
  -- The construction of `W` (e.g. as `g i (kᵢ i) ⁻¹' V i hi`) requires the
  -- missing topological hypotheses to ensure it is open and compact.
  sorry

end IsCompactOpenCovered
