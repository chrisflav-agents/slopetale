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
  obtain ⟨s, hs, V, hc, hunion⟩ := hU
  classical
  -- Strategy: For each i ∈ s, pick some k : σ i and construct a compact open in Y i k
  -- whose image under f i ∘ g i k equals f i '' V i hi
  --
  -- Issue: Without continuity of g i k, we cannot construct compact opens in Y i k
  -- from compact opens in X i. The preimage g i k ⁻¹' V i is not necessarily open
  -- or compact without continuity.
  --
  -- Possible approaches tried:
  -- 1. Use preimages: fails without continuity
  -- 2. Use Set.univ: fails without compactness of Y i k
  -- 3. Use right inverse: fails without continuity of surjInv
  --
  -- This lemma appears to require additional assumptions such as:
  -- - Continuous (g i k), or
  -- - CompactSpace (Y i k), or
  -- - Some other topological property
  sorry

end IsCompactOpenCovered
