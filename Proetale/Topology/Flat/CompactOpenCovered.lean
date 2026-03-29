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
  -- This lemma requires additional assumptions to be provable.
  -- With only surjectivity, we cannot construct compact opens in Y i k from compact opens in X i.
  -- The natural approach is to use preimages g i k ⁻¹' V, but:
  -- 1. Without continuity, preimages of opens are not open
  -- 2. Even with continuity, preimages of compacts are not generally compact
  --    (requires IsProperMap, CompactSpace, or similar conditions)
  -- Possible fixes: add (hgc : ∀ i k, Continuous (g i k)) and (hgp : ∀ i k, IsProperMap (g i k))
  -- or add [∀ i k, CompactSpace (Y i k)]
  sorry

end IsCompactOpenCovered
