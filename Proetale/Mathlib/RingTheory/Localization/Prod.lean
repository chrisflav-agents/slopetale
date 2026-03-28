/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Prod

/-!
# Localization of product rings

This file contains results about localization of product rings at product ideals.
-/

variable {S T : Type*} [CommRing S] [CommRing T]

namespace Localization.AtPrime

/-- The localization of `S × T` at `q.prod ⊤` is isomorphic to `S_q × T`. -/
def prodTopEquiv (q : Ideal S) [q.IsPrime] :
    letI : (q.prod ⊤ : Ideal (S × T)).IsPrime := Ideal.isPrime_ideal_prod_top
    Localization.AtPrime (q.prod ⊤ : Ideal (S × T)) ≃+* Localization.AtPrime q × T := by
  letI : (q.prod ⊤ : Ideal (S × T)).IsPrime := Ideal.isPrime_ideal_prod_top
  -- Forward: (s,t)/(u,v) ↦ (s/u, t)
  have fwd_units : ∀ x : (q.prod ⊤ : Ideal (S × T)).primeCompl,
      IsUnit ((algebraMap S (Localization.AtPrime q) x.val.1, x.val.2) :
        Localization.AtPrime q × T) := by
    intro ⟨⟨s, t⟩, h⟩
    simp [Ideal.primeCompl, Ideal.mem_prod] at h
    refine ⟨⟨(algebraMap S (Localization.AtPrime q) s, t),
      (IsLocalization.map_units _ ⟨s, h⟩).unit⁻¹.1, ?_, ?_⟩, rfl⟩
    · sorry
    · sorry
  set fwd := IsLocalization.lift fwd_units
  refine RingEquiv.ofBijective fwd ⟨?_, ?_⟩
  · sorry -- injectivity
  · sorry -- surjectivity

end Localization.AtPrime
