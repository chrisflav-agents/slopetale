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

lemma primeCompl_prod_top (q : Ideal S) [q.IsPrime] :
    letI : (q.prod ⊤ : Ideal (S × T)).IsPrime := Ideal.isPrime_ideal_prod_top
    (q.prod ⊤ : Ideal (S × T)).primeCompl = (q.primeCompl.prod ⊤ : Submonoid (S × T)) := by
  letI : (q.prod ⊤ : Ideal (S × T)).IsPrime := Ideal.isPrime_ideal_prod_top
  ext ⟨s, t⟩
  simp only [Ideal.primeCompl, Submonoid.mem_prod, Submonoid.mem_top, and_true]
  show (s, t) ∉ q.prod ⊤ ↔ s ∉ q
  simp [Ideal.mem_prod]

/-- The localization of `S × T` at `q.prod ⊤` is isomorphic to `S_q × T`. -/
noncomputable def prodTopEquiv (q : Ideal S) [q.IsPrime] :
    letI : (q.prod ⊤ : Ideal (S × T)).IsPrime := Ideal.isPrime_ideal_prod_top
    Localization.AtPrime (q.prod ⊤ : Ideal (S × T)) ≃+* Localization.AtPrime q × T := by
  letI : (q.prod ⊤ : Ideal (S × T)).IsPrime := Ideal.isPrime_ideal_prod_top
  -- MATHEMATICAL ISSUE: The naive approach fails because we need to show that
  -- (algebraMap S (Localization.AtPrime q) s, t) is a unit in Localization.AtPrime q × T
  -- whenever s ∉ q. While the first component is a unit, t is not necessarily a unit in T.
  -- This suggests the statement may need revision or a different construction approach.
  sorry

end Localization.AtPrime
