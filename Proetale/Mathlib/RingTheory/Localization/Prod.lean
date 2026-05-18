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
    Localization.AtPrime (q.prod ⊤ : Ideal (S × T)) ≃+* Localization.AtPrime q × T :=
  sorry

end Localization.AtPrime
