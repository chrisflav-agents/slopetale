/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Prod

/-!
# Localization of product rings

This file is reserved for results about localization of product rings at product ideals.

The previously stated equivalence
`Localization.AtPrime (q.prod ⊤ : Ideal (S × T)) ≃+* Localization.AtPrime q × T`
is mathematically incorrect: the element `(1, 0)` lies in
`(q.prod ⊤).primeCompl` (since `1 ∉ q` by primeness) and `(1, 0) * (0, t) = 0`,
so `(0, t) = 0` in the localization for every `t : T`, collapsing the second
factor. The mathematically correct equivalence
`Localization.AtPrime (q.prod ⊤ : Ideal (S × T)) ≃+* Localization.AtPrime q`
may be added here when a consumer needs it.
-/
