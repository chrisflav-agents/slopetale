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
  /-
  WARNING: This stated equivalence is mathematically incorrect as written.

  The localization `Localization.AtPrime (q.prod ⊤)` inverts the submonoid
  `(q.prod ⊤).primeCompl = (S \ q) × T`. In particular, `(1, 0)` lies in this
  submonoid (since `1 ∉ q` by primeness), so `(1, 0)` becomes a unit in the
  localization. But `(1, 0) * (0, t) = 0` in `S × T`, hence `(0, t) = 0` in
  the localization for every `t : T`. This collapses the entire second factor:

      Localization.AtPrime (q.prod ⊤)  ≃+*  Localization.AtPrime q

  (i.e. just `S_q`), not `S_q × T`. The following is a self-contained
  verification (compiles in isolation under the same imports):

      example {S T : Type*} [CommRing S] [CommRing T] (q : Ideal S) [hq : q.IsPrime]
          (t : T) :
          letI : (q.prod (⊤ : Ideal T)).IsPrime := Ideal.isPrime_ideal_prod_top
          (algebraMap (S × T) (Localization (q.prod (⊤ : Ideal T)).primeCompl))
              (0, t) = 0 := by
        letI : (q.prod (⊤ : Ideal T)).IsPrime := Ideal.isPrime_ideal_prod_top
        rw [IsLocalization.map_eq_zero_iff (q.prod (⊤ : Ideal T)).primeCompl]
        refine ⟨⟨(1, 0), ?_⟩, ?_⟩
        · rw [Ideal.mem_primeCompl_iff, Ideal.mem_prod]
          exact fun h => absurd h.1 ((Ideal.ne_top_iff_one _).mp hq.ne_top)
        · simp

  A cleaner conceptual argument: `Localization.AtPrime` of a commutative ring
  at any prime is a *local* ring, but `S_q × T` is local iff `T` is local,
  and `T` here is arbitrary. Hence the two cannot be ring-isomorphic in
  general.

  The agent prompt forbids modifying the declaration statement, so this is
  left as `sorry` for the plan agent to decide. Recommended fix: change the
  codomain to `Localization.AtPrime q` (drop the `× T`). The corrected
  equivalence can then be built via the universal property in both
  directions, using `(1, 0) ∈ (q.prod ⊤).primeCompl` as the witness that
  identifies `(s, t)/(u, v)` with `(s, 1)/(u, 1)` in the localization (since
  the difference lies in `(0, _) = 0`).
  -/
  sorry

end Localization.AtPrime
