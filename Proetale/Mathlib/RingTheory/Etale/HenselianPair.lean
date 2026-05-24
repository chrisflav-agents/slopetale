/-
Copyright (c) 2026 The Proetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Henselian pair for étale algebras over henselian local rings

For `A` a henselian local ring and `B` an étale `A`-algebra, the
pair `(B, m·B)` is a henselian ring in the sense of Mathlib's
`HenselianRing` class (which is equivalently the henselian-pair
predicate from Stacks 09XD). This is the Stacks 04GG / 0DXB
fragment that unblocks the §3-cluster of strictly-henselian
results in `Proetale/Mathlib/RingTheory/Etale/StrictlyHenselian.lean`
and the Hensel-idempotent-lift body of
`Proetale/Mathlib/RingTheory/Etale/HenselianIdempotentLift.lean`.

## Main result

* `Algebra.Etale.henselianRing_map_maximalIdeal`:
  `HenselianRing B ((maximalIdeal A).map (algebraMap A B))` for `A`
  henselian local and `B` étale over `A`.

See `blueprint/src/chapters/Proetale_Mathlib_RingTheory_Etale_HenselianPair.tex`
for the informal proof recipe (Jacobson containment via
Stacks 02FK + Hensel lift via Stacks 0DXB residue-product reduction).
-/

open IsLocalRing

namespace Algebra.Etale

/-- **Stacks 04GG / 09XK; henselian-pair fragment.**

For `A` a henselian local ring and `B` a **finite** étale
`A`-algebra, the pair `(B, m·B)` is a henselian ring: the
extension `m·B` of the maximal ideal of `A` is contained in the
Jacobson radical of `B`, and Hensel's lemma holds for monic
polynomials over `B` at roots mod `m·B`.

This is the abstract endpoint that the four open §3-cluster
sorries (`StrictlyHenselian.lean` L682 / L1767 / L1814 +
`HenselianIdempotentLift.lean` body L160) will consume in
iter-055+ wiring; each consumer must establish
`Module.Finite A B'` for its localized / fibre-restricted `B'`
before applying this instance. -/
instance henselianRing_map_maximalIdeal
    (A B : Type*) [CommRing A] [HenselianLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B] :
    HenselianRing B ((IsLocalRing.maximalIdeal A).map (algebraMap A B)) where
  jac := by
    -- Blueprint: `lem:henselianPair-jac` (integral going-up).
    -- For every maximal `J ⊂ B`, the contraction `J ∩ A` is maximal in
    -- the local ring `A` (going-up via integrality from `Module.Finite`),
    -- hence equals `maximalIdeal A`; the map-comap adjunction then gives
    -- `(maximalIdeal A).map (algebraMap A B) ≤ J`.
    haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal]
    refine le_sInf fun J hJ => ?_
    have hJmax : J.IsMaximal := hJ
    rw [Ideal.map_le_iff_le_comap]
    have hcomap : (J.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
    rw [IsLocalRing.eq_maximalIdeal hcomap]
  is_henselian := by
    -- iter-054+ Stacks 0DXB Hensel-lift body (substantive: Newton
    -- iteration via residue-product decomposition `B/mB ≃ ∏ k_i`
    -- from `Algebra.Etale.iff_exists_algEquiv_prod`, with
    -- convergence via mB-adic separation of B following from
    -- mB ⊆ jacobson B + Krull intersection).
    -- Blueprint: `lem:henselianPair-is-henselian`.
    sorry

end Algebra.Etale
