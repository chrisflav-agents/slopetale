/-
Copyright (c) 2026 Archon agents. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon agents
-/
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Topology.Sheaves.Stalks
import Proetale.Algebra.StalkIso

/-!
# Banked utilities for `BijectiveOnStalks`-flavored constructions

This file collects small, sorry-free utilities about the structure-sheaf side of
`Algebra.BijectiveOnStalks A B`. The previous SSP-spine route (an
inverse-image structure-sheaf iso `q⁻¹ 𝒪_{Spec A} ≅ 𝒪_{Spec B}`) has been
retired in favour of the LRS-route at
`lem:exists-algHom-of-continuousMap-via-LRS` in
`blueprint/src/chapters/local-structure.tex`; the construction now happens in
`Proetale/Algebra/IdentifiesLocalRings.lean` using
`LocallyRingedSpace.homMk` and `AlgebraicGeometry.Spec.preimage`.

What remains here are two banked utilities that may still be reused by the
LRS-route prover or by other `BijectiveOnStalks` consumers:

* `Algebra.BijectiveOnStalks.localRingEquiv` — package the bijective
  `Localization.localRingHom` as a `RingEquiv`.
* `Algebra.BijectiveOnStalks.isIso_sheafedSpaceMap_stalkMap` — the
  `SheafedSpace` stalk map of `Spec.sheafedSpaceMap (algebraMap A B)` is iso
  at every prime, via `localRingHom_comp_stalkIso`.
-/

universe u

open AlgebraicGeometry CategoryTheory TopCat

namespace Algebra.BijectiveOnStalks

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.BijectiveOnStalks A B]

/-- The bijective ring map `A_{q∩A} →+* B_q` provided by `BijectiveOnStalks`
packaged as a `RingEquiv`. -/
noncomputable def localRingEquiv (p : Ideal B) [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap A B)) ≃+* Localization.AtPrime p :=
  RingEquiv.ofBijective _
    (Algebra.BijectiveOnStalks.bijective_localRingHom (R := A) (S := B) p)

/-- Helper: the SheafedSpace stalk map of `Spec.sheafedSpaceMap (algebraMap A B)` at any
prime `p` is iso, because — by `localRingHom_comp_stalkIso` — it equals the bijective
`Localization.localRingHom` sandwiched between the two `StructureSheaf.stalkIso`'s. -/
lemma isIso_sheafedSpaceMap_stalkMap (p : PrimeSpectrum B) :
    IsIso ((Spec.sheafedSpaceMap (CommRingCat.ofHom (algebraMap A B))).hom.stalkMap p) := by
  rw [← AlgebraicGeometry.localRingHom_comp_stalkIso (CommRingCat.ofHom (algebraMap A B)) p,
      ConcreteCategory.isIso_iff_bijective]
  -- Reduce to bijectivity of the composite at type level; the composite is
  -- `stalkIso B p ∘ Localization.localRingHom ∘ (stalkIso A _).symm`, all bijective.
  refine (StructureSheaf.stalkIso B p).bijective.comp
    (((Algebra.BijectiveOnStalks.bijective_localRingHom (R := A) (S := B) p.asIdeal)).comp
      (StructureSheaf.stalkIso A _).symm.bijective)

end Algebra.BijectiveOnStalks
