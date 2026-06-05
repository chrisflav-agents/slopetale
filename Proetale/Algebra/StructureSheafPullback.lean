/-
Copyright (c) 2026 Archon agents. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon agents
-/
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheafify
import Proetale.Algebra.StalkIso

/-!
# Inverse-image of the structure sheaf for `BijectiveOnStalks` algebras

Given a ring homomorphism `A → B` such that `Algebra.BijectiveOnStalks A B`, the
induced morphism of locally ringed spaces `q : Spec B → Spec A` has the property
that the structure-sheaf comparison map
`(Spec A).presheaf ⟶ q.base _* (Spec B).presheaf`
(equivalently, by `q⁻¹ ⊣ q_*` adjunction, the counit
`q⁻¹ 𝒪_{Spec A} → 𝒪_{Spec B}`) is an isomorphism of sheaves of rings on
`Spec B`.

This is the Stacks 096J / 096L content lifted into a project-side helper because
the consumer `Algebra.BijectiveOnStalks.exists_algHom_of_continuousMap` (in
`Proetale/Algebra/IdentifiesLocalRings.lean`) needs it at the inverse-image level
on `Spec B` rather than on `Spec A`.

Reference: blueprint chapter `local-structure.tex`
`lem:identifies-local-ring-invImage-structureSheaf-iso`.
-/

universe u

open AlgebraicGeometry CategoryTheory TopCat

namespace TopCat.Presheaf

/-- Sheafification preserves stalks, in a concrete category with sheafification.
This is the concrete-category analogue of Mathlib's `TopCat.Presheaf.sheafifyStalkIso`
(which is `Type`-valued); the file `Mathlib.Topology.Sheaves.Sheafify` carries an
`assert_not_exists CommRingCat`, but the more general lemma
`stalkFunctor_map_unit_toSheafify_isIso` in the same file already covers
`CommRingCat` and other concrete categories.
This is just a thin rename for blueprint cross-reference. -/
lemma sheafifyStalkIso_concrete
    {C : Type (u+1)} [Category.{u} C] [Limits.HasColimits C] [Limits.HasTerminal C]
    {X : TopCat.{u}} [HasWeakSheafify (Opens.grothendieckTopology X) C]
    (F : X.Presheaf C) (x : X) :
    IsIso ((stalkFunctor C x).map
      ((sheafificationAdjunction (Opens.grothendieckTopology X) C).unit.app F)) :=
  stalkFunctor_map_unit_toSheafify_isIso x C F

end TopCat.Presheaf

namespace Algebra.BijectiveOnStalks

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.BijectiveOnStalks A B]

/-- The inverse-image map of structure sheaves on `Spec B` associated to the
locally-ringed-space morphism `q : Spec B → Spec A` induced by `A → B`:
namely, the morphism of sheaves of rings on `Spec B`
`q⁻¹ 𝒪_{Spec A} → 𝒪_{Spec B}` obtained as the `q⁻¹ ⊣ q_*` adjunction transpose
of the direct-image c-component
`𝒪_{Spec A} → q_* 𝒪_{Spec B}` packaged as a morphism of sheaves on `Spec A`. -/
noncomputable def invImageStructureSheafHom :
    (TopCat.Sheaf.pullback CommRingCat
        (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap A B))).toHom.base).obj
      (Spec.locallyRingedSpaceObj (CommRingCat.of A)).sheaf ⟶
      (Spec.locallyRingedSpaceObj (CommRingCat.of B)).sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat
        (Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap A B))).toHom.base).homEquiv
      _ _).symm
    ⟨(Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraMap A B))).toHom.c⟩

/-- The bijective ring map `A_{q∩A} →+* B_q` provided by `BijectiveOnStalks`
packaged as a `RingEquiv`. -/
noncomputable def localRingEquiv (p : Ideal B) [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap A B)) ≃+* Localization.AtPrime p :=
  RingEquiv.ofBijective _
    (Algebra.BijectiveOnStalks.bijective_localRingHom (R := A) (S := B) p)

/-- When `A → B` identifies local rings, the canonical inverse-image map of
structure sheaves on `Spec B`, `q⁻¹ 𝒪_{Spec A} → 𝒪_{Spec B}`, is an isomorphism
of sheaves of rings on `Spec B`. This is the Stacks 096J / 04D2 content at the
inverse-image level.

Proof strategy (per blueprint
`lem:identifies-local-ring-invImage-structureSheaf-iso`): a morphism of sheaves
of rings is an iso iff every stalk map is an iso. At a prime `𝔭 ⊂ B`, the
LHS stalk is identified with the stalk of `𝒪_{Spec A}` at `𝔭 ∩ A`
(`stalkPullbackIso` combined with the sheafification-preserves-stalk
fact); via `StructureSheaf.stalkIso` both stalks become localizations, and
the induced map is `Localization.localRingHom` of `algebraMap A B`, which
is bijective by `Algebra.BijectiveOnStalks.bijective_localRingHom`.

The technical sheaf-level identification of the stalk of
`Sheaf.pullback _ q.base` with the presheaf-level pullback stalk
(`TopCat.Presheaf.stalkPullbackIso`) requires unwinding the
`Sheaf.pullbackIso` (which factors the sheaf pullback through sheafification)
and using that sheafification preserves stalks for concrete categories whose
forget functor preserves filtered colimits. -/
theorem isIso_invImage_structureSheaf :
    IsIso (invImageStructureSheafHom A B) := by
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro p
  -- The bijective local ring map A_{q(p)} → B_p packaged as a CommRingCat iso.
  -- Composed with `StructureSheaf.stalkIso` on both sides, this yields an iso
  -- (𝒪_A).stalk(q.base p) ≅ (𝒪_B).stalk p which agrees (up to canonical
  -- sheaf-pullback stalk identification) with the stalk map of
  -- `invImageStructureSheafHom A B` at p.
  have h_bij : Function.Bijective
      (Localization.localRingHom (p.asIdeal.comap (algebraMap A B)) p.asIdeal
        (algebraMap A B) rfl) :=
    Algebra.BijectiveOnStalks.bijective_localRingHom p.asIdeal
  -- The proof relies on `(forget CommRingCat).reflectsIsomorphisms`; the stalk
  -- functor on `CommRingCat`-valued presheaves becomes the `Type`-level stalk
  -- functor after `forget`, so it suffices to show the underlying type-level
  -- stalk map is bijective. At type level, sheafification preserves stalks
  -- (`TopCat.Presheaf.sheafifyStalkIso` for `Type`, in scope through
  -- `Mathlib.Topology.Sheaves.Sheafify`); the presheaf-level inverse-image
  -- preserves stalks via `Presheaf.stalkPullbackIso`; structure-sheaf stalks
  -- are localizations via `StructureSheaf.stalkIso`; and the underlying
  -- type-level map is `Localization.localRingHom (algebraMap A B)`, which is
  -- bijective by `h_bij`.
  --
  -- The technical content remaining (the chain compatibility) is the
  -- following stalk-level commutative diagram. We package it as a structural
  -- sorry pending a Mathlib-style helper lemma identifying the c-component
  -- of `invImageStructureSheafHom` on germs. The carrier
  -- `sheafifyStalkIso_concrete` is now in scope (see top of file).
  sorry

end Algebra.BijectiveOnStalks
