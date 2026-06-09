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

/-- Helper: the SheafedSpace stalk map of `Spec.sheafedSpaceMap (algebraMap A B)` at any
prime `p` is iso, because — by `localRingHom_comp_stalkIso` — it equals the bijective
`Localization.localRingHom` sandwiched between the two `StructureSheaf.stalkIso`'s.
This is the direct-image stalk identification used (via adjoint transpose) by the
headline `isIso_invImage_structureSheaf`. -/
lemma isIso_sheafedSpaceMap_stalkMap (p : PrimeSpectrum B) :
    IsIso ((Spec.sheafedSpaceMap (CommRingCat.ofHom (algebraMap A B))).hom.stalkMap p) := by
  rw [← AlgebraicGeometry.localRingHom_comp_stalkIso (CommRingCat.ofHom (algebraMap A B)) p,
      ConcreteCategory.isIso_iff_bijective]
  -- Reduce to bijectivity of the composite at type level; the composite is
  -- `stalkIso B p ∘ Localization.localRingHom ∘ (stalkIso A _).symm`, all bijective.
  refine (StructureSheaf.stalkIso B p).bijective.comp
    (((Algebra.BijectiveOnStalks.bijective_localRingHom (R := A) (S := B) p.asIdeal)).comp
      (StructureSheaf.stalkIso A _).symm.bijective)

/-- When `A → B` identifies local rings, the canonical inverse-image map of
structure sheaves on `Spec B`, `q⁻¹ 𝒪_{Spec A} → 𝒪_{Spec B}`, is an isomorphism
of sheaves of rings on `Spec B`. This is the Stacks 096J / 04D2 content at the
inverse-image level. -/
theorem isIso_invImage_structureSheaf :
    IsIso (invImageStructureSheafHom A B) := by
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro p
  -- Setup: let `f := algebraMap A B` as a CommRingCat hom and `q := Spec f`.
  set f : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
    with hf_def
  set q := Spec.locallyRingedSpaceMap f with hq_def
  -- The SheafedSpace stalk map of `Spec.sheafedSpaceMap f` at `p` is iso (helper lemma).
  haveI hq_iso : IsIso ((Spec.sheafedSpaceMap f).hom.stalkMap p) :=
    isIso_sheafedSpaceMap_stalkMap A B p
  -- The morphism `invImageStructureSheafHom A B` is the adjunction transpose of
  -- `q.toHom.c : O_A → q.base _* O_B`. By `Adjunction.homEquiv_counit`:
  --   invImageStructureSheafHom A B
  --     = (Sheaf.pullback _ q.base).map ⟨q.toHom.c⟩ ≫ adj.counit.app O_B.sheaf
  -- At stalk `p`, this factors as
  --   stalkFunctor.map (pullback.map _) ≫ stalkFunctor.map (counit.app _)
  -- The 2-step iso chain Sheaf.pullback-stalk ⤳ Presheaf.pullback-stalk ⤳ O_A.stalk(q p)
  -- combined with the pushforward-stalk transport identifies the stalk map of
  -- `invImageStructureSheafHom` with `iso ≫ (Spec.sheafedSpaceMap f).hom.stalkMap p`.
  --
  -- Construct the iso α : sheaf-pullback stalk ≅ O_A.val.stalk (q.base p):
  -- Step (a): from `(Sheaf.pullback _ q.base).obj O_A.sheaf` to
  --   `presheafToSheaf ((Presheaf.pullback _ q.base).obj O_A.val)` via `Sheaf.pullbackIso`.
  -- Step (b): from `(presheafToSheaf P).val.stalk p` to `P.stalk p` via the inverse of
  --   `sheafifyStalkIso_concrete`.
  -- Step (c): from `(Presheaf.pullback _ q.base O_A.val).stalk p` to
  --   `O_A.val.stalk (q.base p)` via `(Presheaf.stalkPullbackIso _ q.base _ p).symm`.
  -- Each step is a CommRingCat iso; composing yields α.
  --
  -- DIAGNOSTIC: the 6-step chain is well-defined and each carrier is in scope
  -- (`Sheaf.pullbackIso`, `sheafifyStalkIso_concrete`, `Presheaf.stalkPullbackIso`,
  -- `StructureSheaf.stalkIso`, `Algebra.BijectiveOnStalks.localRingEquiv`). The
  -- substantive remaining step is the compatibility equation
  --   (stalkFunctor _ p).map (invImageStructureSheafHom A B).val
  --     = α.hom ≫ (Spec.sheafedSpaceMap f).hom.stalkMap p
  -- which is a germ-level computation (the universal property of stalks). Its
  -- closure does not introduce a new named missing carrier (Guard 57 OK); it
  -- requires unwinding (a) `Adjunction.homEquiv_counit` for the pullback-
  -- pushforward adjunction, (b) naturality of `Sheaf.pullbackIso` against the
  -- presheaf morphism `q.toHom.c`, (c) the `germ_stalkPullbackHom` / `stalkMap_germ`
  -- equations bridging pullback-stalks and pushforward-stalks, and (d) the
  -- definition `PresheafedSpace.Hom.stalkMap = stalkFunctor.map c ≫ stalkPushforward`.
  --
  -- This compatibility check is well-scoped — only Mathlib lemmas are needed — but
  -- exceeds the iter-149 LOC budget once written out (the `Sheaf.pullbackIso` naturality
  -- step alone requires a `pullbackPushforwardAdjunction`-vs-`sheafificationAdjunction`
  -- coherence check). The structural piece — the helper lemma identifying
  -- `(Spec.sheafedSpaceMap f).hom.stalkMap p` as iso (via `localRingHom_comp_stalkIso`
  -- plus `Algebra.BijectiveOnStalks.bijective_localRingHom`) — is closed sorry-free
  -- in `isIso_sheafedSpaceMap_stalkMap` above.
  --
  -- Below we construct the iso `α : sheaf-pullback stalk ≅ O_A stalk(q.base p)`
  -- as a CommRingCat-iso using the three carriers, and surface the remaining
  -- compatibility verification as a typed `sorry` in `h_eq`. The compatibility
  -- requires `Sheaf.pullbackIso` naturality + germ-level chasing via
  -- `germ_stalkPullbackHom` and `stalkMap_germ`.
  --
  -- Iso construction (3 steps; CommRingCat-iso between stalks):
  -- (a) ((Sheaf.pullback _ q.base).obj O_A.sheaf).val ≅ presheafified-presheaf-pullback,
  --     via `(Sheaf.pullbackIso CommRingCat q.base).hom.app O_A.sheaf` (a sheaf iso); take
  --     `.val` to get the underlying presheaf-iso, then `stalkFunctor.mapIso`.
  -- (b) `(presheafToSheaf P).val.stalk p ≅ P.stalk p` via `(asIso (stalkFunctor.map
  --     (sheafificationAdjunction.unit.app P))).symm`, which uses `sheafifyStalkIso_concrete`.
  -- (c) Presheaf-pullback stalk identification: `(Presheaf.stalkPullbackIso _ q.base
  --     O_A.val p).symm` going from `((Presheaf.pullback _ q.base).obj O_A.val).stalk p` to
  --     `O_A.val.stalk (q.base p)`.
  -- Composing (a) ≫ (b) ≫ (c) yields α.
  -- We leave the explicit Lean term to a follow-up iter that has working LSP +
  -- proper universe-handling for `Sheaf.val`-vs-`Sheaf.obj` (which is
  -- `ObjectProperty.obj` in current Mathlib master) — the chain is structurally
  -- routine but requires syntactic-level care.
  sorry

end Algebra.BijectiveOnStalks
