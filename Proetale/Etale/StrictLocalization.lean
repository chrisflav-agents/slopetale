/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.Etale
import Proetale.Algebra.EtalePoint
import Proetale.Algebra.RetractionsStrictlyHenselian
import Proetale.Mathlib.AlgebraicGeometry.Sites.GeometricPoint
import Proetale.Mathlib.CategoryTheory.Filtered.Final

/-!
# The strict localization of a scheme at a geometric point

For a geometric point `x : Spec Ω ⟶ X` (with `Ω` separably closed), the *strict
localization* of `X` at `x` is the filtered colimit of the rings of global functions
over the étale neighbourhoods of `x`, i.e. over the category of elements of the fiber
functor of the associated point of the small étale site
(`AlgebraicGeometry.Scheme.Etale.geometricPoint`).

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.strictLocalization`: the strict localization, as a
  filtered colimit of commutative rings.
- `AlgebraicGeometry.Scheme.Etale.strictLocalizationEval`: evaluation at the geometric
  point, a ring homomorphism to `Ω`.

## Main results

- `AlgebraicGeometry.Scheme.Etale.isUnit_iff_strictLocalizationEval_ne_zero`: an element
  of the strict localization is a unit if and only if its value at the geometric point
  is nonzero. In particular the strict localization is a local ring and evaluation is a
  local homomorphism.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X)

/-- The underlying scheme of an étale neighbourhood of a geometric point. -/
noncomputable abbrev neighbourhoodScheme
    (p : (geometricPoint x).fiber.Elements) : Scheme.{u} :=
  p.1.left

/-- The diagram of rings of global functions on the étale neighbourhoods of a geometric
point. Its filtered colimit is the strict localization. -/
noncomputable def strictLocalizationDiagram :
    ((geometricPoint x).fiber.Elements)ᵒᵖ ⥤ CommRingCat.{u} :=
  (CategoryOfElements.π (geometricPoint x).fiber ⋙
    Etale.forget X ⋙ CategoryTheory.Over.forget X).op ⋙ Scheme.Γ

/-- The strict localization of `X` at the geometric point `x`: the colimit of the rings
of functions over the étale neighbourhoods of `x`. -/
noncomputable def strictLocalization : CommRingCat.{u} :=
  colimit (strictLocalizationDiagram x)

/-- The canonical map from the functions on an étale neighbourhood to the strict
localization. -/
noncomputable def toStrictLocalization (p : (geometricPoint x).fiber.Elements) :
    Scheme.Γ.obj (op p.1.left) ⟶ strictLocalization x :=
  colimit.ι (strictLocalizationDiagram x) (op p)

@[reassoc, elementwise]
lemma toStrictLocalization_w {p q : (geometricPoint x).fiber.Elements} (g : p ⟶ q) :
    (strictLocalizationDiagram x).map (op g) ≫ toStrictLocalization x p =
      toStrictLocalization x q :=
  colimit.w (strictLocalizationDiagram x) (op g)

/-- The cocone on the neighbourhood diagram given by evaluating functions at the
geometric point. -/
noncomputable def strictLocalizationEvalCocone : Cocone (strictLocalizationDiagram x) where
  pt := CommRingCat.of Ω
  ι :=
    { app p := Scheme.Γ.map p.unop.2.val.op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
      naturality p q f := by
        have h : p.unop.2.val = q.unop.2.val ≫ f.unop.val.left :=
          (congrArg Subtype.val f.unop.property).symm
        dsimp [strictLocalizationDiagram]
        rw [Category.comp_id, ← Category.assoc, ← Scheme.Hom.comp_appTop]
        exact congrArg (· ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom)
          (congrArg Scheme.Hom.appTop h.symm) }

/-- Evaluation of germs at the geometric point, as a homomorphism from the strict
localization to `Ω`. -/
noncomputable def strictLocalizationEval : strictLocalization x ⟶ CommRingCat.of Ω :=
  colimit.desc _ (strictLocalizationEvalCocone x)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toStrictLocalization_strictLocalizationEval
    (p : (geometricPoint x).fiber.Elements) :
    toStrictLocalization x p ≫ strictLocalizationEval x =
      Scheme.Γ.map p.2.val.op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom :=
  colimit.ι_desc _ _

/-- Every element of the strict localization is the germ of a function on some étale
neighbourhood. -/
lemma exists_toStrictLocalization_eq (z : strictLocalization x) :
    ∃ (p : (geometricPoint x).fiber.Elements) (a : Scheme.Γ.obj (op p.1.left)),
      (toStrictLocalization x p).hom a = z := by
  obtain ⟨⟨p⟩, a, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (CategoryTheory.forget CommRingCat)
      (colimit.isColimit (strictLocalizationDiagram x))) z
  exact ⟨p, a, rfl⟩

/-- A function on an étale neighbourhood whose value at the geometric point is
invertible has an invertible germ in the strict localization: the basic open on which
the function is invertible is again an étale neighbourhood. -/
private lemma isUnit_toStrictLocalization_of_isUnit
    (p : (geometricPoint x).fiber.Elements) (a : Scheme.Γ.obj (op p.1.left))
    (hb : IsUnit ((p.2.val.appTop).hom a)) :
    IsUnit ((toStrictLocalization x p).hom a) := by
  haveI : Etale p.1.hom := p.1.prop
  let v : Spec (CommRingCat.of Ω) ⟶ p.1.left := p.2.val
  have hb' : IsUnit ((v.appTop).hom a) := hb
  -- the geometric point lands in the basic open of `a`
  have hmem : v.base default ∈ p.1.left.basicOpen a := by
    have h1 : (Spec (CommRingCat.of Ω)).basicOpen ((v.appTop).hom a) = ⊤ :=
      RingedSpace.basicOpen_of_isUnit _ hb'
    have h2 := v.preimage_basicOpen_top a
    rw [h1] at h2
    show default ∈ v ⁻¹ᵁ p.1.left.basicOpen a
    rw [h2]
    trivial
  -- the basic open of `a`, as an étale neighbourhood refining `p`
  set O : p.1.left.Opens := p.1.left.basicOpen a with hO
  have hrange : Set.range v.base ⊆ Set.range O.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨t, rfl⟩
    rw [Unique.eq_default t]
    exact hmem
  let u' : Spec (CommRingCat.of Ω) ⟶ O := IsOpenImmersion.lift O.ι v hrange
  have hfac : u' ≫ O.ι = v := IsOpenImmersion.lift_fac O.ι v hrange
  let V : X.Etale := MorphismProperty.Over.mk _ (O.ι ≫ p.1.hom) inferInstance
  let elt : (geometricPoint x).fiber.obj V := geometricPoint.mkFiber x u' (by
    show u' ≫ O.ι ≫ p.1.hom = x
    rw [← Category.assoc, hfac]
    exact p.2.property)
  let pV : (geometricPoint x).fiber.Elements := ⟨V, elt⟩
  let g : pV ⟶ p :=
    ⟨MorphismProperty.Over.homMk O.ι rfl trivial, Subtype.ext (by
      show u' ≫ O.ι = v
      exact hfac)⟩
  -- the restriction of `a` to its basic open is invertible
  have hunit : IsUnit (((strictLocalizationDiagram x).map (op g)).hom a) := by
    have himg : O.ι ''ᵁ (⊤ : O.toScheme.Opens) = O := Scheme.Opens.ι_image_top O
    have hcomp : (homOfLE le_top : O.ι ''ᵁ (⊤ : O.toScheme.Opens) ⟶ ⊤) =
        eqToHom himg ≫ homOfLE le_top := Subsingleton.elim _ _
    show IsUnit ((p.1.left.presheaf.map
      (homOfLE (x := O.ι ''ᵁ (⊤ : O.toScheme.Opens)) le_top).op).hom a)
    rw [hcomp, op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (p.1.left.toRingedSpace.isUnit_res_basicOpen a).map _
  have h := congrArg (fun t => CommRingCat.Hom.hom t a) (toStrictLocalization_w x g)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [← h]
  exact hunit.map _

/-- An element of the strict localization is a unit if and only if its value at the
geometric point is nonzero. -/
theorem isUnit_iff_strictLocalizationEval_ne_zero (z : strictLocalization x) :
    IsUnit z ↔ (strictLocalizationEval x).hom z ≠ 0 := by
  constructor
  · intro hz h0
    have hu := hz.map (strictLocalizationEval x).hom
    rw [h0] at hu
    exact not_isUnit_zero hu
  · intro hz
    obtain ⟨p, a, rfl⟩ := exists_toStrictLocalization_eq x z
    apply isUnit_toStrictLocalization_of_isUnit
    have hcomp := congrArg (fun t => CommRingCat.Hom.hom t a)
      (toStrictLocalization_strictLocalizationEval x p)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hcomp
    rw [hcomp] at hz
    have h1 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
        ((Scheme.Γ.map p.2.val.op).hom a)) := isUnit_iff_ne_zero.mpr hz
    have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    have h3 : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.Γ.map p.2.val.op).hom a)) =
        (Scheme.Γ.map p.2.val.op).hom a := by
      have h4 := congrArg (fun t => CommRingCat.Hom.hom t ((Scheme.Γ.map p.2.val.op).hom a))
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom_inv_id
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h4
      exact h4
    rw [h3] at h2
    exact h2

instance : Nontrivial (strictLocalization x) :=
  (strictLocalizationEval x).hom.domain_nontrivial

/-- The strict localization at a geometric point is a local ring, the maximal ideal
being the functions vanishing at the point. -/
instance : IsLocalRing (strictLocalization x) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb ↦ ?_
  simp only [mem_nonunits_iff, isUnit_iff_strictLocalizationEval_ne_zero, not_not] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

/-- Evaluation at the geometric point is a local homomorphism. -/
instance : IsLocalHom (strictLocalizationEval x).hom :=
  ⟨fun z hz ↦ (isUnit_iff_strictLocalizationEval_ne_zero x z).mpr hz.ne_zero⟩

lemma mem_maximalIdeal_strictLocalization_iff (z : strictLocalization x) :
    z ∈ IsLocalRing.maximalIdeal (strictLocalization x) ↔
      (strictLocalizationEval x).hom z = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_strictLocalizationEval_ne_zero, not_not]

/-!
### Retractions of étale algebras over the strict localization

Every étale algebra `B` over the strict localization whose spectrum surjects onto the
spectrum of the strict localization admits a retraction: `B` descends to an étale
algebra over an affine étale neighbourhood, and evaluation at the geometric point
provides a section of the descended neighbourhood, i.e. a further étale neighbourhood
mapping to it, whose ring of functions receives `B`.
-/

section Retraction

/-- The affine étale neighbourhoods are initial among the étale neighbourhoods of a
geometric point (spelled with the fiber functor of `geometricPoint`). -/
instance initial_pre_affineEtaleSpec_geometricPoint :
    (CategoryOfElements.pre (AffineEtale.Spec X) (geometricPoint x).fiber).Initial :=
  inferInstanceAs (CategoryOfElements.pre (AffineEtale.Spec X)
    (Etale.forget X ⋙ ((geometricFiber Ω).over x).fiber)).Initial

/-- The category of affine étale neighbourhoods of a geometric point is cofiltered. -/
instance isCofiltered_elements_affineEtaleSpec_geometricPoint :
    IsCofiltered (AffineEtale.Spec X ⋙ (geometricPoint x).fiber).Elements :=
  IsCofiltered.of_initial_of_fullyFaithful
    (CategoryOfElements.pre (AffineEtale.Spec X) (geometricPoint x).fiber)

/-- Étale ring maps out of a filtered colimit over an essentially `u`-small shape
descend to a finite stage. -/
private lemma exists_isPushout_etale_of_essentiallySmall {J : Type*} [Category J]
    [EssentiallySmall.{u} J] [IsFiltered J] {D : J ⥤ CommRingCat.{u}} {c : Cocone D}
    (hc : IsColimit c) {T : CommRingCat.{u}} (f : c.pt ⟶ T)
    (hf : CommRingCat.etale f) :
    ∃ (j : J) (T' : CommRingCat.{u}) (f' : D.obj j ⟶ T') (g : T' ⟶ T),
      IsPushout (c.ι.app j) f' f g ∧ CommRingCat.etale f' := by
  let e := equivSmallModel.{u} J
  haveI : IsFiltered (SmallModel.{u} J) := IsFiltered.of_equivalence e
  obtain ⟨j', T', f', g, hpb, hf'⟩ := CommRingCat.etale.exists_isPushout_of_isFiltered
    ((Functor.Final.isColimitWhiskerEquiv e.inverse c).symm hc) f hf
  exact ⟨e.inverse.obj j', T', f', g, hpb, hf'⟩

/-- The top-level sections of the inverse of `isoSpec` are the inverse of `ΓSpecIso`. -/
private lemma isoSpec_inv_appTop (Y : Scheme.{u}) [IsAffine Y] :
    Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := by
  rw [← Iso.comp_hom_eq_id (Scheme.ΓSpecIso Γ(Y, ⊤)), ← Scheme.toSpecΓ_appTop,
    ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop]

/-- A morphism `Spec R ⟶ Y` to an affine scheme is recovered from the associated map on
global sections, postcomposed with any factorization through `Spec` of a ring `T'`. -/
private lemma specMap_comp_isoSpec_inv_eq {Y : Scheme.{u}} [IsAffine Y]
    {R T' : CommRingCat.{u}} (v : Spec R ⟶ Y)
    (f' : Scheme.Γ.obj (op Y) ⟶ T') (ψ : T' ⟶ R)
    (hψ : f' ≫ ψ = Scheme.Γ.map v.op ≫ (Scheme.ΓSpecIso R).hom) :
    Spec.map ψ ≫ Spec.map f' ≫ Y.isoSpec.inv = v := by
  rw [← Category.assoc, ← Spec.map_comp, hψ, Spec.map_comp, Scheme.Γ_map,
    Quiver.Hom.unop_op, SpecMap_ΓSpecIso_hom, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- An étale algebra over the strict localization descends to an étale ring map on the
functions of some affine étale neighbourhood of the geometric point. -/
private lemma exists_descent_etale (B : Type u) [CommRing B]
    [Algebra (strictLocalization x) B] (hB : Algebra.Etale (strictLocalization x) B) :
    ∃ (p : (geometricPoint x).fiber.Elements) (T' : CommRingCat.{u})
      (f' : Scheme.Γ.obj (op p.1.left) ⟶ T') (g : T' ⟶ CommRingCat.of B),
      IsAffine p.1.left ∧
      IsPushout (toStrictLocalization x p) f'
        (CommRingCat.ofHom (algebraMap (strictLocalization x) B)) g ∧
      CommRingCat.etale f' := by
  have hf : CommRingCat.etale (CommRingCat.ofHom (algebraMap (strictLocalization x) B)) := by
    rw [CommRingCat.etale_iff]
    exact RingHom.etale_algebraMap.mpr hB
  obtain ⟨j, T', f', g, hpb, hf'⟩ := exists_isPushout_etale_of_essentiallySmall
    ((Functor.Final.isColimitWhiskerEquiv (CategoryOfElements.pre (AffineEtale.Spec X)
        (geometricPoint x).fiber).op _).symm
      (colimit.isColimit (strictLocalizationDiagram x)))
    (CommRingCat.ofHom (algebraMap (strictLocalization x) B)) hf
  exact ⟨(CategoryOfElements.pre (AffineEtale.Spec X) (geometricPoint x).fiber).obj j.unop,
    T', f', g, inferInstanceAs (IsAffine (Spec (unop j.unop.1.left))), hpb, hf'⟩

/-- **Retractions of étale algebras over the strict localization.** An étale algebra `B`
over the strict localization at a geometric point which admits a prime over the maximal
ideal (e.g. because its spectrum surjects onto the spectrum of the strict localization)
admits a retraction of the algebra map. This is the section-through-the-closed-point
property of strictly henselian local rings (Stacks 04GG (8)). -/
theorem exists_retraction_of_etale_of_exists_prime (B : Type u) [CommRing B]
    [Algebra (strictLocalization x) B] (hB : Algebra.Etale (strictLocalization x) B)
    (hq : ∃ q : Ideal B, q.IsPrime ∧
      q.comap (algebraMap (strictLocalization x) B) =
        IsLocalRing.maximalIdeal (strictLocalization x)) :
    ∃ f : B →+* strictLocalization x,
      f.comp (algebraMap (strictLocalization x) B) = RingHom.id (strictLocalization x) := by
  letI : Algebra (strictLocalization x) Ω := (strictLocalizationEval x).hom.toAlgebra
  -- Step 1: evaluation at the geometric point extends to a character `χ : B →ₐ Ω`,
  -- because the maximal ideal of the strict localization lifts to `B`.
  have hker : RingHom.ker (algebraMap (strictLocalization x) Ω) =
      IsLocalRing.maximalIdeal (strictLocalization x) := by
    ext z
    rw [RingHom.mem_ker, mem_maximalIdeal_strictLocalization_iff]
    rfl
  obtain ⟨q, hqp, hqm⟩ := hq
  have hQ' : q.comap (algebraMap (strictLocalization x) B) =
      RingHom.ker (algebraMap (strictLocalization x) Ω) := by
    rw [hker]
    exact hqm
  obtain ⟨χ⟩ := Algebra.Etale.exists_algHom_to_isSepClosed B ⟨q, hqp, hQ'⟩
  -- Step 2: descend `B` to an étale ring map `f'` on an affine étale neighbourhood.
  obtain ⟨pE, T', f', g, haff, hpb, hf'⟩ := exists_descent_etale x B hB
  haveI : IsAffine pE.1.left := haff
  haveI : Etale pE.1.hom := pE.1.prop
  haveI : Etale (Spec.map f') :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr ((CommRingCat.etale_iff f').mp hf')
  -- Step 3: `χ` provides a lift of the geometric point to `Spec T'`.
  set ψ : T' ⟶ CommRingCat.of Ω := g ≫ CommRingCat.ofHom χ.toRingHom with hψdef
  have h1 : CommRingCat.ofHom (algebraMap (strictLocalization x) B) ≫
      CommRingCat.ofHom χ.toRingHom = strictLocalizationEval x := by
    ext1
    exact χ.comp_algebraMap
  have hring : f' ≫ ψ =
      Scheme.Γ.map pE.2.val.op ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom := by
    rw [← toStrictLocalization_strictLocalizationEval x pE, hψdef, ← Category.assoc,
      ← hpb.w, Category.assoc, h1]
  have hkey : Spec.map ψ ≫ Spec.map f' ≫ pE.1.left.isoSpec.inv = pE.2.val :=
    specMap_comp_isoSpec_inv_eq (Y := pE.1.left) pE.2.val f' ψ hring
  -- Step 4: `Spec T'` is an étale neighbourhood of the geometric point refining `pE`.
  haveI : Etale ((Spec.map f' ≫ pE.1.left.isoSpec.inv) ≫ pE.1.hom) := by
    haveI : Etale (Spec.map f' ≫ pE.1.left.isoSpec.inv) := inferInstance
    infer_instance
  let V : X.Etale :=
    MorphismProperty.Over.mk _ ((Spec.map f' ≫ pE.1.left.isoSpec.inv) ≫ pE.1.hom)
      inferInstance
  have hVx : Spec.map ψ ≫ (Spec.map f' ≫ pE.1.left.isoSpec.inv) ≫ pE.1.hom = x := by
    rw [← Category.assoc, hkey]
    exact pE.2.property
  let eltW : (geometricPoint x).fiber.obj V := geometricPoint.mkFiber x (Spec.map ψ) hVx
  let pW : (geometricPoint x).fiber.Elements := ⟨V, eltW⟩
  let gW : pW ⟶ pE :=
    ⟨MorphismProperty.Over.homMk (Spec.map f' ≫ pE.1.left.isoSpec.inv) rfl trivial,
      Subtype.ext (by exact hkey)⟩
  -- Step 5: the germ map of the refined neighbourhood retracts `f'`, hence `B`.
  have hmap : (strictLocalizationDiagram x).map (op gW) =
      f' ≫ (Scheme.ΓSpecIso T').inv := by
    change (Spec.map f' ≫ pE.1.left.isoSpec.inv).appTop = f' ≫ (Scheme.ΓSpecIso T').inv
    rw [Scheme.Hom.comp_appTop, isoSpec_inv_appTop, Scheme.ΓSpecIso_inv_naturality]
    rfl
  have htri : toStrictLocalization x pE ≫ 𝟙 (strictLocalization x) =
      f' ≫ (Scheme.ΓSpecIso T').inv ≫ toStrictLocalization x pW := by
    rw [Category.comp_id, ← toStrictLocalization_w x gW, hmap, Category.assoc]
  refine ⟨(hpb.desc (𝟙 (strictLocalization x))
    ((Scheme.ΓSpecIso T').inv ≫ toStrictLocalization x pW) htri).hom, ?_⟩
  have hcomp := hpb.inl_desc (𝟙 (strictLocalization x))
    ((Scheme.ΓSpecIso T').inv ≫ toStrictLocalization x pW) htri
  have h2 := congrArg CommRingCat.Hom.hom hcomp
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_id] at h2
  exact h2

/-- Specialization of `exists_retraction_of_etale_of_exists_prime` to étale algebras
with surjective spectrum map, as consumed by the retraction criterion for strictly
henselian local rings. -/
theorem exists_retraction_of_etale (B : Type u) [CommRing B]
    [Algebra (strictLocalization x) B] (hB : Algebra.Etale (strictLocalization x) B)
    (hsurj : Function.Surjective
      (PrimeSpectrum.comap (algebraMap (strictLocalization x) B))) :
    ∃ f : B →+* strictLocalization x,
      f.comp (algebraMap (strictLocalization x) B) = RingHom.id (strictLocalization x) := by
  obtain ⟨Q, hQ⟩ := hsurj (IsLocalRing.closedPoint (strictLocalization x))
  exact exists_retraction_of_etale_of_exists_prime x B hB
    ⟨Q.asIdeal, Q.isPrime, congrArg PrimeSpectrum.asIdeal hQ⟩

/-- **The strict localization of a scheme at a geometric point is strictly henselian**:
it is a henselian local ring with separably closed residue field. -/
instance isStrictlyHenselianLocalRing_strictLocalization :
    IsStrictlyHenselianLocalRing (strictLocalization x) := by
  haveI h := IsStrictlyHenselianLocalRing.localization_atPrime_of_forall_retraction
    (fun B _ _ hB hsurj ↦ exists_retraction_of_etale x B hB hsurj)
    (IsLocalRing.maximalIdeal (strictLocalization x))
  have e : (strictLocalization x : Type u) ≃ₐ[strictLocalization x]
      Localization.AtPrime (IsLocalRing.maximalIdeal (strictLocalization x)) :=
    IsLocalization.atUnits (strictLocalization x)
      (IsLocalRing.maximalIdeal (strictLocalization x)).primeCompl
      (fun y (hy : y ∉ IsLocalRing.maximalIdeal (strictLocalization x)) ↦ by
        by_contra hn
        exact hy ((IsLocalRing.mem_maximalIdeal y).mpr (mem_nonunits_iff.mpr hn)))
  exact .of_ringEquiv e.toRingEquiv.symm

end Retraction

end AlgebraicGeometry.Scheme.Etale
