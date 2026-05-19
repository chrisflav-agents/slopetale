/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Proetale.Algebra.FaithfullyFlat
import Proetale.Algebra.Ind
import Proetale.Algebra.StalkIso
import Proetale.Mathlib.Algebra.Algebra.Pi
import Proetale.Mathlib.Algebra.Category.CommAlgCat.Limits
import Proetale.Mathlib.Algebra.LocalIso.Spreads
import Proetale.Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Ind-Zariski algebras and ring homomorphisms

In this file we define ind-Zariski algebras.
-/
universe u

open CategoryTheory Limits

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]

section Algebra

variable [Algebra R S] [Algebra R T]

/-- The object property on commutative `R`-algebras of being a local isomorphism. -/
def CommAlgCat.isLocalIso : ObjectProperty (CommAlgCat.{u} R) :=
  fun S ↦ Algebra.IsLocalIso R S

lemma CommAlgCat.isLocalIso_eq : isLocalIso R = RingHom.toObjectProperty RingHom.IsLocalIso R := by
  ext S
  exact RingHom.isLocalIso_algebraMap.symm

instance : (CommAlgCat.isLocalIso R).IsClosedUnderIsomorphisms := by
  rw [CommAlgCat.isLocalIso_eq]
  exact RingHom.IsLocalIso.respectsIso.isClosedUnderIsomorphisms_toObjectProperty R

instance : (CommAlgCat.isLocalIso R).IsClosedUnderFiniteProducts :=
  .of_isClosedUnderLimitsOfShape_discrete fun ι ↦ by
    intro
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro X ⟨F, hF⟩
    let S : ι → CommAlgCat.{u} R := fun i ↦ F.obj ⟨i⟩
    let natIso : F ≅ Discrete.functor S := Discrete.natIso (fun i ↦ Iso.refl _)
    let isoPi : (CommAlgCat.piFan S).pt ≅ limit (Discrete.functor S) :=
      (limit.isoLimitCone ⟨CommAlgCat.piFan S, CommAlgCat.isLimitPiFan S⟩).symm
    let isoLim : limit (Discrete.functor S) ≅ limit F :=
      (HasLimit.isoOfNatIso natIso).symm
    apply (CommAlgCat.isLocalIso R).prop_of_iso (isoPi ≪≫ isoLim)
    have inst (i : ι) : Algebra.IsLocalIso R (S i) := hF ⟨i⟩
    exact Algebra.IsLocalIso.pi_of_finite R (fun i ↦ S i)

/-- A local isomorphism of `R`-algebras is finitely presented. -/
lemma Algebra.IsLocalIso.finitePresentation [Algebra.IsLocalIso R S] :
    (algebraMap R S).FinitePresentation := by
  apply RingHom.finitePresentation_ofLocalizationSpanTarget
    (algebraMap R S) _ (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top R S)
  rintro ⟨g, hg⟩
  rw [show (algebraMap S (Localization.Away g)).comp (algebraMap R S) =
       algebraMap R (Localization.Away g) from
    (IsScalarTower.algebraMap_eq R S (Localization.Away g)).symm,
    RingHom.finitePresentation_algebraMap]
  obtain ⟨r, hr⟩ := hg.exists_away
  exact IsLocalization.Away.finitePresentation r

/-- Local isomorphisms are finitely presentable in `CommAlgCat R`. -/
lemma CommAlgCat.isLocalIso_le_isFinitelyPresentable :
    CommAlgCat.isLocalIso R ≤
      ObjectProperty.isFinitelyPresentable.{u} (CommAlgCat.{u} R) := by
  intro S hS
  haveI : Algebra.IsLocalIso R S := hS
  have hfp : (algebraMap R S).FinitePresentation :=
    Algebra.IsLocalIso.finitePresentation R S
  have hunder : IsFinitelyPresentable.{u}
      ((commAlgCatEquivUnder (.of R)).functor.obj S) :=
    CommRingCat.isFinitelyPresentable_under _ _ (by convert hfp using 1)
  haveI : Fact (Cardinal.aleph0 : Cardinal.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  exact (@isCardinalPresentable_iff_of_isEquivalence
    (CommAlgCat.{u} R) _ S (Cardinal.aleph0 : Cardinal.{u}) this
    (Under (CommRingCat.of.{u} R)) _
    (commAlgCatEquivUnder (.of R)).functor inferInstance).mp hunder

/-- An algebra is ind-Zariski if it can be written as the filtered colimit of locally isomorphic
algebras. -/
@[stacks 096N, mk_iff]
class Algebra.IndZariski (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  exists_colimitPresentation : ∃ (ι : Type u) (_ : SmallCategory ι) (_ : IsFiltered ι)
    (P : ColimitPresentation ι (CommAlgCat.of R S)),
    ∀ (i : ι), Algebra.IsLocalIso R (P.diag.obj i)

namespace Algebra.IndZariski

lemma iff_ind_isLocalIso :
    Algebra.IndZariski R S ↔ ObjectProperty.ind.{u} (CommAlgCat.isLocalIso R) (.of R S) :=
  Algebra.indZariski_iff R S

lemma of_equiv (e : S ≃ₐ[R] T) [IndZariski R S] : IndZariski R T := by
  rwa [iff_ind_isLocalIso, (CommAlgCat.isLocalIso R).ind.prop_iff_of_iso (CommAlgCat.isoMk e.symm),
    ← iff_ind_isLocalIso]

/-- If `R → S` is ind-Zariski and `S → A` is a local isomorphism, then `R → A` is
ind-Zariski. This is the key technical step for `trans`. Mirrors
`Algebra.IndEtale.of_indEtale_etale`, but uses `PreIndSpreads` for
`(RingHom.toMorphismProperty RingHom.IsLocalIso)` (from
`Proetale.Mathlib.Algebra.LocalIso.Spreads`). -/
private lemma of_indZariski_localIso (A : Type u) [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Algebra.IndZariski R S] [Algebra.IsLocalIso S A] :
    Algebra.IndZariski R A := by
  rw [iff_ind_isLocalIso, CommAlgCat.isLocalIso_eq,
    ← RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty]
  -- Morphism-level colimit presentation of R → S with local-iso stages.
  have hRS : MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso)
      (CommRingCat.ofHom (algebraMap R S)) := by
    have h : Algebra.IndZariski R S := inferInstance
    rwa [iff_ind_isLocalIso, CommAlgCat.isLocalIso_eq,
      ← RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty] at h
  obtain ⟨J, _, _, D, sR, tS, htS, hRS_data⟩ := hRS
  -- S → A is a local iso.
  have hSA : (RingHom.toMorphismProperty RingHom.IsLocalIso)
      (CommRingCat.ofHom (algebraMap S A)) :=
    RingHom.isLocalIso_algebraMap.mpr inferInstance
  -- Apply PreIndSpreads to descend S → A to some finite stage j₀ via a pushout square.
  obtain ⟨j₀, T', f', g, hpush, hf'⟩ :=
    MorphismProperty.PreIndSpreads.exists_isPushout
      (P := RingHom.toMorphismProperty RingHom.IsLocalIso) htS
      (CommRingCat.ofHom (algebraMap S A)) hSA
  -- Build the refined diagram D' : Under j₀ → CommRingCat whose colimit is A.
  let D' : Under j₀ ⥤ CommRingCat.{u} :=
    (Under.post D ⋙ Under.pushout f') ⋙ Under.forget _
  let c'₀ : Cocone D' :=
    (Under.pushout f' ⋙ Under.forget _).mapCocone ((Cocone.mk _ tS).underPost j₀)
  let c' : Cocone D' := c'₀.extend hpush.isoPushout.inv
  let hc' : IsColimit c' :=
    IsColimit.extendIso _ (isColimitOfPreserves _ (htS.underPost j₀))
  -- Natural transformation R → D'.
  let s' : (Functor.const (Under j₀)).obj (CommRingCat.of R) ⟶ D' :=
    { app := fun k => sR.app k.right ≫ pushout.inl (D.map k.hom) f'
      naturality := fun k l a => by
        have hnat := sR.naturality a.right
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hnat
        show 𝟙 _ ≫ sR.app l.right ≫ pushout.inl (D.map l.hom) f' =
          (sR.app k.right ≫ pushout.inl (D.map k.hom) f') ≫ _
        rw [Category.id_comp, Category.assoc]
        dsimp [D', Under.post, Under.pushout]
        rw [pushout.inl_desc, ← Category.assoc, ← hnat] }
  refine ⟨Under j₀, inferInstance, inferInstance, D', s', c'.ι, hc', fun k => ⟨?_, ?_⟩⟩
  · -- s'.app k is a local iso: composition of a local-iso stage with the local-iso pushout.inl.
    have h1 : (RingHom.toMorphismProperty RingHom.IsLocalIso) (sR.app k.right) :=
      (hRS_data k.right).1
    have h2 : (RingHom.toMorphismProperty RingHom.IsLocalIso)
        (pushout.inl (D.map k.hom) f') :=
      (RingHom.toMorphismProperty RingHom.IsLocalIso).pushout_inl _ _ hf'
    exact (RingHom.toMorphismProperty RingHom.IsLocalIso).comp_mem _ _ h1 h2
  · -- s'.app k ≫ c'.ι.app k = ofHom (algebraMap R A).
    have hassoc : sR.app k.right ≫ tS.app k.right = CommRingCat.ofHom (algebraMap R S) :=
      (hRS_data k.right).2
    show (sR.app k.right ≫ pushout.inl (D.map k.hom) f') ≫ c'.ι.app k =
      CommRingCat.ofHom (algebraMap R A)
    have hkey : pushout.inl (D.map k.hom) f' ≫ c'₀.ι.app k =
        tS.app k.right ≫ pushout.inl ((Cocone.mk (CommRingCat.of S) tS).ι.app j₀) f' := by
      dsimp only [c'₀, Functor.mapCocone_ι_app, Cocone.underPost_ι_app, Functor.comp_map,
        Under.forget_map, Under.pushout_map, Under.post_obj, Under.mk_hom, Under.homMk_right,
        Cocone.underPost_pt]
      exact pushout.inl_desc _ _ _
    -- Express c'.ι.app k as c'₀.ι.app k ≫ hpush.isoPushout.inv.
    have hc'_def : c'.ι.app k = c'₀.ι.app k ≫ hpush.isoPushout.inv := rfl
    -- Get reassociated form of hkey.
    have hkey' : pushout.inl (D.map k.hom) f' ≫ c'₀.ι.app k ≫ hpush.isoPushout.inv =
        tS.app k.right ≫
          pushout.inl ((Cocone.mk (CommRingCat.of S) tS).ι.app j₀) f' ≫
            hpush.isoPushout.inv := by
      have := congrArg (· ≫ hpush.isoPushout.inv) hkey
      simp only [Category.assoc] at this
      exact this
    -- pushout.inl ≫ c'.ι.app k = tS.app ≫ algebraMap S A.
    have hcomp : pushout.inl (D.map k.hom) f' ≫ c'.ι.app k =
        tS.app k.right ≫ CommRingCat.ofHom (algebraMap S A) := by
      rw [hc'_def]
      have hinl_inv := hpush.inl_isoPushout_inv
      calc pushout.inl (D.map k.hom) f' ≫ c'₀.ι.app k ≫ hpush.isoPushout.inv
          = tS.app k.right ≫
              pushout.inl ((Cocone.mk (CommRingCat.of S) tS).ι.app j₀) f' ≫
                hpush.isoPushout.inv := hkey'
        _ = tS.app k.right ≫ CommRingCat.ofHom (algebraMap S A) :=
            congrArg (tS.app k.right ≫ ·) hinl_inv
    -- Combine using term-mode equalities.
    have step1 : (sR.app k.right ≫ pushout.inl (D.map k.hom) f') ≫ c'.ι.app k =
        sR.app k.right ≫ pushout.inl (D.map k.hom) f' ≫ c'.ι.app k := Category.assoc _ _ _
    have step2 : sR.app k.right ≫ pushout.inl (D.map k.hom) f' ≫ c'.ι.app k =
        sR.app k.right ≫ tS.app k.right ≫ CommRingCat.ofHom (algebraMap S A) :=
      congrArg (sR.app k.right ≫ ·) hcomp
    have step3 : sR.app k.right ≫ tS.app k.right ≫ CommRingCat.ofHom (algebraMap S A) =
        (sR.app k.right ≫ tS.app k.right) ≫ CommRingCat.ofHom (algebraMap S A) :=
      (Category.assoc _ _ _).symm
    have step4 : (sR.app k.right ≫ tS.app k.right) ≫ CommRingCat.ofHom (algebraMap S A) =
        CommRingCat.ofHom (algebraMap R S) ≫ CommRingCat.ofHom (algebraMap S A) :=
      congrArg (· ≫ CommRingCat.ofHom (algebraMap S A)) hassoc
    have step5 : CommRingCat.ofHom (algebraMap R S) ≫ CommRingCat.ofHom (algebraMap S A) =
        CommRingCat.ofHom (algebraMap R A) := by
      ext x
      exact (IsScalarTower.algebraMap_apply R S A x).symm
    exact step1.trans (step2.trans (step3.trans (step4.trans step5)))

/-- Transitivity of ind-Zariski algebras. The proof mirrors `Algebra.IndEtale.trans`,
using the `PreIndSpreads` instance for `RingHom.toMorphismProperty RingHom.IsLocalIso`
provided in `Proetale.Mathlib.Algebra.LocalIso.Spreads`. -/
lemma trans [Algebra S T] [IsScalarTower R S T] [Algebra.IndZariski R S] [Algebra.IndZariski S T] :
    Algebra.IndZariski R T := by
  -- Convert IndZariski R T goal to MorphismProperty.ind form.
  suffices MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso)
      (CommRingCat.ofHom (algebraMap R T)) by
    rw [iff_ind_isLocalIso, CommAlgCat.isLocalIso_eq,
      ← RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty]
    exact this
  -- Convert IndZariski S T to MorphismProperty.ind form.
  have hST : MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso)
      (CommRingCat.ofHom (algebraMap S T)) := by
    have : Algebra.IndZariski S T := inferInstance
    rwa [iff_ind_isLocalIso S, CommAlgCat.isLocalIso_eq,
      ← RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty] at this
  obtain ⟨J, hJ, hFilt, D, s₂, t₂, ht₂, hst₂⟩ := hST
  -- For each j, R → D_j is ind(IsLocalIso) by of_indZariski_localIso.
  have hIndZariski_j : ∀ j, MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IsLocalIso)
      (CommRingCat.ofHom (algebraMap R S) ≫ s₂.app j) := by
    intro j
    have hLocalIso_j : (s₂.app j).hom.IsLocalIso := (hst₂ j).1
    letI : Algebra S (D.obj j) := (s₂.app j).hom.toAlgebra
    letI : Algebra R (D.obj j) :=
      ((CommRingCat.ofHom (algebraMap R S) ≫ s₂.app j).hom).toAlgebra
    haveI : IsScalarTower R S (D.obj j) := .of_algebraMap_eq' rfl
    haveI : Algebra.IsLocalIso S (D.obj j) := RingHom.isLocalIso_algebraMap.mp hLocalIso_j
    have := of_indZariski_localIso R S (D.obj j)
    rwa [iff_ind_isLocalIso, CommAlgCat.isLocalIso_eq,
      ← RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty] at this
  -- R → T is ind(ind(IsLocalIso)): T = colim D_j with each R → D_j ind(IsLocalIso).
  have hind_ind : MorphismProperty.ind.{u}
        (MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso))
      (CommRingCat.ofHom (algebraMap R T)) :=
    ⟨J, hJ, hFilt, D,
      (Functor.const J).map (CommRingCat.ofHom (algebraMap R S)) ≫ s₂,
      t₂, ht₂, fun j => ⟨hIndZariski_j j, by
        show ((Functor.const J).map (CommRingCat.ofHom (algebraMap R S)) ≫ s₂).app j ≫ t₂.app j =
          CommRingCat.ofHom (algebraMap R T)
        simp only [NatTrans.comp_app, Functor.const_obj_obj, Functor.const_map_app, Category.assoc]
        ext x
        show (t₂.app j).hom ((s₂.app j).hom ((algebraMap R S) x)) = (algebraMap R T) x
        have h := RingHom.congr_fun (CommRingCat.hom_ext_iff.mp (hst₂ j).2) ((algebraMap R S) x)
        simp only [CommRingCat.comp_apply] at h
        rw [h]; exact (IsScalarTower.algebraMap_apply R S T x).symm⟩⟩
  -- By ind_ind: ind(ind(IsLocalIso)) = ind(IsLocalIso).
  have key : MorphismProperty.ind.{u}
        (MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso)) =
      MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso) :=
    MorphismProperty.ind_ind (P := RingHom.toMorphismProperty RingHom.IsLocalIso)
      (fun X Y f hf => by
        algebraize [f.hom]
        have : Algebra.IsLocalIso X Y := hf
        exact CommRingCat.isFinitelyPresentable_under _ _
          (Algebra.IsLocalIso.finitePresentation X Y))
  rw [key] at hind_ind
  exact hind_ind

instance pi {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, Algebra.IndZariski R (S i)] : Algebra.IndZariski R (∀ i, S i) := by
  rw [iff_ind_isLocalIso]
  apply ObjectProperty.LimitOfShape.prop (J := Discrete ι)
  refine ⟨⟨Discrete.functor fun i ↦ .of R (S i),
      Discrete.natTrans fun i ↦ CommAlgCat.ofHom (Pi.evalAlgHom _ _ _), ?_⟩, ?_⟩
  · exact CommAlgCat.isLimitPiFan fun i ↦ .of R (S i)
  · intro j
    dsimp
    rw [← iff_ind_isLocalIso]
    infer_instance

/-- The product of two ind-Zariski algebras is ind-Zariski. -/
instance prod [Algebra.IndZariski R S] [Algebra.IndZariski R T] :
    Algebra.IndZariski R (S × T) := by
  let F : ULift.{u} (Fin 2) → Type u := fun | ⟨0⟩ => S | ⟨1⟩ => T
  letI : ∀ i, CommRing (F i) := fun | ⟨0⟩ => ‹_› | ⟨1⟩ => ‹_›
  letI : ∀ i, Algebra R (F i) := fun | ⟨0⟩ => ‹_› | ⟨1⟩ => ‹_›
  haveI : ∀ i, IndZariski R (F i) := fun | ⟨0⟩ => ‹_› | ⟨1⟩ => ‹_›
  have := pi R F
  let e : (∀ i, F i) ≃ₐ[R] S × T :=
    { toFun := fun f ↦ (f ⟨0⟩, f ⟨1⟩)
      invFun := fun p ↦ fun | ⟨0⟩ => p.1 | ⟨1⟩ => p.2
      left_inv := fun f ↦ by ext ⟨i⟩; fin_cases i <;> rfl
      right_inv := fun ⟨_, _⟩ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  exact Algebra.IndZariski.of_equiv (R := R) (S := ∀ i, F i) (T := S × T) e

instance function {ι : Type u} [_root_.Finite ι] (S : Type u) [CommRing S]
    [Algebra R S] [Algebra.IndZariski R S] : Algebra.IndZariski R (ι → S) :=
  pi R (fun _ ↦ S)

variable {R}

instance (priority := 100) of_isLocalIso [Algebra.IsLocalIso R S] : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso]
  exact ObjectProperty.le_ind _ _ ‹_›

instance refl : Algebra.IndZariski R R :=
  Algebra.IndZariski.of_isLocalIso _

/-- The index category for the colimit presentation `M⁻¹R = colim_{m ∈ M} R[1/m]`:
a wrapper around the submonoid `M`, equipped with the divisibility preorder. -/
@[ext]
structure AwayIndex {R : Type u} [CommRing R] (M : Submonoid R) where
  /-- The underlying element of the submonoid. -/
  val : R
  /-- The element belongs to `M`. -/
  property : val ∈ M

namespace AwayIndex

variable {R : Type u} [CommRing R] {M : Submonoid R}

instance : Preorder (AwayIndex M) where
  le m m' := m.val ∣ m'.val
  le_refl _ := dvd_refl _
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂

instance : IsDirected (AwayIndex M) (· ≤ ·) :=
  ⟨fun m m' => ⟨⟨m.val * m'.val, M.mul_mem m.2 m'.2⟩,
    ⟨m'.val, rfl⟩, ⟨m.val, mul_comm _ _⟩⟩⟩

instance : Nonempty (AwayIndex M) := ⟨⟨1, M.one_mem⟩⟩

lemma le_def {m m' : AwayIndex M} : m ≤ m' ↔ m.val ∣ m'.val := Iff.rfl

end AwayIndex

/-- The transition map `Localization.Away m → Localization.Away m'` when `m ∣ m'`,
viewed as an `R`-algebra homomorphism. -/
noncomputable def awayDvdHom (R : Type u) [CommRing R] {m m' : R} (h : m ∣ m')
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsLocalization.Away m A] [IsLocalization.Away m' B] : A →ₐ[R] B :=
  { IsLocalization.Away.lift (S := A) m
      (g := algebraMap R B) (IsLocalization.Away.isUnit_of_dvd m' h) with
    commutes' := fun _ => IsLocalization.Away.lift_eq _ _ _ }

/-- The diagram functor `AwayIndex M ⥤ CommAlgCat R` sending `m ↦ Localization.Away m`. -/
noncomputable def awayDiag (R : Type u) [CommRing R] (M : Submonoid R) :
    AwayIndex M ⥤ CommAlgCat.{u} R where
  obj m := CommAlgCat.of R (Localization.Away m.val)
  map {m m'} h := CommAlgCat.ofHom (awayDvdHom R (m := m.val) (m' := m'.val) h.le)
  map_id m := by
    refine CommAlgCat.hom_ext (AlgHom.coe_ringHom_injective ?_)
    ext x
    obtain ⟨a, n, rfl⟩ := IsLocalization.mk'_surjective (.powers m.val) x
    simp [awayDvdHom, IsLocalization.Away.lift]
  map_comp {m₁ _ _} _ _ := by
    refine CommAlgCat.hom_ext (AlgHom.coe_ringHom_injective ?_)
    refine IsLocalization.ringHom_ext (.powers m₁.val) ?_
    ext _
    simp [awayDvdHom, IsLocalization.Away.lift]

/-- Helper: the carrier of `(awayDiag R M).obj m` is by definition
`Localization.Away m.val`, so it carries the corresponding localization instance. -/
instance awayDiag_obj_isLocalization (R : Type u) [CommRing R] (M : Submonoid R)
    (m : AwayIndex M) :
    IsLocalization (Submonoid.powers m.val) ((awayDiag R M).obj m : Type u) :=
  inferInstanceAs (IsLocalization (.powers m.val) (Localization.Away m.val))

/-- Helper: the carrier of `(awayDiag R M).obj m` is the standard localization away
from `m.val`. -/
instance awayDiag_obj_isLocalizationAway (R : Type u) [CommRing R] (M : Submonoid R)
    (m : AwayIndex M) :
    IsLocalization.Away m.val ((awayDiag R M).obj m : Type u) :=
  inferInstanceAs (IsLocalization.Away m.val (Localization.Away m.val))

/-- For each `m ∈ M`, the canonical map `Localization.Away m → S` induced by
the universal property of localization, viewed as an `R`-algebra homomorphism. -/
noncomputable def awayToLocalization (R : Type u) [CommRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] (m : AwayIndex M) :
    Localization.Away m.val →ₐ[R] S :=
  { IsLocalization.Away.lift (S := Localization.Away m.val) m.val
      (g := algebraMap R S)
      (IsLocalization.map_units S ⟨m.val, m.property⟩) with
    commutes' := fun _ => IsLocalization.Away.lift_eq _ _ _ }

/-- The cocone over the diagram `awayDiag M` with apex `S`. -/
noncomputable def awayCocone (R : Type u) [CommRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] :
    (awayDiag R M) ⟶ (Functor.const (AwayIndex M)).obj (CommAlgCat.of R S) where
  app m := CommAlgCat.ofHom (awayToLocalization R M S m)
  naturality {m m'} _ := by
    refine CommAlgCat.hom_ext ?_
    haveI : Subsingleton (((awayDiag R M).obj m : Type u) →ₐ[R]
        (((Functor.const (AwayIndex M)).obj (CommAlgCat.of R S)).obj m' : Type u)) :=
      IsLocalization.algHom_subsingleton (Submonoid.powers m.val)
    exact Subsingleton.elim _ _

/-- A localization of `R` at a submonoid `M` is the filtered colimit of `R[1/m]`
over `m ∈ M`, in the category of `R`-algebras. -/
noncomputable def awayColimitPresentation (R : Type u) [CommRing R] (M : Submonoid R)
    (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S] :
    ColimitPresentation (AwayIndex M) (CommAlgCat.of R S) where
  diag := awayDiag R M
  ι := awayCocone R M S
  isColimit := by
    refine ⟨?desc, ?fac, ?uniq⟩
    case desc =>
      intro c
      refine CommAlgCat.ofHom (IsLocalization.liftAlgHom (M := M)
        (f := Algebra.ofId R c.pt) ?_)
      intro y
      have hy : IsUnit (algebraMap R (Localization.Away y.val) y.val) :=
        IsLocalization.Away.algebraMap_isUnit y.val
      have key : (c.ι.app ⟨y.val, y.2⟩).hom
          (algebraMap R (Localization.Away y.val) y.val) = algebraMap R c.pt y.val :=
        (c.ι.app ⟨y.val, y.2⟩).hom.commutes y.val
      show IsUnit ((Algebra.ofId R c.pt) (y : R))
      rw [Algebra.ofId_apply, ← key]
      exact hy.map (c.ι.app ⟨y.val, y.2⟩).hom
    case fac =>
      intro c m
      refine CommAlgCat.hom_ext ?_
      haveI : Subsingleton
          (((awayDiag R M).obj m : Type u) →ₐ[R] (c.pt : Type u)) :=
        IsLocalization.algHom_subsingleton (Submonoid.powers m.val)
      exact Subsingleton.elim _ _
    case uniq =>
      intro c _ _
      refine CommAlgCat.hom_ext ?_
      haveI : Subsingleton (S →ₐ[R] (c.pt : Type u)) :=
        IsLocalization.algHom_subsingleton M
      exact Subsingleton.elim _ _

lemma of_isLocalization (M : Submonoid R) [IsLocalization M S] : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso]
  refine ⟨AwayIndex M, inferInstance, inferInstance,
    awayColimitPresentation R M S, fun m => ?_⟩
  show Algebra.IsLocalIso R (Localization.Away m.val)
  infer_instance

instance localization (M : Submonoid R) : Algebra.IndZariski R (Localization M) :=
  of_isLocalization _ M

variable (R)

instance (priority := 100) _root_.Module.Flat.of_indZariski [Algebra.IndZariski R S] :
    Module.Flat R S := by
  rw [Module.Flat.iff_ind_flat]
  obtain ⟨J, _, _, pres, h⟩ := (Algebra.IndZariski.iff_ind_isLocalIso R S).mp ‹_›
  refine ⟨J, inferInstance, inferInstance, pres, fun i ↦ ?_⟩
  rw [CommAlgCat.flat_iff]
  exact @Algebra.IsLocalIso.flat _ _ _ _ _ (h i)

/-- Helper: if `S` is a filtered colimit of `R`-algebras `Aᵢ` and each algebra map
`R → Aᵢ` is bijective on stalks, then so is `R → S`. -/
lemma bijectiveOnStalks_of_colimitPresentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ i, (algebraMap R (P.diag.obj i)).BijectiveOnStalks) :
    (algebraMap R S).BijectiveOnStalks := by
  -- Underlying type-level colimit cocone.
  have hcolim : IsColimit ((forget (CommAlgCat.{u} R)).mapCocone P.cocone) :=
    isColimitOfPreserves (forget (CommAlgCat.{u} R)) P.isColimit
  -- The cocone leg, applied as a function, commutes with algebra maps from `R`.
  have hcomm : ∀ (i : ι) (r : R),
      (P.ι.app i).hom (algebraMap R (P.diag.obj i) r) = algebraMap R S r :=
    fun i r => (P.ι.app i).hom.commutes r
  -- Compatibility of the cocone legs under the diagram maps.
  have hnat : ∀ {i j : ι} (f : i ⟶ j) (x : P.diag.obj i),
      (P.ι.app j).hom ((P.diag.map f).hom x) = (P.ι.app i).hom x := by
    intro i j f x
    have hw : P.diag.map f ≫ P.ι.app j = P.ι.app i := P.w f
    show (P.diag.map f ≫ P.ι.app j).hom x = (P.ι.app i).hom x
    rw [hw]
    rfl
  intro p hp
  -- At each stage `i`, the pulled-back prime of `p` along the cocone leg.
  have hp_i_prime : ∀ (i : ι), (p.comap (P.ι.app i).hom.toRingHom).IsPrime :=
    fun i => Ideal.IsPrime.comap _
  -- `p.comap (algebraMap R S) = (p.comap (P.ι.app i).hom.toRingHom).comap (algebraMap R _)`.
  have hq_eq : ∀ (i : ι),
      p.comap (algebraMap R S) =
        (p.comap (P.ι.app i).hom.toRingHom).comap (algebraMap R (P.diag.obj i)) := by
    intro i
    ext r
    simp only [Ideal.mem_comap]
    rw [← hcomm i r]
    rfl
  refine ⟨?_, ?_⟩
  · -- INJECTIVITY of `Localization.localRingHom (p.comap (algebraMap R S)) p (algebraMap R S) rfl`.
    intro x y hxy
    obtain ⟨⟨r₁, s₁, hs₁⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (p.comap (algebraMap R S)).primeCompl x
    obtain ⟨⟨r₂, s₂, hs₂⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (p.comap (algebraMap R S)).primeCompl y
    rw [Localization.localRingHom_mk', Localization.localRingHom_mk'] at hxy
    -- Extract witness `c ∉ p` from the equality in `S_p`.
    obtain ⟨⟨c, hcp⟩, hc⟩ := (IsLocalization.eq (S := Localization.AtPrime p)).mp hxy
    simp only at hc
    -- Lift `c` to some stage `i₀`.
    obtain ⟨i₀, c', hc'⟩ : ∃ (i₀ : ι) (c' : ↑(P.diag.obj i₀)), (P.ι.app i₀).hom c' = c :=
      Types.jointly_surjective_of_isColimit hcolim c
    -- The equation translates to an equation in `S` after applying `(P.ι.app i₀).hom`.
    have hkey :
        (P.ι.app i₀).hom (c' * (algebraMap R (P.diag.obj i₀) s₂ *
            algebraMap R (P.diag.obj i₀) r₁)) =
        (P.ι.app i₀).hom (c' * (algebraMap R (P.diag.obj i₀) s₁ *
            algebraMap R (P.diag.obj i₀) r₂)) := by
      simp only [map_mul, hcomm i₀, hc']
      exact hc
    -- Use filtered colimit equality to lift to a stage `j` where the equation holds.
    obtain ⟨j, fij, hjeq⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hcolim _ _).mp hkey
    -- At stage `j`.
    let cj : ↑(P.diag.obj j) := (P.diag.map fij).hom c'
    let pj : Ideal (P.diag.obj j) := p.comap (P.ι.app j).hom.toRingHom
    haveI : pj.IsPrime := hp_i_prime j
    -- `cj` maps to `c` under the stage `j` cocone leg.
    have hcj_to_c : (P.ι.app j).hom cj = c := by
      show (P.ι.app j).hom ((P.diag.map fij).hom c') = c
      exact (hnat fij c').trans hc'
    have hcj_mem : cj ∈ pj.primeCompl := fun hmem => hcp <| by
      have h1 : (P.ι.app j).hom.toRingHom cj ∈ p := hmem
      rw [← hcj_to_c]
      exact h1
    -- The equation at stage `j`.
    have hkey_j :
        cj * (algebraMap R (P.diag.obj j) s₂ * algebraMap R (P.diag.obj j) r₁) =
        cj * (algebraMap R (P.diag.obj j) s₁ * algebraMap R (P.diag.obj j) r₂) := by
      have hjeq' : (P.diag.map fij).hom (c' * (algebraMap R (P.diag.obj i₀) s₂ *
          algebraMap R (P.diag.obj i₀) r₁)) =
          (P.diag.map fij).hom (c' * (algebraMap R (P.diag.obj i₀) s₁ *
            algebraMap R (P.diag.obj i₀) r₂)) := hjeq
      simp only [map_mul, AlgHom.commutes] at hjeq'
      exact hjeq'
    -- The prime equation at stage `j`.
    have hq_eq_j : p.comap (algebraMap R S) =
        pj.comap (algebraMap R (P.diag.obj j)) := hq_eq j
    -- Translate the primeCompl memberships of `s₁, s₂` to stage `j`.
    have hs₁' : s₁ ∈ (pj.comap (algebraMap R (P.diag.obj j))).primeCompl :=
      fun hmem => hs₁ <| by rw [hq_eq_j]; exact hmem
    have hs₂' : s₂ ∈ (pj.comap (algebraMap R (P.diag.obj j))).primeCompl :=
      fun hmem => hs₂ <| by rw [hq_eq_j]; exact hmem
    -- The image under `localRingHom` of `mk' rₖ ⟨sₖ, ...⟩` is `mk' (alg rₖ) ⟨alg sₖ, ...⟩`.
    have himg :
        Localization.localRingHom (pj.comap (algebraMap R (P.diag.obj j))) pj
            (algebraMap R (P.diag.obj j)) rfl
            (IsLocalization.mk'
              (Localization.AtPrime (pj.comap (algebraMap R (P.diag.obj j))))
              r₁ ⟨s₁, hs₁'⟩) =
        Localization.localRingHom (pj.comap (algebraMap R (P.diag.obj j))) pj
            (algebraMap R (P.diag.obj j)) rfl
            (IsLocalization.mk' _ r₂ ⟨s₂, hs₂'⟩) := by
      rw [Localization.localRingHom_mk', Localization.localRingHom_mk']
      rw [IsLocalization.eq]
      exact ⟨⟨cj, hcj_mem⟩, hkey_j⟩
    have hxy_in_Rq' := (h j pj).1 himg
    -- Transport from `Localization.AtPrime (pj.comap (algebraMap R _))` to
    -- `Localization.AtPrime (p.comap (algebraMap R S))`.
    rw [IsLocalization.eq] at hxy_in_Rq' ⊢
    obtain ⟨⟨c0, hc0⟩, hc0_eq⟩ := hxy_in_Rq'
    refine ⟨⟨c0, ?_⟩, hc0_eq⟩
    intro hmem
    apply hc0
    rw [← hq_eq_j]
    exact hmem
  · -- SURJECTIVITY.
    intro z
    obtain ⟨⟨s, u, hu⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    -- Lift `s, u` to a common stage `i`.
    obtain ⟨i, s', u', hs', hu'⟩ : ∃ (i : ι) (s' u' : ↑(P.diag.obj i)),
        (P.ι.app i).hom s' = s ∧ (P.ι.app i).hom u' = u :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hcolim s u
    let pi : Ideal (P.diag.obj i) := p.comap (P.ι.app i).hom.toRingHom
    haveI : pi.IsPrime := hp_i_prime i
    have hu'_mem : u' ∈ pi.primeCompl := fun hmem => hu <| by
      have h1 : (P.ι.app i).hom.toRingHom u' ∈ p := hmem
      rw [← hu']
      exact h1
    have hq_eq_i : p.comap (algebraMap R S) =
        pi.comap (algebraMap R (P.diag.obj i)) := hq_eq i
    -- Use surjectivity at stage `i` to find a preimage.
    obtain ⟨w, hw⟩ := (h i pi).2 (IsLocalization.mk'
        (Localization.AtPrime pi) s' ⟨u', hu'_mem⟩)
    obtain ⟨⟨a, b, hb⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (pi.comap (algebraMap R (P.diag.obj i))).primeCompl w
    rw [Localization.localRingHom_mk'] at hw
    -- Extract witness from the mk'-equality at stage `i`.
    rw [IsLocalization.eq] at hw
    obtain ⟨⟨e, he⟩, he_eq⟩ := hw
    simp only at he_eq
    -- Build the preimage.
    have hb_R : b ∈ (p.comap (algebraMap R S)).primeCompl := by
      intro hmem
      apply hb
      rw [← hq_eq_i]
      exact hmem
    refine ⟨IsLocalization.mk' _ a ⟨b, hb_R⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    rw [IsLocalization.eq]
    refine ⟨⟨(P.ι.app i).hom e, ?_⟩, ?_⟩
    · -- `(P.ι.app i).hom e ∉ p`
      intro hmem
      exact he (Ideal.mem_comap.mpr hmem)
    · -- equation in `S`: apply `(P.ι.app i).hom` to `he_eq` and simplify.
      have heq := congrArg (P.ι.app i).hom he_eq
      simp only [map_mul, hcomm, hs', hu'] at heq
      exact heq

/-- An ind-Zariski algebra map is bijective on stalks. -/
@[stacks 096T]
theorem bijectiveOnStalks_algebraMap [Algebra.IndZariski R S] :
    (algebraMap R S).BijectiveOnStalks := by
  obtain ⟨ι, _, _, P, h⟩ := IndZariski.exists_colimitPresentation (R := R) (S := S)
  have h_stage : ∀ i, (algebraMap R (P.diag.obj i)).BijectiveOnStalks := fun i => by
    haveI : Algebra.IsLocalIso R (P.diag.obj i) := h i
    exact RingHom.IsLocalIso.bijectiveOnStalks (RingHom.isLocalIso_algebraMap.mpr ‹_›)
  exact bijectiveOnStalks_of_colimitPresentation P h_stage

theorem of_colimitPresentation {ι : Type u} [SmallCategory ι] [IsFiltered ι]
    (P : ColimitPresentation ι (CommAlgCat.of R S))
    (h : ∀ (i : ι), Algebra.IndZariski R (P.diag.obj i)) : Algebra.IndZariski R S := by
  rw [iff_ind_isLocalIso, ← ObjectProperty.ind_ind
    (CommAlgCat.isLocalIso_le_isFinitelyPresentable R)]
  exact ⟨ι, ‹_›, ‹_›, P, fun i => (iff_ind_isLocalIso R _).mp (h i)⟩

end Algebra.IndZariski

end Algebra

section RingHom

/-- A ring hom is ind-Zariski if and only if it is an ind-Zariski algebra. -/
@[stacks 096N, algebraize Algebra.IndZariski]
def RingHom.IndZariski {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IndZariski R S

namespace RingHom.IndZariski

lemma algebraMap_iff [Algebra R S] :
    (algebraMap R S).IndZariski ↔ Algebra.IndZariski R S:=
  toAlgebra_algebraMap (R := R) (S := S).symm ▸ Iff.rfl

variable {R S T}

lemma iff_ind_isLocalIso (f : R →+* S) :
    f.IndZariski ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IsLocalIso) (CommRingCat.ofHom f) := by
  algebraize [f]
  rw [RingHom.IndZariski, Algebra.IndZariski.iff_ind_isLocalIso, ← f.algebraMap_toAlgebra,
    RingHom.IsLocalIso.respectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty,
    CommAlgCat.isLocalIso_eq]
  try rfl

/-- A ring hom is ind-Zariski if and only if it can be written
as a colimit of local isomorphisms. -/
lemma iff_exists {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f.hom.IndZariski ↔
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{u})
      (t : (Functor.const J).obj R ⟶ D) (c : D ⟶ (Functor.const J).obj S)
      (_ : IsColimit (.mk _ c)), ∀ i, (t.app i).hom.IsLocalIso ∧ t.app i ≫ c.app i = f :=
  RingHom.IndZariski.iff_ind_isLocalIso _

lemma id : (RingHom.id R).IndZariski :=
  Algebra.IndZariski.refl

variable {f : R →+* S} {g : S →+* T}

lemma comp (hg : g.IndZariski) (hf : f.IndZariski) : (g.comp f).IndZariski := by
  algebraize [f, g, g.comp f]
  exact Algebra.IndZariski.trans R S T

lemma prod {g : R →+* T} (hf : f.IndZariski) (hg : g.IndZariski) : (f.prod g).IndZariski := by
  algebraize [f, g]
  exact Algebra.IndZariski.prod R S T

lemma pi {ι : Type u} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    (f : ∀ i, R →+* (S i)) (hf : ∀ i, (f i).IndZariski) : (Pi.ringHom f).IndZariski := by
  let (i : ι) : Algebra R (S i) := (f i).toAlgebra
  have (i : ι) : Algebra.IndZariski R (S i) := hf i
  exact Algebra.IndZariski.pi R S

lemma flat (h : f.IndZariski) : f.Flat := by
  algebraize [f]
  exact .of_indZariski R S

@[stacks 096T]
theorem bijectiveOnStalks (h : f.IndZariski) : f.BijectiveOnStalks := by
  algebraize [f]
  exact Algebra.IndZariski.bijectiveOnStalks_algebraMap R S

/-- Local isomorphisms (as a `MorphismProperty` on `CommRingCat`) are finitely presentable. -/
lemma isLocalIso_le_isFinitelyPresentable :
    RingHom.toMorphismProperty.{u} RingHom.IsLocalIso ≤
      MorphismProperty.isFinitelyPresentable.{u} CommRingCat.{u} := by
  intro X Y f hf
  algebraize [f.hom]
  have : Algebra.IsLocalIso X Y := hf
  exact CommRingCat.isFinitelyPresentable_under _ _
    (Algebra.IsLocalIso.finitePresentation X Y)

/-- Ind-Zariski is equivalent to ind-ind-Zariski. -/
lemma iff_ind_indZariski (f : R →+* S) :
    f.IndZariski ↔ MorphismProperty.ind.{u}
      (RingHom.toMorphismProperty RingHom.IndZariski) (CommRingCat.ofHom f) := by
  rw [iff_ind_isLocalIso, ← MorphismProperty.ind_ind isLocalIso_le_isFinitelyPresentable.{u}]
  have heq : RingHom.toMorphismProperty RingHom.IndZariski =
      MorphismProperty.ind.{u} (RingHom.toMorphismProperty RingHom.IsLocalIso) := by
    ext X Y g
    exact iff_ind_isLocalIso g.hom
  rw [heq]

/-- A ring hom is ind-Zariski if it can be written as a filtered colimit of ind-Zariski maps. -/
lemma of_isColimit {R S : CommRingCat.{u}} (f : R ⟶ S) (J : Type u) [SmallCategory J]
    [IsFiltered J] (D : J ⥤ CommRingCat.{u}) {t : (Functor.const J).obj R ⟶ D}
    {c : D ⟶ (Functor.const J).obj S} (hc : IsColimit (.mk _ c))
    (htc : ∀ i, (t.app i).hom.IndZariski ∧ t.app i ≫ c.app i = f) : f.hom.IndZariski :=
  (iff_ind_indZariski _).mpr ⟨J, ‹_›, ‹_›, D, t, c, hc, by simpa using htc⟩

theorem _root_.Algebra.IndZariski.iff_ind_indZariksi [Algebra R S] :
    Algebra.IndZariski R S ↔ ObjectProperty.ind.{u}
      (RingHom.toObjectProperty RingHom.IndZariski R) (.of R S) := by
  rw [Algebra.IndZariski.iff_ind_isLocalIso,
    ← ObjectProperty.ind_ind (CommAlgCat.isLocalIso_le_isFinitelyPresentable R)]
  have heq : RingHom.toObjectProperty RingHom.IndZariski R =
      ObjectProperty.ind.{u} (CommAlgCat.isLocalIso R) := by
    ext X
    exact (RingHom.IndZariski.algebraMap_iff R X).trans
      (Algebra.IndZariski.iff_ind_isLocalIso R X)
  rw [heq]

end RingHom.IndZariski

end RingHom
