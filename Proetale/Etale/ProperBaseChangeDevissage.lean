/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.DevissageComparisonB

/-!
# Dévissage in `K` for the proper base change theorem

Let

```
X' --g'--> X
|          |
f'         f
↓          ↓
S' --g---> S
```

be a commutative square of schemes. The proper base change theorem asserts that the
derived base change transformation `Rf_* ⋙ g^* ⟶ g'^* ⋙ Rf'_*` is an isomorphism on
every bounded below complex with locally torsion cohomology sheaves (when the square is
cartesian and `f` is proper). This file proves the **dévissage in `K`**: the statement
for arbitrary such complexes follows from the statement for a single locally torsion
sheaf placed in degree `0`
(`AlgebraicGeometry.Scheme.isIso_derivedBaseChangeNatTrans_app_of_singleFunctor`).

The proof avoids the (not yet formalized) triangulated structure on
`DerivedCategoryPlus` and instead works entirely with concrete short exact sequences of
bounded below cochain complexes:

- a morphism `ψ` of bounded below complexes becomes an isomorphism in
  `DerivedCategoryPlus` iff it is a quasi-isomorphism
  (`DerivedCategoryPlus.isIso_Q_map_iff_quasiIso`);
- on a fibrant complex `I` (a bounded below complex of injectives for the injective
  model structure on `CochainComplex.Plus`), the value of the derived base change
  transformation is, up to isomorphism, `Q.map` of a concrete comparison morphism
  `g^* f_* I ⟶ f'_* J` for any fibrant replacement `J` of `g'^* I`;
- short exact sequences of complexes are resolved by short exact sequences of fibrant
  complexes (a model-categorical horseshoe lemma,
  `CochainComplex.Plus.exists_fibrant_ses_resolution`);
- the five lemma for the homology long exact sequence then yields a two-out-of-three
  property for the class of complexes on which the transformation is an isomorphism;
- singles in all degrees are reached from degree `0` via short exact sequences
  `0 ⟶ single (n+1) F ⟶ D ⟶ single n F ⟶ 0` with `D` acyclic (no shift functors are
  needed), and general complexes by induction on the cohomological amplitude using the
  canonical truncations; finally, bounded below complexes with unbounded cohomology are
  treated degreewise using that a fibrant complex which is acyclic in degrees `< n`
  splits in low degrees, so that its image under any additive functor is acyclic in
  degrees `≤ n - 2`.
-/

universe w v u v' u'

open CategoryTheory Limits HomotopicalAlgebra

/-! ## Singles in all degrees, acyclic complexes, and the dévissage -/


namespace AlgebraicGeometry.Scheme

open CochainComplex.Plus CochainComplex.Plus.modelCategoryQuillen HomologicalComplex ZeroObject

variable {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf X'.smallEtaleTopology Ab.{u + 1})]
  [HasDerivedCategoryPlus.{u + 1} (Sheaf S'.smallEtaleTopology Ab.{u + 1})]

/-- The single-sheaf hypothesis of the dévissage: the derived base change
transformation is an isomorphism on every locally torsion abelian sheaf placed in
degree `0`. -/
def SingleBaseChangeHyp : Prop :=
  ∀ (F : Sheaf X.smallEtaleTopology Ab.{u + 1}), Sheaf.IsLocallyTorsion F →
    IsIso ((derivedBaseChangeNatTrans f g f' g' w).app
      ((DerivedCategoryPlus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F))

/-- The derived base change transformation is an isomorphism on acyclic complexes,
assuming the single-sheaf hypothesis. -/
lemma baseChangeIso_of_acyclic (H : SingleBaseChangeHyp f g f' g' w)
    (M : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hM : ∀ i, M.obj.ExactAt i) : BaseChangeIso f g f' g' w M := by
  have h0 : BaseChangeIso f g f' g' w
      ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj 0, ⟨0, inferInstance⟩⟩ :=
    H 0 (Sheaf.isLocallyTorsion_of_isZero (isZero_zero _))
  refine (baseChangeIso_iff_of_quasiIso f g f' g' w
    (ObjectProperty.homMk (0 : M.obj ⟶ _)) ?_).mpr h0
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_exactAt _ i (hM i)]
  by_cases hi : i = 0
  · subst hi
    exact HomologicalComplex.ExactAt.of_isZero
      (IsZero.of_iso (isZero_zero _) (HomologicalComplex.singleObjXSelf _ 0 0))
  · exact HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

/-- The derived base change transformation is an isomorphism on all singles of locally
torsion sheaves, in any degree, assuming the single-sheaf hypothesis in degree `0`. -/
lemma baseChangeIso_single (H : SingleBaseChangeHyp f g f' g' w)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) (hF : Sheaf.IsLocallyTorsion F) :
    ∀ (n : ℤ), BaseChangeIso f g f' g' w
      ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj F, ⟨n, inferInstance⟩⟩ := by
  -- both induction steps go through the short exact sequence `singleDoubleSES F n`
  have hdouble : ∀ n : ℤ, BaseChangeIso f g f' g' w ⟨idDouble F n, idDouble_plus F n⟩ :=
    fun n => baseChangeIso_of_acyclic f g f' g' w H _ (idDouble_exactAt F n)
  have hup : ∀ n : ℤ, BaseChangeIso f g f' g' w
      ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj F, ⟨n, inferInstance⟩⟩ →
      BaseChangeIso f g f' g' w
        ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) (n + 1)).obj F,
          ⟨n + 1, inferInstance⟩⟩ := by
    intro n hn
    exact baseChangeIso_X₁ f g f' g' w (singleDoubleSES F n)
      (singleDoubleSES_shortExact F n)
      ⟨n + 1, inferInstanceAs (CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ)
        (n + 1)).obj F) (n + 1))⟩
      (idDouble_plus F n)
      ⟨n, inferInstanceAs (CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ)
        n).obj F) n)⟩ (hdouble n) hn
  have hdown : ∀ n : ℤ, BaseChangeIso f g f' g' w
      ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) (n + 1)).obj F,
        ⟨n + 1, inferInstance⟩⟩ →
      BaseChangeIso f g f' g' w
        ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj F, ⟨n, inferInstance⟩⟩ := by
    intro n hn
    exact baseChangeIso_X₃ f g f' g' w (singleDoubleSES F n)
      (singleDoubleSES_shortExact F n)
      ⟨n + 1, inferInstanceAs (CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ)
        (n + 1)).obj F) (n + 1))⟩
      (idDouble_plus F n)
      ⟨n, inferInstanceAs (CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ)
        n).obj F) n)⟩ hn (hdouble n)
  intro n
  induction n using Int.induction_on with
  | zero => exact H F hF
  | succ k ih => exact hup k ih
  | pred k ih =>
    refine hdown (-(k : ℕ) - 1) ?_
    have e : (-(k : ℕ) : ℤ) - 1 + 1 = -(k : ℕ) := by ring
    rw [e]
    exact ih

set_option synthInstance.maxHeartbeats 100000 in
-- the `HasHomology` searches on iterated truncations of sheaf complexes are large
/-- Peeling off the top cohomological degree: if `K` is cohomologically bounded above
by `b` with locally torsion homology and the canonical truncation `τ_{≤ b - 1} K`
satisfies `BaseChangeIso`, then so does `K`. The cokernel of `τ_{≤ b-1} K ⟶ K` is
quasi-isomorphic to a single in degree `b`. -/
lemma baseChangeIso_of_truncLE (H : SingleBaseChangeHyp f g f' g' w)
    (K : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ)
    (p : CochainComplex.plus _ K) (b : ℤ) [K.IsLE b]
    (hT : ∀ n, Sheaf.IsLocallyTorsion (K.homology n))
    (h₁ : ∀ (p₁ : CochainComplex.plus _ (K.truncLE (b - 1))),
      BaseChangeIso f g f' g' w ⟨K.truncLE (b - 1), p₁⟩) :
    BaseChangeIso f g f' g' w ⟨K, p⟩ := by
  obtain ⟨a, ha⟩ := id p
  haveI := ha
  haveI : ∀ i, ((K.truncGE b).truncLE b).HasHomology i := fun i =>
    CategoryTheory.CategoryWithHomology.hasHomology _
  -- the short exact sequence `0 ⟶ τ_{≤ b-1} K ⟶ K ⟶ X₃ ⟶ 0`
  have hSq : (K.shortComplexTruncLE (b - 1)).ShortExact :=
    K.shortComplexTruncLE_shortExact (b - 1)
  -- the third term is quasi-isomorphic to `τ_{≥ b} K`
  let ρ : (K.shortComplexTruncLE (b - 1)).X₃ ⟶ K.truncGE b :=
    K.shortComplexTruncLEX₃ToTruncGE (b - 1) b (by lia)
  haveI hρ : QuasiIso ρ := by
    dsimp [ρ]
    infer_instance
  -- `τ_{≥ b} K` is cohomologically concentrated in degree `b`
  haveI : (K.truncGE b).IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    haveI := K.quasiIsoAt_πTruncGE b i (by lia)
    exact (exactAt_iff_of_quasiIsoAt (K.πTruncGE b) i).mp
      (K.exactAt_of_isLE b i hi)
  -- its truncation `τ_{≤ b}` is concentrated in degree `b` and isomorphic to a single
  obtain ⟨W, ⟨eY⟩⟩ := CochainComplex.exists_iso_single ((K.truncGE b).truncLE b) b
  -- `W` is locally torsion, being isomorphic to `H^b K`
  have hW : Sheaf.IsLocallyTorsion W := by
    haveI := K.quasiIsoAt_πTruncGE b b (le_refl b)
    haveI := (K.truncGE b).quasiIsoAt_ιTruncLE b b (le_refl b)
    have hiso₁ : IsIso (HomologicalComplex.homologyMap (K.πTruncGE b) b) := by
      rw [← quasiIsoAt_iff_isIso_homologyMap]
      infer_instance
    have hiso₂ : IsIso (HomologicalComplex.homologyMap ((K.truncGE b).ιTruncLE b) b) := by
      rw [← quasiIsoAt_iff_isIso_homologyMap]
      infer_instance
    refine Sheaf.IsLocallyTorsion.of_iso ?_ (hT b)
    exact (asIso (HomologicalComplex.homologyMap (K.πTruncGE b) b)) ≪≫
      (asIso (HomologicalComplex.homologyMap ((K.truncGE b).ιTruncLE b) b)).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) b).mapIso eY ≪≫
      (HomologicalComplex.homologyFunctorSingleIso
        (Sheaf X.smallEtaleTopology Ab.{u + 1}) (ComplexShape.up ℤ) b).app W
  -- plus-ness of all objects involved
  have pY : CochainComplex.plus _ ((K.truncGE b).truncLE b) := ⟨b, inferInstance⟩
  have pG : CochainComplex.plus _ (K.truncGE b) := ⟨b, inferInstance⟩
  have p₃ : CochainComplex.plus _ (K.shortComplexTruncLE (b - 1)).X₃ :=
    (CochainComplex.plus _).prop_colimit (parallelPair (K.ιTruncLE (b - 1)) 0) (fun j => by
      obtain (_ | _) := j
      · exact ⟨a, inferInstanceAs (CochainComplex.IsStrictlyGE (K.truncLE (b - 1)) a)⟩
      · exact ⟨a, ha⟩)
  -- transfer `BaseChangeIso` along the chain of quasi-isomorphisms
  haveI hHW : ∀ i, (((HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj W :
      CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ)).HasHomology i := fun i =>
    CategoryTheory.CategoryWithHomology.hasHomology _
  haveI hHG : ∀ i, (K.truncGE b).HasHomology i := fun i =>
    CategoryTheory.CategoryWithHomology.hasHomology _
  have hqY : QuasiIso eY.hom := inferInstance
  have hqι : QuasiIso ((K.truncGE b).ιTruncLE b) := inferInstance
  have hsingle : BaseChangeIso f g f' g' w
      ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj W, ⟨b, inferInstance⟩⟩ :=
    baseChangeIso_single f g f' g' w H W hW b
  have hY : BaseChangeIso f g f' g' w ⟨(K.truncGE b).truncLE b, pY⟩ :=
    (baseChangeIso_iff_of_quasiIso f g f' g' w
      (M := ⟨(K.truncGE b).truncLE b, pY⟩)
      (N := ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) b).obj W, ⟨b, inferInstance⟩⟩)
      (ObjectProperty.homMk eY.hom) hqY).mpr hsingle
  have hG : BaseChangeIso f g f' g' w ⟨K.truncGE b, pG⟩ :=
    (baseChangeIso_iff_of_quasiIso f g f' g' w
      (M := ⟨(K.truncGE b).truncLE b, pY⟩) (N := ⟨K.truncGE b, pG⟩)
      (ObjectProperty.homMk ((K.truncGE b).ιTruncLE b))
      hqι).mp hY
  have h₃ : BaseChangeIso f g f' g' w ⟨(K.shortComplexTruncLE (b - 1)).X₃, p₃⟩ :=
    (baseChangeIso_iff_of_quasiIso f g f' g' w
      (M := ⟨(K.shortComplexTruncLE (b - 1)).X₃, p₃⟩) (N := ⟨K.truncGE b, pG⟩)
      (ObjectProperty.homMk ρ) hρ).mpr hG
  -- conclude by the two-out-of-three property
  have p₁ : CochainComplex.plus _ (K.truncLE (b - 1)) := ⟨a, inferInstance⟩
  exact baseChangeIso_X₂ f g f' g' w (K.shortComplexTruncLE (b - 1)) hSq
    p₁ p p₃ (h₁ p₁) h₃

/-- The bounded dévissage: the derived base change transformation is an isomorphism on
every bounded below complex with locally torsion homology which is moreover
cohomologically bounded above, assuming the single-sheaf hypothesis. -/
lemma baseChangeIso_of_isLE (H : SingleBaseChangeHyp f g f' g' w)
    (K : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ)
    (p : CochainComplex.plus _ K) (b : ℤ) (hb : K.IsLE b)
    (hT : ∀ n, Sheaf.IsLocallyTorsion (K.homology n)) :
    BaseChangeIso f g f' g' w ⟨K, p⟩ := by
  obtain ⟨a, ha⟩ := id p
  suffices h : ∀ (k : ℕ) (K : CochainComplex (Sheaf X.smallEtaleTopology Ab.{u + 1}) ℤ)
      (a b : ℤ), K.IsStrictlyGE a → K.IsLE b →
      (∀ n, Sheaf.IsLocallyTorsion (K.homology n)) → (b - a).toNat ≤ k →
      ∀ (p : CochainComplex.plus _ K), BaseChangeIso f g f' g' w ⟨K, p⟩ by
    exact h (b - a).toNat K a b ha hb hT le_rfl p
  intro k
  induction k with
  | zero =>
    intro K a b hge hle hT hk p
    haveI := hge
    haveI := hle
    have hba : b ≤ a := by omega
    by_cases hlt : b < a
    · -- `K` is acyclic
      refine baseChangeIso_of_acyclic f g f' g' w H _ (fun i => ?_)
      by_cases hia : i < a
      · exact K.exactAt_of_isGE a i hia
      · exact K.exactAt_of_isLE b i (by omega)
    · -- `b = a`: the truncation `τ_{≤ b - 1} K` is acyclic
      refine baseChangeIso_of_truncLE f g f' g' w H K p b hT (fun p₁ => ?_)
      refine baseChangeIso_of_acyclic f g f' g' w H _ (fun i => ?_)
      by_cases hib : b - 1 < i
      · exact (K.truncLE (b - 1)).exactAt_of_isLE (b - 1) i hib
      · haveI := K.quasiIsoAt_ιTruncLE (b - 1) i (by omega)
        exact (exactAt_iff_of_quasiIsoAt (K.ιTruncLE (b - 1)) i).mpr
          (K.exactAt_of_isGE a i (by omega))
  | succ k ih =>
    intro K a b hge hle hT hk p
    haveI := hge
    haveI := hle
    by_cases hlt : b < a
    · refine baseChangeIso_of_acyclic f g f' g' w H _ (fun i => ?_)
      by_cases hia : i < a
      · exact K.exactAt_of_isGE a i hia
      · exact K.exactAt_of_isLE b i (by omega)
    · refine baseChangeIso_of_truncLE f g f' g' w H K p b hT (fun p₁ => ?_)
      haveI : (K.truncLE (b - 1)).IsLE (b - 1) := by
        rw [CochainComplex.isLE_iff]
        intro i hi
        exact (K.truncLE (b - 1)).exactAt_of_isLE (b - 1) i hi
      refine ih (K.truncLE (b - 1)) a (b - 1) inferInstance inferInstance ?_ (by omega) p₁
      intro n
      by_cases hn : n ≤ b - 1
      · haveI := K.quasiIsoAt_ιTruncLE (b - 1) n hn
        have hiso : IsIso (HomologicalComplex.homologyMap (K.ιTruncLE (b - 1)) n) := by
          rw [← quasiIsoAt_iff_isIso_homologyMap]
          infer_instance
        exact Sheaf.IsLocallyTorsion.of_iso
          (asIso (HomologicalComplex.homologyMap (K.ιTruncLE (b - 1)) n)).symm (hT n)
      · exact Sheaf.isLocallyTorsion_of_isZero
          (((K.truncLE (b - 1)).exactAt_of_isLE (b - 1) n (by omega)).isZero_homology)

/-- **Dévissage in `K` for the proper base change theorem, bounded case**: if the
derived base change transformation is an isomorphism on every locally torsion abelian
sheaf placed in degree `0`, then it is an isomorphism on every complex with locally
torsion cohomology which is moreover cohomologically bounded above. -/
theorem isIso_derivedBaseChangeNatTrans_app_of_singleFunctor_of_isLE
    (H : ∀ (F : Sheaf X.smallEtaleTopology Ab.{u + 1}), Sheaf.IsLocallyTorsion F →
      IsIso ((derivedBaseChangeNatTrans f g f' g' w).app
        ((DerivedCategoryPlus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F)))
    (K : DerivedCategoryPlus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : ∀ n : ℤ, Sheaf.IsLocallyTorsion
      ((DerivedCategoryPlus.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K))
    (b : ℤ)
    (hb : ∀ n : ℤ, b ≤ n → IsZero
      ((DerivedCategoryPlus.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K)) :
    IsIso ((derivedBaseChangeNatTrans f g f' g' w).app K) := by
  haveI : (DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).EssSurj :=
    Localization.essSurj _ (CochainComplex.Plus.quasiIso _)
  obtain ⟨M, ⟨e⟩⟩ : ∃ M, Nonempty
      ((DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).obj M ≅ K) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ K⟩⟩
  rw [← NatTrans.isIso_app_iff_of_isIso (derivedBaseChangeNatTrans f g f' g' w) e.hom]
  have hfac : ∀ n : ℤ, (DerivedCategoryPlus.homologyFunctor
      (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K ≅ M.obj.homology n := fun n =>
    (DerivedCategoryPlus.homologyFunctor _ n).mapIso e.symm ≪≫
      (DerivedCategoryPlus.homologyFunctorFactors _ n).app M
  have hT : ∀ n, Sheaf.IsLocallyTorsion (M.obj.homology n) := fun n =>
    Sheaf.IsLocallyTorsion.of_iso (hfac n) (hK n)
  have hle : M.obj.IsLE (b - 1) := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hb i (by omega)).of_iso (hfac i).symm
  exact baseChangeIso_of_isLE f g f' g' w H M.obj M.2 (b - 1) hle hT

/-- **Dévissage in `K` for the proper base change theorem.** If the derived base
change transformation `Rf_* ⋙ g^* ⟶ g'^* ⋙ Rf'_*` is an isomorphism on every locally
torsion abelian sheaf placed in degree `0` of the bounded below derived category, then
it is an isomorphism on every bounded below complex with locally torsion cohomology
sheaves. -/
theorem isIso_derivedBaseChangeNatTrans_app_of_singleFunctor
    (H : ∀ (F : Sheaf X.smallEtaleTopology Ab.{u + 1}), Sheaf.IsLocallyTorsion F →
      IsIso ((derivedBaseChangeNatTrans f g f' g' w).app
        ((DerivedCategoryPlus.singleFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) 0).obj F)))
    (K : DerivedCategoryPlus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : ∀ n : ℤ, Sheaf.IsLocallyTorsion
      ((DerivedCategoryPlus.homologyFunctor (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K)) :
    IsIso ((derivedBaseChangeNatTrans f g f' g' w).app K) := by
  -- replace `K` by `Q.obj M` for a bounded below complex `M`
  haveI : (DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).EssSurj :=
    Localization.essSurj _ (CochainComplex.Plus.quasiIso _)
  obtain ⟨M, ⟨e⟩⟩ : ∃ M, Nonempty
      ((DerivedCategoryPlus.Q (Sheaf X.smallEtaleTopology Ab.{u + 1})).obj M ≅ K) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ K⟩⟩
  rw [← NatTrans.isIso_app_iff_of_isIso (derivedBaseChangeNatTrans f g f' g' w) e.hom]
  have hfacM : ∀ n : ℤ, (DerivedCategoryPlus.homologyFunctor
      (Sheaf X.smallEtaleTopology Ab.{u + 1}) n).obj K ≅ M.obj.homology n := fun n =>
    (DerivedCategoryPlus.homologyFunctor _ n).mapIso e.symm ≪≫
      (DerivedCategoryPlus.homologyFunctorFactors _ n).app M
  -- replace `M` by a fibrant complex `R` (a bounded below complex of injectives)
  let R : CochainComplex.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}) :=
    FibrantObject.HoCat.resolutionObj M
  let iR : M ⟶ R := FibrantObject.HoCat.iResolutionObj M
  have hiR : QuasiIso iR.hom := by
    rw [← modelCategoryQuillen.weakEquivalence_iff]
    infer_instance
  show BaseChangeIso f g f' g' w M
  rw [baseChangeIso_iff_of_quasiIso f g f' g' w iR hiR]
  -- the homology of `R` is locally torsion
  have hTR : ∀ n, Sheaf.IsLocallyTorsion (R.obj.homology n) := by
    intro n
    have hiso : IsIso (HomologicalComplex.homologyMap iR.hom n) := by
      rw [← quasiIsoAt_iff_isIso_homologyMap]
      exact hiR.quasiIsoAt n
    exact Sheaf.IsLocallyTorsion.of_iso
      (hfacM n ≪≫ asIso (HomologicalComplex.homologyMap iR.hom n)) (hK n)
  -- choose a fibrant replacement of `g'^* R` and reduce to a quasi-isomorphism claim
  let J : CochainComplex.Plus (Sheaf X'.smallEtaleTopology Ab.{u + 1}) :=
    FibrantObject.HoCat.resolutionObj ((etalePullback g').mapCochainComplexPlus.obj R)
  let jJ : (etalePullback g').mapCochainComplexPlus.obj R ⟶ J :=
    FibrantObject.HoCat.iResolutionObj _
  have hjJ : QuasiIso jJ.hom := by
    rw [← modelCategoryQuillen.weakEquivalence_iff]
    infer_instance
  rw [baseChangeIso_iff_quasiIso_baseChangeComparison f g f' g' w R jJ hjJ]
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  -- reformulate via the homology of the derived transformation at `Q.obj R`
  rw [← isIso_homologyMap_baseChangeComparison_iff f g f' g' w R jJ hjJ q]
  -- the truncation short exact sequence at level `q + 2`
  have hSq : (R.obj.shortComplexTruncLE (q + 2)).ShortExact :=
    R.obj.shortComplexTruncLE_shortExact (q + 2)
  obtain ⟨a, ha⟩ := id R.2
  haveI := ha
  have p₁ : CochainComplex.plus _ (R.obj.truncLE (q + 2)) := ⟨a, inferInstance⟩
  -- the first term satisfies `BaseChangeIso` by the bounded dévissage
  have hX₁ : BaseChangeIso f g f' g' w ⟨R.obj.truncLE (q + 2), p₁⟩ := by
    haveI : (R.obj.truncLE (q + 2)).IsLE (q + 2) := by
      rw [CochainComplex.isLE_iff]
      intro i hi
      exact (R.obj.truncLE (q + 2)).exactAt_of_isLE (q + 2) i hi
    refine baseChangeIso_of_isLE f g f' g' w H _ p₁ (q + 2) inferInstance (fun n => ?_)
    by_cases hn : n ≤ q + 2
    · haveI := R.obj.quasiIsoAt_ιTruncLE (q + 2) n hn
      have hiso : IsIso (HomologicalComplex.homologyMap (R.obj.ιTruncLE (q + 2)) n) := by
        rw [← quasiIsoAt_iff_isIso_homologyMap]
        infer_instance
      exact Sheaf.IsLocallyTorsion.of_iso
        (asIso (HomologicalComplex.homologyMap (R.obj.ιTruncLE (q + 2)) n)).symm (hTR n)
    · exact Sheaf.isLocallyTorsion_of_isZero
        (((R.obj.truncLE (q + 2)).exactAt_of_isLE (q + 2) n (by omega)).isZero_homology)
  -- the third term is exact in degrees `< q + 3`
  have hX₃exact : ∀ i, i < q + 3 → (R.obj.shortComplexTruncLE (q + 2)).X₃.ExactAt i := by
    intro i hi
    have hqq : (q + 2 : ℤ) + 1 = q + 3 := by ring
    let ρ' := R.obj.shortComplexTruncLEX₃ToTruncGE (q + 2) (q + 3) hqq
    haveI hρ' : QuasiIso ρ' := by
      dsimp only [ρ']
      infer_instance
    haveI := hρ'.quasiIsoAt i
    refine (exactAt_iff_of_quasiIsoAt ρ' i).mpr ?_
    exact (R.obj.truncGE (q + 3)).exactAt_of_isGE (q + 3) i hi
  -- resolve the truncation sequence by a fibrant one
  obtain ⟨T', Φ, hT', ⟨q₁', q₂', q₃'⟩, ⟨k₁', k₂', k₃'⟩, m₁, m₂, m₃⟩ :=
    CochainComplex.Plus.exists_fibrant_ses_resolution
      (R.obj.shortComplexTruncLE (q + 2)) hSq p₁ R.2
  -- the ladder attached to the fibrant resolution
  obtain ⟨R₁, R₂, Ψ, hR₁, hR₂, -, hdeg, hvan⟩ := exists_ladder_of_fibrant f g f' g' w
    T' hT' q₁' q₂' q₃' k₁' k₂' k₃'
  -- vanishing of the third column in the relevant degrees
  have hvan' : ∀ r, r ≤ q + 1 → (R₁.X₃.ExactAt r ∧ R₂.X₃.ExactAt r) := by
    refine fun r hr => hvan (q + 3) (fun i hi => ?_) r (by omega)
    haveI := m₃.quasiIsoAt i
    exact (exactAt_iff_of_quasiIsoAt Φ.τ₃ i).mp (hX₃exact i hi)
  -- transfer of the per-degree statements from the truncation sequence to `T'`
  have htr₁ : ∀ r, IsIso ((DerivedCategoryPlus.homologyFunctor _ r).map
      ((derivedBaseChangeNatTrans f g f' g' w).app
        ((DerivedCategoryPlus.Q _).obj (⟨T'.X₁, q₁'⟩ : CochainComplex.Plus _)))) := by
    intro r
    have hBCI : BaseChangeIso f g f' g' w ⟨T'.X₁, q₁'⟩ :=
      (baseChangeIso_iff_of_quasiIso f g f' g' w
        (M := ⟨(R.obj.shortComplexTruncLE (q + 2)).X₁, p₁⟩) (N := ⟨T'.X₁, q₁'⟩)
        (ObjectProperty.homMk Φ.τ₁) m₁).mp hX₁
    haveI : IsIso ((derivedBaseChangeNatTrans f g f' g' w).app
        ((DerivedCategoryPlus.Q _).obj (⟨T'.X₁, q₁'⟩ : CochainComplex.Plus _))) := hBCI
    infer_instance
  -- the five lemma in degree `q`
  have hτ₂ : IsIso (HomologicalComplex.homologyMap Ψ.τ₂ q) := by
    refine HomologicalComplex.HomologySequence.isIso_homologyMap_τ₂ Ψ hR₁ hR₂
      (q - 1) q (q + 1) (by simp) (by simp) ?_ ?_ ?_ ?_
    · -- `Epi` in degree `q - 1`: the target homology vanishes
      exact epi_of_isZero ((hvan' (q - 1) (by omega)).2.isZero_homology) _
    · exact ((hdeg q).1).mp (htr₁ q)
    · -- `IsIso` in degree `q`: both homologies vanish
      exact isIso_of_isZero_of_isZero
        ((hvan' q (by omega)).1.isZero_homology)
        ((hvan' q (by omega)).2.isZero_homology) _
    · haveI : IsIso (HomologicalComplex.homologyMap Ψ.τ₁ (q + 1)) :=
        ((hdeg (q + 1)).1).mp (htr₁ (q + 1))
      infer_instance
  -- transfer back to the comparison morphism for `R`
  have h₂' := ((hdeg q).2.1).mpr hτ₂
  haveI : IsIso ((DerivedCategoryPlus.Q
      (Sheaf X.smallEtaleTopology Ab.{u + 1})).map (ObjectProperty.homMk Φ.τ₂ :
        (⟨(R.obj.shortComplexTruncLE (q + 2)).X₂, R.2⟩ : CochainComplex.Plus _) ⟶
          ⟨T'.X₂, q₂'⟩)) :=
    (DerivedCategoryPlus.isIso_Q_map_iff_quasiIso _).mpr m₂
  exact (isIso_homologyMap_derivedBaseChangeNatTrans_app_iff_of_isIso f g f' g' w
    ((DerivedCategoryPlus.Q _).map (ObjectProperty.homMk Φ.τ₂ :
      (⟨(R.obj.shortComplexTruncLE (q + 2)).X₂, R.2⟩ : CochainComplex.Plus _) ⟶
        ⟨T'.X₂, q₂'⟩)) q).mpr h₂'

end AlgebraicGeometry.Scheme
