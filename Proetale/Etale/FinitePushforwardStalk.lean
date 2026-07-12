/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Preserves
import Proetale.Mathlib.AlgebraicGeometry.Sites.DerivedPushforward
import Proetale.Mathlib.AlgebraicGeometry.Sites.GeometricPoint
import Proetale.Topology.Coherent.Etale

/-!
# Stalks of pushforwards along finite morphisms

This file works towards the sheaf-level half of the proper base change dévissage for
finite morphisms (blueprint `lemma:pbc-finite`): for a finite morphism `f : Y ⟶ X`, a
geometric point `x : Spec Ω ⟶ X` and an abelian sheaf `F` on the small étale site of
`Y`, the stalk of `f_* F` at `x` decomposes as a finite product of stalks of `F` at
geometric points of `Y` over `x`.

It contains the following fully proved stages.

## The pushforward-stalk colimit description

The pushforward along the small étale sites is precomposition with the base change
functor, so its stalk at `x` is the filtered colimit, over the étale neighbourhoods
`(U, u)` of `x`, of the sections `F(U ×_X Y)`:

- `AlgebraicGeometry.Scheme.Etale.etalePushforward_obj_obj` /
  `etalePushforward_obj_map`: the pushforward is evaluated at the base change,
  definitionally.
- `AlgebraicGeometry.Scheme.Etale.pushforwardStalkIsoColimit`: the colimit description
  of the stalk of the pushforward.
- `AlgebraicGeometry.Scheme.Etale.toPushforwardStalk` (with `toPushforwardStalk_w` and
  `pushforwardStalk_hom_ext`): the canonical cocone legs `F(U ×_X Y) ⟶ (f_* F)_x`.
- `AlgebraicGeometry.Scheme.Etale.pushforwardStalkToStalk`: for a geometric point
  `y : Spec Ω' ⟶ Y` lying over `x` (via any morphism `ε : Spec Ω' ⟶ Spec Ω`, allowing
  separably closed extension fields), the canonical comparison map
  `(f_* F)_x ⟶ F_y`, induced by the lifts `pullbackFiberLift` of the étale
  neighbourhoods of `x` to étale neighbourhoods of `y`. It is natural in `F`
  (`pushforwardStalkToStalk_naturality`).
- `AlgebraicGeometry.Scheme.Etale.pushforwardStalkToPiStalk`: the combined comparison
  map into the finite product of stalks. The goal theorem asserts that for finite `f`
  and a suitable finite family of lifts this map is an isomorphism.

Note that the extension field `Ω'` is necessary in general: for `X = Spec k` with `k`
separably closed but imperfect and `Y = Spec k^(1/p)`, the (finite) morphism `f` admits
no lift `y : Spec k ⟶ Y` of the identity geometric point at all, while
`(f_* F)_x = F(Y)` is in general nonzero; the geometric point of `Y` over `x` only
exists after passing to a separably closed extension of `k` containing `k^(1/p)`.

## Additivity

Sections of an abelian sheaf on the small étale site over a finite disjoint union
decompose as a finite product — the sheaf condition for the cover by the summands:

- `AlgebraicGeometry.Scheme.Etale.generate_ofArrows_cofanInj_mem_smallEtaleTopology`:
  the injections of a finite coproduct decomposition cover.
- `AlgebraicGeometry.Scheme.Etale.preservesProduct_sheaf_obj_of_isColimit`: an abelian
  sheaf takes the coproduct to a product (via
  `CategoryTheory.Presieve.preservesProduct_of_isSheafFor` and extensivity of the
  small étale site).
- `AlgebraicGeometry.Scheme.Etale.isLimitSheafObjFanOfIsColimit` and
  `AlgebraicGeometry.Scheme.Etale.sheafObjProdIsoOfIsColimit`: the limit fan and the
  induced isomorphism `F(V) ≅ ∏ᵢ F(Vᵢ)` with the restrictions as projections.

## Descent of idempotents to a finite stage

- `CommRingCat.exists_orthogonal_idempotents_of_isColimit`: a complete orthogonal
  system of idempotents in a filtered colimit of commutative rings descends to some
  stage. This will split the fiber `U ×_X Y` over a cofinal system of neighbourhoods,
  since the splitting of the finite algebra `Γ(Y ×_X Spec 𝒪^sh_{X,x})` into local
  factors (`AlgebraicGeometry.Scheme.Etale.
  finite_maximalSpectrum_and_bijective_pi_localization_of_finite`) is given by such a
  system of idempotents.
- `CategoryTheory.Limits.Types.FilteredColimit.exists_map_eq_of_isColimit`: finitely
  many equalities between elements of a filtered colimit of types are equalized at a
  single later stage.

## Remaining steps towards `lemma:pbc-finite`

The final assembly (not yet formalized) combines the above: over affine étale
neighbourhoods the fiber `U ×_X Y` is affine with `Γ(U ×_X Y)` finite over `Γ(U)` and
the transition maps are base changes, so `S = colim Γ(U ×_X Y)` is finite over the
strict localization; its splitting into finitely many strictly henselian local factors
descends (by the idempotent descent above) to a finite disjoint union decomposition of
`U ×_X Y` over a cofinal system of neighbourhoods; additivity and the commutation of
filtered colimits with finite products then reduce the claim to the cofinality of the
split neighbourhoods among the étale neighbourhoods of each geometric point of `Y`
over `x`.
-/

universe w v u

open CategoryTheory Limits MorphismProperty Opposite

namespace CategoryTheory.Limits.Types.FilteredColimit

variable {J : Type*} [Category* J] [IsFiltered J] {D : J ⥤ Type w} {c : Cocone D}

private lemma exists_map_eq_fin_of_isColimit (hc : IsColimit c) {j : J} {n : ℕ}
    (a b : Fin n → D.obj j) (h : ∀ m, c.ι.app j (a m) = c.ι.app j (b m)) :
    ∃ (k : J) (g : j ⟶ k), ∀ m, D.map g (a m) = D.map g (b m) := by
  induction n with
  | zero => exact ⟨j, 𝟙 j, fun m => m.elim0⟩
  | succ n ih =>
    obtain ⟨k, g, hk⟩ := ih (fun m => a m.castSucc) (fun m => b m.castSucc)
      (fun m => h m.castSucc)
    have hlast : c.ι.app k (D.map g (a (Fin.last n))) =
        c.ι.app k (D.map g (b (Fin.last n))) := by
      have h1 := ConcreteCategory.congr_hom (c.w g) (a (Fin.last n))
      have h2 := ConcreteCategory.congr_hom (c.w g) (b (Fin.last n))
      rw [ConcreteCategory.comp_apply] at h1 h2
      exact h1.trans ((h (Fin.last n)).trans h2.symm)
    obtain ⟨l, g', hg'⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc _ _).mp hlast
    refine ⟨l, g ≫ g', fun m => ?_⟩
    refine Fin.lastCases ?_ ?_ m
    · simpa [Functor.map_comp_apply] using hg'
    · intro m'
      simp only [Functor.map_comp_apply]
      rw [hk m']

/-- Finitely many pairs of elements at a stage of a filtered colimit of types that
become equal in the colimit are equalized by a single map to a later stage. -/
lemma exists_map_eq_of_isColimit (hc : IsColimit c) {j : J} {ι : Type*} [Finite ι]
    (a b : ι → D.obj j) (h : ∀ m, c.ι.app j (a m) = c.ι.app j (b m)) :
    ∃ (k : J) (g : j ⟶ k), ∀ m, D.map g (a m) = D.map g (b m) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨k, g, hk⟩ := exists_map_eq_fin_of_isColimit hc (a ∘ e.symm) (b ∘ e.symm)
    (fun m => h _)
  exact ⟨k, g, fun m => by simpa using hk (e m)⟩

end CategoryTheory.Limits.Types.FilteredColimit

namespace CommRingCat

/-- **Complete orthogonal systems of idempotents in a filtered colimit of commutative
rings descend to a stage**: given finitely many pairwise orthogonal idempotents summing
to `1` in the colimit, some stage contains pairwise orthogonal idempotents summing to
`1` that map to them. -/
theorem exists_orthogonal_idempotents_of_isColimit {J : Type*} [Category* J]
    [IsFiltered J] {D : J ⥤ CommRingCat.{v}} {c : Cocone D}
    (hc : IsColimit ((CategoryTheory.forget CommRingCat).mapCocone c))
    {ι : Type*} [Fintype ι] (e : ι → c.pt)
    (hidem : ∀ i, IsIdempotentElem (e i))
    (horth : Pairwise fun i i' => e i * e i' = 0)
    (hsum : ∑ i, e i = 1) :
    ∃ (j : J) (ε : ι → D.obj j),
      (∀ i, IsIdempotentElem (ε i)) ∧ (Pairwise fun i i' => ε i * ε i' = 0) ∧
      (∑ i, ε i = 1) ∧ ∀ i, (c.ι.app j).hom (ε i) = e i := by
  classical
  -- lift each idempotent to some stage of the colimit
  have hsurj : ∀ i, ∃ (j : J) (z : D.obj j),
      ((CategoryTheory.forget CommRingCat).mapCocone c).ι.app j z = e i :=
    fun i => Types.jointly_surjective_of_isColimit hc (e i)
  choose j₀ a₀ ha₀ using hsurj
  -- move them to a common stage
  obtain ⟨S, hS⟩ := IsFiltered.sup_objs_exists (Finset.univ.image j₀ : Finset J)
  have hhom : ∀ i, Nonempty (j₀ i ⟶ S) :=
    fun i => hS (Finset.mem_image_of_mem j₀ (Finset.mem_univ i))
  have g₀ : ∀ i, j₀ i ⟶ S := fun i => (hhom i).some
  set b : ι → D.obj S := fun i => (D.map (g₀ i)).hom (a₀ i) with hb
  have hbe : ∀ i, (c.ι.app S).hom (b i) = e i := by
    intro i
    have hw := congrArg (fun t => CommRingCat.Hom.hom t (a₀ i)) (c.w (g₀ i))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hw
    exact hw.trans (ha₀ i)
  -- the relations to descend: the pairwise products and the sum
  set lhs : (ι × ι) ⊕ Unit → D.obj S :=
    fun p => p.elim (fun q => b q.1 * b q.2) (fun _ => ∑ i, b i) with hlhs
  set rhs : (ι × ι) ⊕ Unit → D.obj S :=
    fun p => p.elim (fun q => if q.1 = q.2 then b q.1 else 0) (fun _ => 1) with hrhs
  have hrel : ∀ p, ((CategoryTheory.forget CommRingCat).mapCocone c).ι.app S (lhs p) =
      ((CategoryTheory.forget CommRingCat).mapCocone c).ι.app S (rhs p) := by
    rintro (⟨i, i'⟩ | ⟨⟩)
    · change (c.ι.app S).hom (b i * b i') = (c.ι.app S).hom (if i = i' then b i else 0)
      rcases eq_or_ne i i' with rfl | hne
      · rw [if_pos rfl, map_mul, hbe]
        exact hidem i
      · rw [if_neg hne, map_mul, hbe, hbe, map_zero]
        exact horth hne
    · change (c.ι.app S).hom (∑ i, b i) = (c.ι.app S).hom 1
      rw [map_sum, map_one, Finset.sum_congr rfl (fun i _ => hbe i)]
      exact hsum
  obtain ⟨k, g, hg⟩ := Types.FilteredColimit.exists_map_eq_of_isColimit hc lhs rhs hrel
  refine ⟨k, fun i => (D.map g).hom (b i), ?_, ?_, ?_, ?_⟩
  · intro i
    have h := hg (Sum.inl (i, i))
    change (D.map g).hom (b i) * (D.map g).hom (b i) = (D.map g).hom (b i)
    calc (D.map g).hom (b i) * (D.map g).hom (b i)
        = (D.map g).hom (b i * b i) := (map_mul _ _ _).symm
      _ = (D.map g).hom (if i = i then b i else 0) := h
      _ = (D.map g).hom (b i) := by rw [if_pos rfl]
  · intro i i' hne
    have h := hg (Sum.inl (i, i'))
    calc (D.map g).hom (b i) * (D.map g).hom (b i')
        = (D.map g).hom (b i * b i') := (map_mul _ _ _).symm
      _ = (D.map g).hom (if i = i' then b i else 0) := h
      _ = 0 := by rw [if_neg hne, map_zero]
  · have h := hg (Sum.inr ⟨⟩)
    calc ∑ i, (D.map g).hom (b i)
        = (D.map g).hom (∑ i, b i) := (map_sum _ _ _).symm
      _ = (D.map g).hom 1 := h
      _ = 1 := map_one _
  · intro i
    have hw := congrArg (fun t => CommRingCat.Hom.hom t (b i)) (c.w g)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hw
    exact hw.trans (hbe i)

end CommRingCat

namespace AlgebraicGeometry.Scheme

/-- The injections of a colimit cofan of schemes are jointly surjective. -/
lemma exists_cofan_inj_base_eq_of_isColimit {ι : Type u} {Z : ι → Scheme.{u}}
    {c : Cofan Z} (hc : IsColimit c) (v : c.pt) :
    ∃ (i : ι) (w : Z i), (c.inj i).base w = v := by
  let e : (∐ Z : Scheme.{u}) ≅ c.pt :=
    (colimit.isColimit _).coconePointUniqueUpToIso hc
  obtain ⟨⟨i, w⟩, hw⟩ := (AlgebraicGeometry.sigmaMk Z).surjective (e.inv.base v)
  refine ⟨i, w, ?_⟩
  have h1 : Sigma.ι Z i ≫ e.hom = c.inj i :=
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have h2 : (Sigma.ι Z i).base w = e.inv.base v := by
    rw [← hw, AlgebraicGeometry.sigmaMk_mk]
  have h3 := congrArg e.hom.base h2
  rw [← Scheme.Hom.comp_apply, h1] at h3
  rw [h3, ← Scheme.Hom.comp_apply, e.inv_hom_id]
  simp

namespace Etale

/-!
### Additivity of abelian sheaves on the small étale site

Sections over a finite disjoint union decompose as a finite product: the summands form
an étale cover, and the sheaf condition for this cover is exactly the product
condition since the summands are pairwise disjoint (the small étale site is finitary
extensive).
-/

section Additivity

variable {S : Scheme.{u}}

/-- The underlying scheme cofan of a colimit cofan in the small étale site is a
colimit cofan of schemes. -/
noncomputable def isColimitCofanLeft {ι : Type u} {Z : ι → S.Etale} {c : Cofan Z}
    (hc : IsColimit c) :
    IsColimit (Cofan.mk c.pt.left fun i => (c.inj i).left) :=
  isColimitCofanMkObjOfIsColimit (Etale.forget S ⋙ CategoryTheory.Over.forget S) _ _ hc

/-- The injections of a cofan in the small étale site are étale morphisms of
schemes. -/
lemma etale_cofan_inj_left {ι : Type u} {Z : ι → S.Etale} {c : Cofan Z} (i : ι) :
    Etale ((c.inj i).left) := by
  have h : Etale ((c.inj i).left ≫ c.pt.hom) := by
    rw [MorphismProperty.Over.w (c.inj i)]
    exact (Z i).prop
  exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) _ c.pt.hom c.pt.prop h

/-- The injections of a finite coproduct decomposition in the small étale site
generate a covering sieve. -/
lemma generate_ofArrows_cofanInj_mem_smallEtaleTopology {ι : Type u} {Z : ι → S.Etale}
    {c : Cofan Z} (hc : IsColimit c) :
    Sieve.generate (Presieve.ofArrows Z c.inj) ∈ S.smallEtaleTopology c.pt := by
  change _ ∈ S.smallGrothendieckTopology @Etale c.pt
  rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology,
    mem_toGrothendieck_smallPretopology]
  intro v
  obtain ⟨i, w, hw⟩ := exists_cofan_inj_base_eq_of_isColimit (isColimitCofanLeft hc) v
  exact ⟨Z i, c.inj i, w,
    ⟨Z i, 𝟙 _, c.inj i, ⟨i⟩, Category.id_comp _⟩, etale_cofan_inj_left i, hw⟩

/-- The empty sieve covers every object of the small étale site with empty underlying
scheme. -/
lemma bot_mem_smallEtaleTopology {V : S.Etale} (hV : IsEmpty V.left) :
    (⊥ : Sieve V) ∈ S.smallEtaleTopology V := by
  change _ ∈ S.smallGrothendieckTopology @Etale V
  rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology,
    mem_toGrothendieck_smallPretopology]
  exact fun v => hV.elim v

/-- The initial object of the small étale site has empty underlying scheme. -/
lemma isEmpty_initial_left : IsEmpty (⊥_ (S.Etale)).left := by
  have h : IsInitial ((Etale.forget S ⋙ CategoryTheory.Over.forget S).obj (⊥_ (S.Etale))) :=
    initialIsInitial.isInitialObj _ _
  exact (isInitial_iff_isEmpty).mp ⟨h⟩

/-- A sheaf of types on the small étale site satisfies the sheaf condition for the
empty presieve on the initial object. -/
lemma isSheafFor_ofArrows_empty (G : (S.Etale)ᵒᵖ ⥤ Type (u + 1))
    (hG : Presieve.IsSheaf S.smallEtaleTopology G) :
    (Presieve.ofArrows (X := ⊥_ (S.Etale)) Empty.elim Empty.instIsEmpty.elim).IsSheafFor
      G := by
  rw [Presieve.isSheafFor_iff_generate]
  exact hG _ (S.smallEtaleTopology.superset_covering bot_le
    (bot_mem_smallEtaleTopology isEmpty_initial_left))

/-- **Additivity of abelian sheaves on the small étale site**: an abelian sheaf takes
a finite coproduct decomposition to a product. -/
theorem preservesProduct_sheaf_obj_of_isColimit (F : Sheaf S.smallEtaleTopology Ab.{u + 1})
    {ι : Type u} [Finite ι] {Z : ι → S.Etale} {c : Cofan Z} (hc : IsColimit c) :
    PreservesLimit (Discrete.functor fun i => op (Z i)) F.obj := by
  have hG : Presieve.IsSheaf S.smallEtaleTopology
      (F.obj ⋙ CategoryTheory.forget Ab.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property)
  haveI : ∀ i, Mono (c.inj i) := fun i => FinitaryExtensive.mono_ι hc ⟨i⟩
  have hd : Pairwise fun i j =>
      IsPullback (initial.to _) (initial.to _) (c.inj i) (c.inj j) := fun i j hij =>
    FinitaryExtensive.isPullback_initial_to hc ⟨i⟩ ⟨j⟩ (by simpa using hij)
  have hF' : (Presieve.ofArrows Z c.inj).IsSheafFor
      (F.obj ⋙ CategoryTheory.forget Ab) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      (hG _ (generate_ofArrows_cofanInj_mem_smallEtaleTopology hc))
  haveI h1 : PreservesLimit (Discrete.functor fun i => op (Z i))
      (F.obj ⋙ CategoryTheory.forget Ab) :=
    Presieve.preservesProduct_of_isSheafFor _
      (isSheafFor_ofArrows_empty _ hG) initialIsInitial c hc hd hF'
  exact preservesLimit_of_reflects_of_preserves F.obj (CategoryTheory.forget Ab)

/-- The sections of an abelian sheaf over a finite disjoint union, together with the
restrictions to the summands, form a limit fan. -/
noncomputable def isLimitSheafObjFanOfIsColimit (F : Sheaf S.smallEtaleTopology Ab.{u + 1})
    {ι : Type u} [Finite ι] {Z : ι → S.Etale} {c : Cofan Z} (hc : IsColimit c) :
    IsLimit (Fan.mk (F.obj.obj (op c.pt)) fun i => F.obj.map (c.inj i).op) :=
  haveI := preservesProduct_sheaf_obj_of_isColimit F hc
  isLimitFanMkObjOfIsLimit F.obj _ _ (Cofan.IsColimit.op hc)

/-- The sections of an abelian sheaf on the small étale site over a finite disjoint
union decompose as a finite product, via the restriction maps to the summands. -/
noncomputable def sheafObjProdIsoOfIsColimit (F : Sheaf S.smallEtaleTopology Ab.{u + 1})
    {ι : Type u} [Finite ι] {Z : ι → S.Etale} {c : Cofan Z} (hc : IsColimit c) :
    F.obj.obj (op c.pt) ≅ ∏ᶜ fun i => F.obj.obj (op (Z i)) :=
  (isLimitSheafObjFanOfIsColimit F hc).conePointUniqueUpToIso (productIsProduct _)

@[reassoc (attr := simp)]
lemma sheafObjProdIsoOfIsColimit_hom_π (F : Sheaf S.smallEtaleTopology Ab.{u + 1})
    {ι : Type u} [Finite ι] {Z : ι → S.Etale} {c : Cofan Z} (hc : IsColimit c) (i : ι) :
    (sheafObjProdIsoOfIsColimit F hc).hom ≫ Pi.π _ i = F.obj.map (c.inj i).op :=
  (isLimitSheafObjFanOfIsColimit F hc).conePointUniqueUpToIso_hom_comp
    (productIsProduct _) ⟨i⟩

end Additivity

/-!
### The stalk of the pushforward at a geometric point

The pushforward along the small étale sites is precomposition with the base change
functor `Over.pullback @Etale ⊤ f`, so its stalk at a geometric point `x` is the
filtered colimit over the étale neighbourhoods `(U, u)` of `x` of the sections
`F(U ×_X Y)`. A geometric point `y` of `Y` over `x` — possibly with values in a
separably closed extension field, reached by a morphism `ε` of spectra — lifts every
étale neighbourhood of `x` to an étale neighbourhood of `y` of the base change, which
induces the canonical comparison map from the stalk of the pushforward to the stalk of
`F` at `y`.
-/

section PushforwardStalk

variable {X Y : Scheme.{u}} (f : Y ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (CommRingCat.of Ω) ⟶ X)

@[reassoc (attr := simp)]
lemma pullback_map_left_fst {U V : X.Etale} (g : U ⟶ V) :
    ((Over.pullback @Etale ⊤ f).map g).left ≫ pullback.fst V.hom f =
      pullback.fst U.hom f ≫ g.left := by
  simp [MorphismProperty.Over.pullback]

@[reassoc (attr := simp)]
lemma pullback_map_left_snd {U V : X.Etale} (g : U ⟶ V) :
    ((Over.pullback @Etale ⊤ f).map g).left ≫ pullback.snd V.hom f =
      pullback.snd U.hom f := by
  simp [MorphismProperty.Over.pullback]

/-- The pushforward along the small étale sites is evaluated at the base change,
definitionally. -/
lemma etalePushforward_obj_obj (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) (U : X.Etale) :
    ((etalePushforward f).obj F).obj.obj (op U) =
      F.obj.obj (op ((Over.pullback @Etale ⊤ f).obj U)) :=
  rfl

/-- The action of the pushforward on restriction maps is the action of `F` on the base
changed morphisms, definitionally. -/
lemma etalePushforward_obj_map (F : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    {U V : X.Etale} (g : U ⟶ V) :
    ((etalePushforward f).obj F).obj.map g.op =
      F.obj.map ((Over.pullback @Etale ⊤ f).map g).op :=
  rfl

/-- **The pushforward-stalk colimit description**: the stalk of `f_* F` at a geometric
point `x` of `X` is the colimit, over the étale neighbourhoods `(U, u)` of `x`, of the
sections of `F` over the base changes `U ×_X Y`. -/
noncomputable def pushforwardStalkIsoColimit (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    (geometricPoint x).sheafFiber.obj ((etalePushforward f).obj F) ≅
      colimit ((CategoryOfElements.π (geometricPoint x).fiber).op ⋙
        (Over.pullback @Etale ⊤ f).op ⋙ F.obj) :=
  Iso.refl _

/-- The canonical map from the sections of `F` over the base change of an étale
neighbourhood of `x` to the stalk of the pushforward at `x`. These maps form the
colimit cocone of the stalk. -/
noncomputable def toPushforwardStalk (F : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    (U : X.Etale) (u : (geometricPoint x).fiber.obj U) :
    F.obj.obj (op ((Over.pullback @Etale ⊤ f).obj U)) ⟶
      (geometricPoint x).sheafFiber.obj ((etalePushforward f).obj F) :=
  (geometricPoint x).toPresheafFiber U u ((etalePushforward f).obj F).obj

@[reassoc]
lemma toPushforwardStalk_w (F : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    {U V : X.Etale} (g : U ⟶ V) (u : (geometricPoint x).fiber.obj U) :
    F.obj.map ((Over.pullback @Etale ⊤ f).map g).op ≫ toPushforwardStalk f x F U u =
      toPushforwardStalk f x F V ((geometricPoint x).fiber.map g u) :=
  (geometricPoint x).toPresheafFiber_w g u ((etalePushforward f).obj F).obj

/-- Morphisms out of the stalk of the pushforward are determined by their composites
with the canonical maps from the étale neighbourhoods. -/
lemma pushforwardStalk_hom_ext {F : Sheaf Y.smallEtaleTopology Ab.{u + 1}}
    {T : Ab.{u + 1}}
    {φ ψ : (geometricPoint x).sheafFiber.obj ((etalePushforward f).obj F) ⟶ T}
    (h : ∀ (U : X.Etale) (u : (geometricPoint x).fiber.obj U),
      toPushforwardStalk f x F U u ≫ φ = toPushforwardStalk f x F U u ≫ ψ) : φ = ψ :=
  (geometricPoint x).presheafFiber_hom_ext h

section Lift

variable {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
  (ε : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))
  (y : Spec (CommRingCat.of Ω') ⟶ Y)

/-- A geometric point `y` of `Y` lying over `x` (via a morphism `ε` of spectra of
separably closed fields) lifts every étale neighbourhood `(U, u)` of `x` to an étale
neighbourhood of `y`: the base change `U ×_X Y` with the point `(ε ≫ u, y)`. -/
noncomputable def pullbackFiberLift (hy : y ≫ f = ε ≫ x) (U : X.Etale)
    (u : (geometricPoint x).fiber.obj U) :
    (geometricPoint y).fiber.obj ((Over.pullback @Etale ⊤ f).obj U) :=
  geometricPoint.mkFiber y
    (pullback.lift (ε ≫ u.val) y (by
      rw [Category.assoc]
      have hu : u.val ≫ U.hom = x := u.property
      rw [hu]
      exact hy.symm))
    (pullback.lift_snd _ _ _)

variable (hy : y ≫ f = ε ≫ x)

@[reassoc (attr := simp)]
lemma pullbackFiberLift_val_fst (U : X.Etale) (u : (geometricPoint x).fiber.obj U) :
    (pullbackFiberLift f x ε y hy U u).val ≫ pullback.fst U.hom f = ε ≫ u.val :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackFiberLift_val_snd (U : X.Etale) (u : (geometricPoint x).fiber.obj U) :
    (pullbackFiberLift f x ε y hy U u).val ≫ pullback.snd U.hom f = y :=
  pullback.lift_snd _ _ _

/-- The lifts of the étale neighbourhoods of `x` to étale neighbourhoods of `y` are
compatible with the transition maps. -/
lemma fiber_map_pullbackFiberLift {U V : X.Etale} (g : U ⟶ V)
    (u : (geometricPoint x).fiber.obj U) :
    (geometricPoint y).fiber.map ((Over.pullback @Etale ⊤ f).map g)
        (pullbackFiberLift f x ε y hy U u) =
      pullbackFiberLift f x ε y hy V ((geometricPoint x).fiber.map g u) := by
  refine Subtype.ext ?_
  rw [geometricPoint.fiber_map]
  change (pullback.lift (ε ≫ u.val) y _ : Spec (CommRingCat.of Ω') ⟶ pullback U.hom f) ≫
      ((Over.pullback @Etale ⊤ f).map g).left =
    pullback.lift (ε ≫ (u.val ≫ g.left)) y _
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback_map_left_fst, pullback.lift_fst_assoc, pullback.lift_fst,
      Category.assoc]
  · rw [Category.assoc, pullback_map_left_snd, pullback.lift_snd, pullback.lift_snd]

/-- **The canonical comparison map from the stalk of the pushforward at `x` to the
stalk at a geometric point `y` of `Y` over `x`**: on the étale neighbourhood `(U, u)`
of `x`, it is given by restricting to the étale neighbourhood
`(U ×_X Y, (ε ≫ u, y))` of `y`. -/
noncomputable def pushforwardStalkToStalk (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    (geometricPoint x).sheafFiber.obj ((etalePushforward f).obj F) ⟶
      (geometricPoint y).sheafFiber.obj F :=
  (geometricPoint x).presheafFiberDesc (P := ((etalePushforward f).obj F).obj)
    (fun U u => (geometricPoint y).toPresheafFiber ((Over.pullback @Etale ⊤ f).obj U)
      (pullbackFiberLift f x ε y hy U u) F.obj)
    (fun U V g u => by
      dsimp only
      rw [← fiber_map_pullbackFiberLift]
      exact (geometricPoint y).toPresheafFiber_w ((Over.pullback @Etale ⊤ f).map g)
        (pullbackFiberLift f x ε y hy U u) F.obj)

@[reassoc (attr := simp)]
lemma toPushforwardStalk_pushforwardStalkToStalk
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1})
    (U : X.Etale) (u : (geometricPoint x).fiber.obj U) :
    toPushforwardStalk f x F U u ≫ pushforwardStalkToStalk f x ε y hy F =
      (geometricPoint y).toPresheafFiber ((Over.pullback @Etale ⊤ f).obj U)
        (pullbackFiberLift f x ε y hy U u) F.obj :=
  (geometricPoint x).toPresheafFiber_presheafFiberDesc _ _ U u

/-- The comparison map from the stalk of the pushforward to the stalk at a lift is
natural in the sheaf. -/
lemma pushforwardStalkToStalk_naturality {F G : Sheaf Y.smallEtaleTopology Ab.{u + 1}}
    (φ : F ⟶ G) :
    (geometricPoint x).sheafFiber.map ((etalePushforward f).map φ) ≫
        pushforwardStalkToStalk f x ε y hy G =
      pushforwardStalkToStalk f x ε y hy F ≫ (geometricPoint y).sheafFiber.map φ := by
  refine pushforwardStalk_hom_ext f x fun U u => ?_
  have h1 : toPushforwardStalk f x F U u ≫
      (geometricPoint x).sheafFiber.map ((etalePushforward f).map φ) =
      ((sheafToPresheaf _ _).map ((etalePushforward f).map φ)).app (op U) ≫
        toPushforwardStalk f x G U u :=
    (geometricPoint x).toPresheafFiber_naturality _ U u
  have h2 : (geometricPoint y).toPresheafFiber ((Over.pullback @Etale ⊤ f).obj U)
      (pullbackFiberLift f x ε y hy U u) F.obj ≫ (geometricPoint y).sheafFiber.map φ =
      ((sheafToPresheaf _ _).map φ).app (op ((Over.pullback @Etale ⊤ f).obj U)) ≫
        (geometricPoint y).toPresheafFiber ((Over.pullback @Etale ⊤ f).obj U)
          (pullbackFiberLift f x ε y hy U u) G.obj :=
    (geometricPoint y).toPresheafFiber_naturality _ _ _
  rw [reassoc_of% h1, toPushforwardStalk_pushforwardStalkToStalk,
    toPushforwardStalk_pushforwardStalkToStalk_assoc, h2]
  rfl

end Lift

/-- The combined comparison map from the stalk of the pushforward at `x` to the finite
product of the stalks of `F` at a finite family of geometric points of `Y` over `x`.
The goal theorem (blueprint `lemma:pbc-finite`, sheaf-level half) asserts that for a
finite morphism `f` and a suitable family of lifts this map is an isomorphism. -/
noncomputable def pushforwardStalkToPiStalk {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (ε : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))
    {ι : Type u} [Finite ι]
    (y : ι → (Spec (CommRingCat.of Ω') ⟶ Y)) (hy : ∀ i, y i ≫ f = ε ≫ x)
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    (geometricPoint x).sheafFiber.obj ((etalePushforward f).obj F) ⟶
      ∏ᶜ fun i => (geometricPoint (y i)).sheafFiber.obj F :=
  Pi.lift fun i => pushforwardStalkToStalk f x ε (y i) (hy i) F

@[reassoc (attr := simp)]
lemma pushforwardStalkToPiStalk_π {Ω' : Type u} [Field Ω'] [IsSepClosed Ω']
    (ε : Spec (CommRingCat.of Ω') ⟶ Spec (CommRingCat.of Ω))
    {ι : Type u} [Finite ι]
    (y : ι → (Spec (CommRingCat.of Ω') ⟶ Y)) (hy : ∀ i, y i ≫ f = ε ≫ x)
    (F : Sheaf Y.smallEtaleTopology Ab.{u + 1}) (i : ι) :
    pushforwardStalkToPiStalk f x ε y hy F ≫ Pi.π _ i =
      pushforwardStalkToStalk f x ε (y i) (hy i) F :=
  Pi.lift_π _ _

end PushforwardStalk

end Etale

end AlgebraicGeometry.Scheme
