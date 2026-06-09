import Proetale.Algebra.WeaklyEtale
import Proetale.Algebra.WeaklyEtaleField
import Proetale.Algebra.IndEtale
import Proetale.Algebra.FaithfullyFlat
import Proetale.Algebra.HenselianLocalRing
import Proetale.Algebra.WContractible
import Proetale.Algebra.WeakDimension
import Proetale.Mathlib.RingTheory.Flat.FilteredColimit

universe u

open CategoryTheory Limits

instance {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IndEtale R S] :
    Algebra.WeaklyEtale R S := by
  obtain ⟨ι, _, _, P, hP⟩ := Algebra.IndEtale.exists_colimitPresentation (R := R) (S := S)
  have hflat (i : ι) : Module.Flat R (P.diag.obj i) := by
    haveI : Algebra.Etale R (P.diag.obj i) := hP i
    exact (inferInstance : Algebra.WeaklyEtale R (P.diag.obj i)).flat
  have hlmul (i : ι) : (Algebra.TensorProduct.lmul' R (S := P.diag.obj i)).Flat := by
    haveI : Algebra.Etale R (P.diag.obj i) := hP i
    exact Algebra.WeaklyEtale.flat_lmul' R (P.diag.obj i)
  refine ⟨?_, ?_⟩
  · -- `Module.Flat R S`: transfer the `CommAlgCat`-level presentation to `ModuleCat`.
    rw [← CommAlgCat.flat_iff (S := .of R S), CommAlgCat.flat,
        ObjectProperty.inverseImage, ← ModuleCat.ind_flat R,
        ← ObjectProperty.prop_inverseImage_iff (ModuleCat.flat.{u} R).ind]
    refine ObjectProperty.ind_inverseImage_le _ _ _ ⟨ι, ‹_›, ‹_›, P, fun i ↦ ?_⟩
    exact CommAlgCat.flat_iff.mpr (hflat i)
  · exact RingHom.Flat.of_filteredColim_lmul' P hlmul

lemma RingHom.IndEtale.weaklyEtale {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.IndEtale) :
    f.WeaklyEtale := by
  algebraize [f]
  rw [← RingHom.algebraMap_toAlgebra f, weaklyEtale_algebraMap_iff]
  infer_instance

/-!
### Scaffolding sub-lemmas for Stacks 097Y (Olivier).

The main theorem `Algebra.WeaklyEtale.exists_indEtale` (Stacks 097Y) reduces, via the
`exists_isWContractibleRing` construction already available in
`Proetale/Algebra/WContractible.lean`, to the single sub-statement
`Algebra.IndEtale.of_weaklyEtale_isWContractibleRing` below: any weakly étale algebra
over a w-contractible ring is automatically ind-étale.

That reduction is in turn proved using two further sub-lemmas, also scaffolded below:

* `Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing` — Olivier's theorem
  itself (Stacks 097Z): a local, weakly étale ring map out of a strictly henselian
  local ring is an isomorphism.
* `Algebra.WeaklyEtale.indEtale_of_isField` — Stacks 092Q: a weakly étale algebra
  over a field is ind-étale.

Each helper is left as a typed `sorry` so future iterations can attack them individually
without having to re-derive the high-level skeleton. -/

/-- (Stacks 092Q.) A weakly étale algebra over a field is ind-étale.

The Stacks proof writes `B` as a filtered colimit of its finitely generated `K`-subalgebras,
each of which turns out to be étale over `K` because `B` is absolutely flat, reduced, and
its local rings are separable algebraic extensions of `K`. -/
theorem Algebra.WeaklyEtale.indEtale_of_isField (K B : Type u) [Field K] [CommRing B]
    [Algebra K B] [Algebra.WeaklyEtale K B] :
    Algebra.IndEtale K B := by
  -- Blueprint: thm:weakly-etale-imples-ind-etale-over-fields (more-on-local-structure.tex L558).
  --
  -- Strategy (per blueprint):
  -- (a) Show `B` is absolutely flat: `K` is absolutely flat (field), and weakly étale preserves
  --     absolute flatness via `Ring.AbsolutelyFlat.of_flat_lmul'`.
  -- (b) Show `B` is reduced and every prime ideal of `B` is maximal: this follows from
  --     `Ring.AbsolutelyFlat.tfae`.
  -- (c) Show that for every prime `q` of `B`, `B_q = κ(q)` is a field separable algebraic
  --     over `K` (Stacks 092P).
  -- (d) Show every finitely generated `K`-subalgebra `A ⊂ B` is étale over `K` (using (a)-(c)).
  -- (e) Assemble: `B` is the filtered colimit of its finitely generated `K`-subalgebras, hence
  --     ind-étale by `Algebra.IndEtale.of_colimitPresentation` (or direct).
  -- ----------------------------------------------------------------
  -- Step (a): B is absolutely flat.
  haveI hKabs : Ring.AbsolutelyFlat K := .of_field K
  have hlmul : (Algebra.TensorProduct.lmul' (S := B) K).Flat :=
    Algebra.WeaklyEtale.flat_lmul' K B
  haveI hBabs : Ring.AbsolutelyFlat B :=
    Ring.AbsolutelyFlat.of_flat_lmul' (R := K) (S := B) hlmul
  -- Step (b): B is reduced and every prime of B is maximal.
  -- Use `Ring.AbsolutelyFlat.tfae` (1 ↔ 2): absolutely flat ↔ reduced ∧ every prime maximal.
  have hredmax : IsReduced B ∧ ∀ P : Ideal B, P.IsPrime → P.IsMaximal := by
    have := ((Ring.AbsolutelyFlat.tfae B).out 0 1).mp hBabs
    exact this
  haveI : IsReduced B := hredmax.1
  -- Step (b'): every local ring of B is a field.
  -- This follows from the (1 ↔ 4) part of the TFAE.
  have hloc_field : ∀ (P : Ideal B) [P.IsPrime], IsField (Localization.AtPrime P) := fun P =>
    Ring.AbsolutelyFlat.isField_of_isLocalization_prime (R := B) P (Localization.AtPrime P)
  -- Step (c-e): the remainder is the colimit construction. The mathematical proof
  -- proceeds as follows:
  -- For each finite subset s ⊂ B, let A_s = Algebra.adjoin K (s : Set B). Then:
  -- * A_s is finitely generated K-algebra, reduced (subring of reduced B).
  -- * A_s has dim 0: every prime of A_s contracts from some prime of B, whose localization
  --   is a field separable algebraic over K (Stacks 092P).
  -- * A_s, being Noetherian (fin-type over field) + dim 0 + reduced, is a product of fields,
  --   each finite separable over K. Hence A_s is étale over K (by `Algebra.Etale.iff_exists_algEquiv_prod`).
  -- * The diagram s ↦ A_s is filtered (under inclusion) and B = colim_s A_s.
  -- Both the dim-0 argument (which requires Stacks 092P) and the colimit construction
  -- (which requires nontrivial categorical infrastructure for fg subalgebras as a small diagram)
  -- are out of reach this iter. A scoped `sorry` remains.
  --
  -- Missing infrastructure (recorded for future iters):
  -- 1. Stacks 092P: a field extension L/K with `lmul' : L ⊗_K L → L` flat is separable algebraic.
  -- 2. A categorical "B = colim of fg K-subalgebras" lemma for `CommAlgCat K`.
  --
  -- The bulk of the obligation lives at the dedicated declaration
  -- `Algebra.WeaklyEtale.indEtale_field` in `Proetale/Algebra/WeaklyEtaleField.lean`,
  -- which carries the same Stacks 092Q statement and is its own (still-open) sorry.
  -- We delegate here so that any future closure there immediately closes this theorem.
  exact Algebra.WeaklyEtale.indEtale_field K B

/-- Reduction sub-lemma for Stacks 097Y. If `T` is a w-contractible ring (so every local
ring of `T` at a maximal ideal is strictly henselian) and `R → T` is weakly étale, then
`R → T` is automatically ind-étale.

This is the *only* extra ingredient — beyond the pre-existing
`exists_isWContractibleRing` and the helpers `bijective_of_isStrictlyHenselianLocalRing`,
`indEtale_of_isField` above — needed to deduce Stacks 097Y in the form used by the
Bhatt–Scholze proétale topology. -/
theorem Algebra.IndEtale.of_weaklyEtale_isWContractibleRing
    (R T : Type u) [CommRing R] [CommRing T] [Algebra R T]
    [Algebra.WeaklyEtale R T] [IsWContractibleRing T] :
    Algebra.IndEtale R T := by
  -- Blueprint: thm:weakly-etale-ind-etale (more-on-local-structure.tex L857) under the
  -- additional assumption that the target ring is w-contractible.
  --
  -- Proof sketch: the local rings of `T` at maximal ideals are strictly henselian, so
  -- Olivier (`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing`) forces the
  -- composition `R → T_m` to be a local iso onto a residue-field-trivial Henselization
  -- of `R` at the contracted prime. Globalising via the w-contractible structure of `T`
  -- (Stacks 097G + the constructible cover) writes `T` as a filtered colimit of étale
  -- `R`-algebras.
  --
  -- Partial scaffolding (iter-105+): the one structural fact directly usable from the
  -- hypotheses is that every maximal ideal of `T` has a strictly henselian localization.
  -- This is exactly the `IsWStrictlyLocalRing` part of `IsWContractibleRing T`.
  have _hSH : ∀ (m : Ideal T) [m.IsMaximal],
      IsStrictlyHenselianLocalRing (Localization.AtPrime m) := fun m _ =>
    IsWStrictlyLocalRing.isStrictlyHenselianLocalRing_localization m
  -- Step (a). Weakly étale is stable under composition: for each maximal `m` of `T`,
  -- the ring-map composition `R → T → T_m` is weakly étale because `T → T_m` is
  -- ind-Zariski (hence weakly étale) and weakly étale is closed under `comp`.
  have _hRTm : ∀ (m : Ideal T) [m.IsMaximal],
      ((algebraMap T (Localization.AtPrime m)).comp (algebraMap R T)).WeaklyEtale := by
    intro m _
    have hRT : (algebraMap R T).WeaklyEtale :=
      (RingHom.weaklyEtale_algebraMap_iff (R := R) (S := T)).mpr inferInstance
    have hTTm : (algebraMap T (Localization.AtPrime m)).WeaklyEtale :=
      (RingHom.weaklyEtale_algebraMap_iff (R := T) (S := Localization.AtPrime m)).mpr
        inferInstance
    exact RingHom.WeaklyEtale.comp hRT hTTm
  -- Step (b). The IsWLocalRing structure on `T` (carried by `IsWContractibleRing`) provides
  -- exactly the data needed for the constructible-clopen cover: every prime of `T`
  -- specializes to a unique closed point.
  have _hwl : IsWLocalRing T := inferInstance
  -- Step (c). Olivier's bijectivity helper
  -- `Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing` is poised to apply,
  -- once we identify the canonical source of the local map `R_{m.comap _} → T_m`
  -- with a strictly henselian local ring. The two remaining ingredients are:
  --   1. Strict henselization `R^{sh}_p` as a weakly étale, faithfully flat
  --      `R`-algebra at a prime `p`. Then `R^{sh}_p` is strictly henselian local,
  --      and the base change `R^{sh}_p → T_m ⊗_R R^{sh}_p` is weakly étale (Olivier
  --      applies) and local; concluding via the Olivier helper identifies
  --      `R^{sh}_p` with the localization `T_m` upto a uniqueness argument.
  --   2. A `ColimitPresentation`-shape lemma packaging the constructible-clopen
  --      cover of a w-contractible ring into a filtered diagram of étale
  --      `R`-subalgebras whose colimit is `T`. Combined with (1), this gives a
  --      `ColimitPresentation` for `T` over `R` whose stages are étale, which is
  --      the hypothesis of `Algebra.IndEtale.of_colimitPresentation`.
  -- Neither (1) nor (2) is currently in Mathlib or this project; they will be
  -- supplied by a dedicated infrastructure iteration once L3c closes upstream
  -- (PROGRESS.md "off-limits this iter" list).
  --
  -- Final step (anticipated): apply `Algebra.IndEtale.of_colimitPresentation` to the
  -- filtered diagram supplied by (2):
  --   `exact Algebra.IndEtale.of_colimitPresentation R T P (fun i => by infer_instance)`.
  sorry

/-- If `S` is a weakly étale `R`-algebra, there exists a faithfully flat, ind-étale `S`-algebra `T`
such that `T` is an ind-étale `R`-algebra.

This is the main theorem of the Bhatt–Scholze "pro-étale" paper (Stacks 097Y, due to Olivier).
The proof reduces, via the existing `exists_isWContractibleRing`, to the helper
`Algebra.IndEtale.of_weaklyEtale_isWContractibleRing`. -/
theorem Algebra.WeaklyEtale.exists_indEtale (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [WeaklyEtale R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra S T) (_ : IsScalarTower R S T),
      IndEtale S T ∧ Module.FaithfullyFlat S T ∧ IndEtale R T := by
  -- Step 1: find a w-contractible cover `T` of `S`, ind-étale and faithfully flat over `S`.
  obtain ⟨T, _, _, hIE_ST, hFF_ST, _⟩ := exists_isWContractibleRing S
  -- Step 2: equip `T` with its induced `R`-algebra structure via `R → S → T`.
  letI : Algebra R T := Algebra.compHom T (algebraMap R S)
  haveI : IsScalarTower R S T := .of_algebraMap_eq' rfl
  -- Step 3: `R → T` is weakly étale (composition of weakly étale `R → S` and ind-étale
  --         `S → T`, the latter being weakly étale via the instance at the top of this file).
  haveI : Algebra.WeaklyEtale S T := inferInstance
  haveI : Algebra.WeaklyEtale R T := Algebra.WeaklyEtale.trans R S T
  -- Step 4: weakly étale into a w-contractible ring is ind-étale.
  haveI : Algebra.IndEtale R T := Algebra.IndEtale.of_weaklyEtale_isWContractibleRing R T
  exact ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, hIE_ST, hFF_ST,
    inferInstance⟩

/-- If `S` is a weakly étale `R`-algebra, there exists a faithfully flat, ind-étale `S`-algebra `T`
such that `T` is an ind-étale `R`-algebra. -/
theorem RingHom.WeaklyEtale.exists_indEtale_comp {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.WeaklyEtale) :
    ∃ (T : Type u) (_ : CommRing T) (g : S →+* T),
      g.IndEtale ∧ g.FaithfullyFlat ∧ (g.comp f).IndEtale := by
  algebraize [f]
  obtain ⟨T, _, _, _, _, h₁, h₂, h₃⟩ := Algebra.WeaklyEtale.exists_indEtale R S
  refine ⟨T, inferInstance, algebraMap S T, ?_, ?_, ?_⟩
  · rwa [IndEtale.algebraMap_iff]
  · rwa [faithfullyFlat_algebraMap_iff]
  · rwa [← RingHom.algebraMap_toAlgebra f, ← IsScalarTower.algebraMap_eq, IndEtale.algebraMap_iff]
