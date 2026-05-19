import Proetale.Algebra.WeaklyEtale
import Proetale.Algebra.IndEtale
import Proetale.Algebra.FaithfullyFlat
import Proetale.Mathlib.RingTheory.Flat.FilteredColimit

universe u

open CategoryTheory Limits TensorProduct

instance {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IndEtale R S] :
    Algebra.WeaklyEtale R S := by
  obtain ⟨ι, hcat, hfilt, P, hP⟩ :=
    Algebra.IndEtale.exists_colimitPresentation (R := R) (S := S)
  letI := hcat; letI := hfilt
  refine ⟨?_, ?_⟩
  · -- Flatness of `R → S`: filtered colimit of flat modules is flat.
    -- Lift the colimit presentation through the forgetful functor to `ModuleCat`.
    have hflat (i : ι) : Module.Flat R (P.diag.obj i) := by
      haveI : Algebra.Etale R (P.diag.obj i) := hP i
      infer_instance
    -- Convert `P` to a `ModuleCat`-level colimit presentation via the forgetful chain.
    -- We use the established pattern from `CommAlgCat.faithfullyFlat_of_colimitPresentation`.
    rw [← CommAlgCat.flat_iff (S := CommAlgCat.of R S), CommAlgCat.flat,
        ObjectProperty.inverseImage, ← ModuleCat.ind_flat R,
        ← ObjectProperty.prop_inverseImage_iff (ModuleCat.flat.{u} R).ind]
    refine ObjectProperty.ind_inverseImage_le _ _ _ ⟨ι, ‹_›, ‹_›, P, fun i ↦ ?_⟩
    exact hflat i
  · -- Flatness of multiplication `lmul' : S ⊗[R] S → S`.
    --
    -- Strategy (round 2, May 2026): factor `lmul'_S` through the lift maps
    --   `S ⊗[R] S → S ⊗[Sᵢ] S → S`,
    -- where the first arrow is `Algebra.TensorProduct.lift` (the base-change comparison),
    -- flat by `RingHom.Flat.lift_includeLeft_includeRight` applied to the weakly étale
    -- `R → Sᵢ`, and the second arrow is `lmul'_{S/Sᵢ}`. Each `S ⊗[Sᵢ] S` is, in
    -- `CommRingCat`, the pushout of `(Sᵢ → S, Sᵢ → S)` (both being the cocone leg).
    -- Since filtered colimits commute with finite colimits (pushouts), and
    -- `colim Sᵢ = S` is the identity at the limit, we have
    --   `colim_i (S ⊗[Sᵢ] S) = pushout(id_S, id_S) = S`,
    -- with the cocone arrows `S ⊗[Sᵢ] S → S` given by multiplication. Applying
    -- `RingHom.Flat.of_isColimit` with `D.obj i = S ⊗[Sᵢ] S` closes the goal.
    -- Each `R → P.diag.obj i` is étale, so weakly étale.
    have hweakly (i : ι) : Algebra.WeaklyEtale R (P.diag.obj i) :=
      haveI : Algebra.Etale R (P.diag.obj i) := hP i
      inferInstance
    -- Each `lmul'_i : Sᵢ ⊗[R] Sᵢ → Sᵢ` is flat (definition of weakly étale, Stacks 092B).
    have hflat_lmul (i : ι) :
        (Algebra.TensorProduct.lmul' (S := P.diag.obj i) R).Flat := by
      haveI := hweakly i
      exact Algebra.WeaklyEtale.flat_lmul' R (P.diag.obj i)
    -- Underlying ring diagram and cocone with apex `S` (in `CommRingCat`).
    let F : ι ⥤ CommRingCat.{u} := P.diag ⋙ forget₂ (CommAlgCat R) CommRingCat
    let SR : CommRingCat.{u} := CommRingCat.of S
    -- `pi.app i : F.obj i ⟶ SR` is the cocone leg `Sᵢ → S` (after forget₂).
    let pi : F ⟶ (Functor.const ι).obj SR :=
      Functor.whiskerRight P.ι (forget₂ (CommAlgCat R) CommRingCat)
    -- `S` is the filtered colimit of `F` in `CommRingCat` (forget₂ preserves filtered colims
    -- between `CommAlgCat R` and `CommRingCat`).
    have hF : IsColimit (Cocone.mk SR pi) :=
      isColimitOfPreserves (forget₂ (CommAlgCat R) CommRingCat) P.isColimit
    -- Verify the per-stage flat lift: for each `i`, the base-change comparison
    -- `S ⊗[R] S → S ⊗[P.diag.obj i] S` is flat. The `P.diag.obj i`-algebra structure
    -- on `S` comes from the cocone leg `P.ι.app i`. This invokes
    -- `RingHom.Flat.lift_includeLeft_includeRight` on `hflat_lmul i`.
    have hflat_t (i : ι) :
        letI : Algebra (P.diag.obj i) S := (P.ι.app i).hom.toAlgebra
        haveI : IsScalarTower R (P.diag.obj i) S :=
          .of_algebraMap_eq fun r => ((P.ι.app i).hom.commutes r).symm
        (Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
            (Algebra.TensorProduct.includeRight.restrictScalars R)
            (fun _ _ ↦ .all _ _) :
          S ⊗[R] S →ₐ[S] S ⊗[P.diag.obj i] S).Flat := by
      letI : Algebra (P.diag.obj i) S := (P.ι.app i).hom.toAlgebra
      letI : IsScalarTower R (P.diag.obj i) S :=
        .of_algebraMap_eq fun r => ((P.ι.app i).hom.commutes r).symm
      exact RingHom.Flat.lift_includeLeft_includeRight S S (hflat_lmul i)
    -- Round 4 progress: the helper lemma `RingHom.Flat.of_filteredColim_lmul'` has been
    -- placed in `Proetale/Mathlib/RingTheory/Flat/FilteredColimit.lean`. Its proof reduces
    -- to constructing an `IsColimit` witness for the diagonal pushout diagram `i ↦
    -- pushout(pi.app i, pi.app i)` in `CommRingCat`, which is itself the only remaining
    -- mathematical gap (see that file's docstring for the strategy). The per-stage
    -- data (`hF`, `hflat_t`) constructed above is what the helper consumes; we keep it
    -- here as a reference, even though the final application only needs `P` and
    -- `hflat_lmul`.
    let _ := hF
    let _ := hflat_t
    exact RingHom.Flat.of_filteredColim_lmul' P hflat_lmul

lemma RingHom.IndEtale.weaklyEtale {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.IndEtale) :
    f.WeaklyEtale := by
  algebraize [f]
  rw [← RingHom.algebraMap_toAlgebra f, weaklyEtale_algebraMap_iff]
  infer_instance

/-- If `S` is a weakly étale `R`-algebra, there exists a faithfully flat, ind-étale `S`-algebra `T`
such that `T` is an ind-étale `R`-algebra.

This is the main theorem of the Bhatt–Scholze "pro-étale" paper (Stacks 097Y, due to Olivier).
The blueprint marks this proof as TBA. The proof requires:
  (1) Olivier's theorem (Stacks 097Z): for a Henselian local ring `A` with separably closed
      residue field, any local weakly étale `A → B` is an isomorphism.
  (2) "Weakly étale over a field is ind-étale" (Stacks 092Q).
  (3) "Bijective on stalks of ind-Zariski covers" (used in the construction of `T`).
The strategy is to construct `T` as the colimit of a directed system of ind-étale `S`-algebras
that "trivialize" all local henselian-strictly-local data of `S`. This is significant work
beyond the current infrastructure. -/
theorem Algebra.WeaklyEtale.exists_indEtale (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [WeaklyEtale R S] :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra S T) (_ : IsScalarTower R S T),
      IndEtale S T ∧ Module.FaithfullyFlat S T ∧ IndEtale R T :=
  sorry

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
