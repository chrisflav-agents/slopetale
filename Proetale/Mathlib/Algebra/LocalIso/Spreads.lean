/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHomProperties
import Proetale.Algebra.LocalIso
import Proetale.Mathlib.CategoryTheory.MorphismProperty.IndSpreads

/-!
# Spreading of local isomorphisms

This file develops descent (`PreIndSpreads`) and base change stability for the
property `RingHom.IsLocalIso`. The main results are:

- `Algebra.IsLocalIso.baseChange`: base change of a local iso is local iso.
- `(RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderCobaseChange`: the
  categorical form of base change stability.
- `(RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderComposition`: from
  `Algebra.IsLocalIso.trans`.
- `PreIndSpreads (RingHom.toMorphismProperty RingHom.IsLocalIso)`: the spreading
  lemma — currently `sorry`.

These instances allow `Algebra.IndZariski.trans` to be proved by appealing to
`MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads`. The strategies
for each are documented above each declaration.
-/

universe u

open CategoryTheory Limits TensorProduct

namespace Algebra.IsLocalIso

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    {T : Type u} [CommRing T] [Algebra R T]

/-- Base change of a local isomorphism is a local isomorphism.

Strategy: cover `T` by `{g_α : T}` with `R → T[1/g_α]` standard open immersion.
For each `α`, the base change `(S ⊗[R] T)[1/(1 ⊗ g_α)] ≅ S ⊗[R] T[1/g_α]` is a
standard open immersion of `S` (base change of `IsStandardOpenImmersion`).
Since the `1 ⊗ g_α` span the top ideal of `S ⊗[R] T`, this gives the local iso
structure on `S → S ⊗[R] T`.

Currently `sorry`. -/
instance baseChange [Algebra.IsLocalIso R T] :
    Algebra.IsLocalIso S (S ⊗[R] T) := by
  sorry

end Algebra.IsLocalIso

namespace CategoryTheory.MorphismProperty

open CategoryTheory Limits

/-- The morphism property `RingHom.IsLocalIso` is stable under cobase change.

Strategy: convert the pushout square in `CommRingCat` to an `Algebra.IsPushout`,
then use `Algebra.IsLocalIso.baseChange` to transport the local iso structure
through the iso `A' ⊗[A] B ≃ B'`.

Currently `sorry` (depends on `Algebra.IsLocalIso.baseChange`). -/
instance isLocalIso_isStableUnderCobaseChange :
    (RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderCobaseChange where
  of_isPushout {A A' B B'} {f g f' g'} sq hf := by
    sorry

/-- The morphism property `RingHom.IsLocalIso` is stable under composition. This
follows from `Algebra.IsLocalIso.trans`. -/
instance isLocalIso_isStableUnderComposition :
    (RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderComposition where
  comp_mem f g hf hg := by
    show (g.hom.comp f.hom).IsLocalIso
    exact hg.comp hf

/-- **The spreading lemma for local isomorphisms.** If `S = colim D_j` is a filtered
colimit of commutative rings and `f : S → T` is a local isomorphism, then `f` descends
to a local isomorphism `D_j → T'` at some stage `j` with `T ≅ S ⊗_{D_j} T'`.

This is the analogue of `Algebra.Etale.exists_subalgebra_fg` for `IsLocalIso`. The
strategy: write `T = S[1/h_1, ..., 1/h_n] / (relations)` via the finite cover from
`Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top`. Each `h_i` and each
relation can be lifted to some stage `j` of the filtered colimit; the resulting
`D_j`-algebra is a local iso of `D_j` and base-changes to `T` over `S`.

Currently `sorry`. -/
instance isLocalIso_preIndSpreads :
    MorphismProperty.PreIndSpreads.{u}
      (RingHom.toMorphismProperty RingHom.IsLocalIso) := by
  sorry

end CategoryTheory.MorphismProperty
