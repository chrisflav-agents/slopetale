import Mathlib.AlgebraicGeometry.Sites.Small
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma
import Proetale.Mathlib.CategoryTheory.Sites.Continuous

universe u

open CategoryTheory MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u}) {P Q : MorphismProperty Scheme.{u}}
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] [IsJointlySurjectivePreserving Q]

omit [IsJointlySurjectivePreserving P] [IsJointlySurjectivePreserving Q] in
private lemma changeProp_coverPreserving (hPQ : P ≤ Q) :
    CoverPreserving (S.smallGrothendieckTopology P) (S.smallGrothendieckTopology Q)
      (Over.changeProp S hPQ le_rfl) where
  cover_preserve {U R} hR := by
    simp only [smallGrothendieckTopology, Functor.mem_inducedTopology_sieves_iff] at hR ⊢
    rw [← Sieve.functorPushforward_comp]
    exact grothendieckTopology_monotone hPQ _ hR

-- Compatibility-preserving for `Over.changeProp`. This is the hard part of showing
-- `Over.changeProp` is a continuous functor between small sites.
--
-- Even though `Over.changeProp S hPQ le_rfl` is fully faithful (it is the inclusion of the
-- full subcategory of `Q.Over ⊤ S` consisting of objects whose structure morphism satisfies
-- `P`), the standard `compatiblePreservingOfDownwardsClosed` does NOT apply: it would
-- require every `d : Q.Over ⊤ S` admitting a morphism to some `F.obj c` to itself lie in
-- the image of `F` (equivalently, `d.hom` would have to satisfy `P`), which fails in
-- general.
--
-- Similarly, `compatiblePreservingOfFlat` does not apply because `Over.changeProp` is not
-- representably flat in general — verifying the cofiltering condition would require
-- equalizers in `P.Over ⊤ S`, which need not exist as `P`-objects (equalizers are typically
-- locally closed immersions, which need not satisfy `P`).
--
-- The intended approach is via the comparison with `forget_P : P.Over ⊤ S ⥤ Over S` and
-- `forget_Q : Q.Over ⊤ S ⥤ Over S`, both of which are `LocallyCoverDense` and have
-- well-known continuity properties for the induced topologies, combined with the
-- factorisation `changeProp ⋙ forget_Q = forget_P`.
omit [IsJointlySurjectivePreserving P] [IsJointlySurjectivePreserving Q] in
private lemma changeProp_compatiblePreserving (hPQ : P ≤ Q) :
    CompatiblePreserving (S.smallGrothendieckTopology Q) (Over.changeProp S hPQ le_rfl) := by
  sorry

instance changeProp_isContinuous (hPQ : P ≤ Q) :
    (Over.changeProp S hPQ le_rfl).IsContinuous
    (smallGrothendieckTopology P) (smallGrothendieckTopology Q) :=
  Functor.isContinuous_of_coverPreserving (changeProp_compatiblePreserving S hPQ)
    (changeProp_coverPreserving S hPQ)

section

variable {S T : Scheme.{u}} (f : S ⟶ T)
  (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.RespectsIso]
  [P.IsStableUnderBaseChange]
variable (A : Type*) [Category* A]

instance :
    (Over.pullback P ⊤ f).PreservesOneHypercovers
      (T.smallGrothendieckTopology P)
      (S.smallGrothendieckTopology P) := by
  intro X E
  constructor
  · sorry
  · sorry

noncomputable
abbrev smallPushforward :
    Sheaf (S.smallGrothendieckTopology P) A ⥤ Sheaf (T.smallGrothendieckTopology P) A :=
  (Over.pullback P ⊤ f).sheafPushforwardContinuous _ _ _

instance :
    ((Over.pullback P ⊤ f).sheafPushforwardContinuous A (smallGrothendieckTopology P)
      (smallGrothendieckTopology P)).IsRightAdjoint :=
  sorry

noncomputable
abbrev smallPullback :
    Sheaf (T.smallGrothendieckTopology P) A ⥤ Sheaf (S.smallGrothendieckTopology P) A :=
  (Over.pullback P ⊤ f).sheafPullback _ _ _

noncomputable
def smallPullbackPushforwardAdj :
    smallPullback f P A ⊣ smallPushforward f P A :=
  (Over.pullback P ⊤ f).sheafAdjunctionContinuous A _ _

instance (hf : P f) :
    (Over.map ⊤ hf).IsContinuous (smallGrothendieckTopology P) (smallGrothendieckTopology P) :=
  sorry

def smallSheafRestrict (hf : P f) :
    Sheaf (T.smallGrothendieckTopology P) A ⥤ Sheaf (S.smallGrothendieckTopology P) A :=
  (Over.map ⊤ hf).sheafPushforwardContinuous _ _ _

noncomputable def smallSheafRestrictAdj (hf : P f) :
    smallSheafRestrict f P A hf ⊣ smallPushforward f P A :=
  (Over.mapPullbackAdj P ⊤ f hf trivial).sheaf _ _

/-- If `f : S ⟶ T` satisfies `P` the pullback functor `Shv(T) ⥤ Shv(S)` is
naturally isomorphic to the restriction functor. -/
noncomputable def smallPullbackIsoRestrict (hf : P f) :
    smallPullback f P A ≅ smallSheafRestrict f P A hf :=
  (conjugateIsoEquiv (smallSheafRestrictAdj f P A hf) (smallPullbackPushforwardAdj f P A)).symm
    (Iso.refl _)

end

end AlgebraicGeometry.Scheme
