import Mathlib.AlgebraicGeometry.Sites.Small
import Proetale.Mathlib.CategoryTheory.MorphismProperty.Comma

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

instance changeProp_isContinuous (hPQ : P ≤ Q) :
    (Over.changeProp S hPQ le_rfl).IsContinuous
    (smallGrothendieckTopology P) (smallGrothendieckTopology Q) where
  op_comp_isSheaf_of_types := by
    -- Mathematically: changeProp with le_rfl is essentially the identity on underlying objects,
    -- so the sheaf condition should transfer directly. However, the categorical machinery
    -- to express this cleanly is missing from Mathlib.
    --
    -- The key facts are:
    -- 1. changeProp S hPQ le_rfl ⋙ forget Q ⊤ S = forget P ⊤ S (definitionally)
    -- 2. Both topologies are induced from overGrothendieckTopology via these forgetful functors
    -- 3. Therefore the sheaf conditions should coincide
    --
    -- What's needed: infrastructure relating sheaf conditions across functors that compose
    -- to give the same induced topology.
    sorry

end AlgebraicGeometry.Scheme
