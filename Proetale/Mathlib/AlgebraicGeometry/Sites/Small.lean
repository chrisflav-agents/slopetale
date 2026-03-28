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
    intro G X R hR xx hxx
    set F : P.Over ⊤ S ⥤ Q.Over ⊤ S := Over.changeProp S hPQ le_rfl
    have hR' : R.functorPushforward F ∈ (S.smallGrothendieckTopology Q) (F.obj X) :=
      (changeProp_coverPreserving S hPQ).cover_preserve hR
    have hGsheaf : Presieve.IsSheaf (S.smallGrothendieckTopology Q) G.val :=
      (isSheaf_iff_isSheaf_of_type _ G.val).1 G.cond
    have hSF : Presieve.IsSheafFor G.val (R.functorPushforward F).arrows :=
      hGsheaf _ hR'
    -- Key fact: changeProp with le_rfl acts as identity on morphisms
    have key : ∀ {Y Z : P.Over ⊤ S} (g : Y ⟶ Z), (F.map g).hom = g.hom := fun _ => rfl
    -- Construct a family on the pushforward sieve by transporting xx
    let yy : Presieve.FamilyOfElements G.val (R.functorPushforward F).arrows := fun Y f hf =>
      let s := Presieve.getFunctorPushforwardStructure hf
      -- xx s.premap s.cover : G.val.obj (op (F.obj s.preobj))
      -- We need: G.val.obj (op Y)
      -- We have s.lift : Y ⟶ F.obj s.preobj
      G.val.map s.lift.op (xx s.premap s.cover)
    -- Show this family is compatible
    have hyy : yy.Compatible := by
      intro Y₁ Y₂ W g₁ g₂ f₁ f₂ hf₁ hf₂ comm
      dsimp only [yy]
      let s₁ := Presieve.getFunctorPushforwardStructure hf₁
      let s₂ := Presieve.getFunctorPushforwardStructure hf₂
      -- BLOCKED: Need to relate G.val.map to (F.op ⋙ G.val).map to use hxx
      -- The issue is that xx s.premap s.cover : (F.op ⋙ G.val).obj (op s.preobj)
      -- but the goal has G.val.map, not (F.op ⋙ G.val).map
      -- Missing: lemmas about how compatible families transform under functorPushforward
      sorry
    -- Get amalgamation from sheaf condition on G
    obtain ⟨t, ht, ht_unique⟩ := hSF yy hyy
    -- Show t works for xx
    refine ⟨t, ?_, ?_⟩
    · -- Show t is an amalgamation for xx
      intro Y f hf
      -- Need: (F.op ⋙ G.val).map f.op t = xx f hf
      -- Have: yy is amalgamation, yy uses xx values
      sorry
    · -- Show uniqueness
      intro y hy
      -- Need to show y = t using ht_unique
      sorry

end AlgebraicGeometry.Scheme
