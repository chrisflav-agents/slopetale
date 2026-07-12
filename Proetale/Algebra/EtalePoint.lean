/-
Copyright (c) 2026 The Slopetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Points of étale algebras valued in separably closed fields

We show that a nontrivial étale algebra over a separably closed field `K` admits a
`K`-algebra homomorphism to `K`, and more generally that a ring homomorphism `A → Ω`
into a separably closed field extends to any étale `A`-algebra `B` admitting a prime
lying over the kernel of `A → Ω`.
-/

universe u

open scoped TensorProduct

/-- A nontrivial étale algebra over a separably closed field admits an algebra
homomorphism to the field. -/
theorem Algebra.Etale.exists_algHom_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    (A : Type u) [CommRing A] [Algebra K A] [Algebra.Etale K A] [Nontrivial A] :
    Nonempty (A →ₐ[K] K) := by
  obtain ⟨I, hIfin, Ai, hfield, halg, e, hAi⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp ‹_›
  letI := hfield
  letI := halg
  cases isEmpty_or_nonempty I with
  | inl hI =>
    haveI := hI
    exact absurd e.toEquiv.subsingleton (not_subsingleton A)
  | inr hI =>
    obtain ⟨i⟩ := hI
    haveI := (hAi i).2
    exact ⟨(IsSepClosed.lift (K := K) (M := K) (L := Ai i)).comp
      ((Pi.evalAlgHom K Ai i).comp e.toAlgHom)⟩

/-- Let `A → Ω` be a ring homomorphism into a separably closed field, and let `B` be an
étale `A`-algebra admitting a prime over the kernel of `A → Ω`. Then the map to `Ω`
extends to `B`. -/
theorem Algebra.Etale.exists_algHom_to_isSepClosed {A Ω : Type u} [CommRing A] [Field Ω]
    [IsSepClosed Ω] [Algebra A Ω] (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.Etale A B]
    (h : ∃ q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω)) :
    Nonempty (B →ₐ[A] Ω) := by
  obtain ⟨q, hq, hq'⟩ := h
  set p : Ideal A := RingHom.ker (algebraMap A Ω) with hp_def
  haveI hp : p.IsPrime := RingHom.ker_isPrime _
  -- The residue field `κ(p)` embeds into `Ω`.
  have hinj : Function.Injective (RingHom.kerLift (algebraMap A Ω)) :=
    RingHom.kerLift_injective _
  letI : Algebra p.ResidueField Ω := (IsFractionRing.lift (A := A ⧸ p) hinj).toAlgebra
  haveI : IsScalarTower A p.ResidueField Ω := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [RingHom.algebraMap_toAlgebra,
      IsScalarTower.algebraMap_apply A (A ⧸ p) p.ResidueField,
      IsFractionRing.lift_algebraMap]
    exact (RingHom.kerLift_mk (algebraMap A Ω) a).symm
  -- The fiber ring `κ(p) ⊗[A] B` is nontrivial since `q` lies over `p`.
  haveI : Nontrivial (p.Fiber B) := by
    have Q : PrimeSpectrum (p.Fiber B) :=
      PrimeSpectrum.primesOverOrderIsoFiber A B p ⟨q, hq, ⟨hq'.symm⟩⟩
    rw [← not_subsingleton_iff_nontrivial, ← PrimeSpectrum.isEmpty_iff_subsingleton]
    exact fun hempty => hempty.false Q
  -- Hence `Ω ⊗[A] B` is nontrivial, by faithful flatness of `Ω` over `κ(p)`.
  haveI : Module.FaithfullyFlat p.ResidueField Ω := inferInstance
  haveI : Nontrivial (Ω ⊗[p.ResidueField] (p.ResidueField ⊗[A] B)) := inferInstance
  haveI : Nontrivial (Ω ⊗[A] B) :=
    (Algebra.TensorProduct.cancelBaseChange A p.ResidueField p.ResidueField
      Ω B).symm.toEquiv.nontrivial
  -- `Ω ⊗[A] B` is étale over `Ω`, so it admits an `Ω`-point.
  haveI : Algebra.Etale Ω (Ω ⊗[A] B) := inferInstance
  obtain ⟨φ⟩ := Algebra.Etale.exists_algHom_of_isSepClosed (K := Ω) (Ω ⊗[A] B)
  exact ⟨(φ.restrictScalars A).comp Algebra.TensorProduct.includeRight⟩
