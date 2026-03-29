import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.Topology.JacobsonSpace

-- after `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`
theorem Algebra.HasGoingDown.specComap_surjective_of_closedPoints_subset_preimage
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.HasGoingDown R S]
    (h : closedPoints (PrimeSpectrum R) ⊆ Set.range (PrimeSpectrum.comap (algebraMap R S))) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
  rintro ⟨p, hp⟩
  obtain ⟨m, hm, hle⟩  := Ideal.exists_le_maximal _ hp.ne_top
  have : ⟨m, hm.isPrime⟩ ∈ closedPoints (PrimeSpectrum R) := by
    rwa [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  obtain ⟨⟨n, _⟩, hn⟩ := h this
  have : n.LiesOver m := ⟨PrimeSpectrum.ext_iff.mp hn.symm⟩
  obtain ⟨q, _, hq, hpq⟩ := Ideal.exists_ideal_le_liesOver_of_le n hle
  use ⟨q, hq⟩, PrimeSpectrum.ext hpq.over.symm

theorem Algebra.HasGoingDown.localization_bijective_of_subsingleton {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.HasGoingDown R S] (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime]
    [q.LiesOver p]
    (h : ∀ (p : Ideal R) [p.IsPrime], Subsingleton {q : Ideal S // q.IsPrime ∧ q.LiesOver p}) :
    IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) (Localization.AtPrime q) := by
  -- Stacks 00EA: Under going-down and uniqueness, S_q = S_{pS}
  -- BLOCKER: This requires showing that the two submonoids generate the same localization.
  -- We have: algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl (proved below)
  -- We need: IsLocalization.iff_of_le_of_exists_dvd requires proving that for every s ∈ q.primeCompl,
  --          there exists r ∈ algebraMapSubmonoid S p.primeCompl such that s ∣ r
  -- The uniqueness hypothesis should imply this, but the precise argument is unclear.
  -- Mathlib lacks: either IsLocalization.of_ge (reverse of of_le) or the divisibility lemma
  have hdisjoint : Disjoint (↑(Algebra.algebraMapSubmonoid S p.primeCompl) : Set S) (↑q : Set S) :=
    Ideal.disjoint_primeCompl_of_liesOver q p
  have hsub : Algebra.algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl := by
    intro x hx
    rw [Ideal.mem_primeCompl_iff]
    exact Set.disjoint_left.mp hdisjoint hx
  -- We need to show: IsLocalization (algebraMapSubmonoid S p.primeCompl) (Localization.AtPrime q)
  -- We have: IsLocalization q.primeCompl (Localization.AtPrime q)
  -- And: algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl
  --
  -- IsLocalization.of_le_of_exists_dvd goes from smaller to larger submonoid
  -- But we need the reverse: from larger (q.primeCompl) to smaller (algebraMapSubmonoid)
  -- This is the fundamental blocker - Mathlib lacks the reverse direction lemma
  sorry
