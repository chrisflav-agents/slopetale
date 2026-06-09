/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Algebra.WeaklyEtaleField
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Reducedness of `L ⊗[K] L` for weakly étale field extensions

If `K → L` is a weakly étale extension between fields, then `L ⊗[K] L` is reduced.

This is the field-to-field specialisation of the `IsReduced` half of
[Stacks 092I (2)](https://stacks.math.columbia.edu/tag/092I): a weakly étale
algebra over a reduced ring is reduced. It follows from
`Algebra.WeaklyEtale.absolutelyFlat_tensor_self` via the local-rings-are-fields
characterisation `Ring.AbsolutelyFlat.isField_of_isLocalization_prime` and
`isReduced_ofLocalizationMaximal`.
-/

universe u

open scoped TensorProduct

namespace Algebra.WeaklyEtale

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- If `K → L` is a weakly étale extension of fields, then `L ⊗[K] L` is reduced.

Field-to-field specialisation of [Stacks 092I (2)](https://stacks.math.columbia.edu/tag/092I).
Derived from `Ring.AbsolutelyFlat (L ⊗[K] L)` via `Ring.AbsolutelyFlat.tfae`
(every prime localisation of an absolutely flat ring is a field, hence reduced). -/
instance isReduced_tensor_self [Algebra.WeaklyEtale K L] :
    IsReduced (L ⊗[K] L) := by
  refine isReduced_ofLocalizationMaximal _ fun P hP ↦ ?_
  haveI : P.IsPrime := hP.isPrime
  haveI : IsField (Localization.AtPrime P) :=
    Ring.AbsolutelyFlat.isField_of_isLocalization_prime
      (R := L ⊗[K] L) P (Localization.AtPrime P)
  letI := ‹IsField (Localization.AtPrime P)›.toField
  infer_instance

end Algebra.WeaklyEtale
