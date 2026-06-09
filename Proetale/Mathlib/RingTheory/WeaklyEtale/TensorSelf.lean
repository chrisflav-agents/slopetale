/-
Copyright (c) 2026 The slopetale Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Proetale.Algebra.WeaklyEtaleField
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Reducedness of `L ⊗[K] L` for weakly étale field extensions

This file isolates the single fact about `L ⊗[K] L` (for a weakly étale extension
`K → L` of fields) that both
`Proetale/Mathlib/RingTheory/WeaklyEtale/Subalgebra.lean` and
`Proetale/Mathlib/RingTheory/WeaklyEtale/FieldExtension.lean` consume:
the tensor square is reduced.

Placing this instance here breaks the otherwise-circular import between
`Subalgebra.lean` and `FieldExtension.lean`.
-/

universe u

open scoped TensorProduct

namespace Algebra.WeaklyEtale

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- If `L / K` is weakly étale between fields, then `L ⊗[K] L` is reduced.

This is the special-field version: derived from `Ring.AbsolutelyFlat (L ⊗[K] L)` via
the TFAE result `Ring.AbsolutelyFlat.tfae` (absolutely flat ⇒ reduced + all primes
maximal). -/
instance isReduced_tensor_self [Algebra.WeaklyEtale K L] :
    IsReduced (L ⊗[K] L) := by
  haveI : Ring.AbsolutelyFlat (L ⊗[K] L) := absolutelyFlat_tensor_self K L
  refine isReduced_ofLocalizationMaximal _ fun P hP ↦ ?_
  haveI : P.IsPrime := hP.isPrime
  haveI hfld : IsField (Localization.AtPrime P) :=
    Ring.AbsolutelyFlat.isField_of_isLocalization_prime
      (R := L ⊗[K] L) P (Localization.AtPrime P)
  letI := hfld.toField
  infer_instance

end Algebra.WeaklyEtale
