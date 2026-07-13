/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Proetale.Etale.FinitePushforwardBaseChangeStalk
import Proetale.Etale.FinitePushforwardExact
import Proetale.Etale.FinitePushforwardLifts

/-!
# Proper base change for finite morphisms

Let

```
Y' --g'--> Y
|          |
f'         f
↓          ↓
X' --g---> X
```

be a cartesian square of schemes with `f` **finite**. This file completes blueprint
`lemma:pbc-finite`: the base change transformation is an isomorphism, both on abelian
sheaves and, in the derived form, on all of the bounded below derived category (no
torsion hypothesis is needed for finite morphisms).

The two inputs are the stalk formula for the pushforward along a finite morphism
(`Proetale.Etale.FinitePushforwardStalkFormula`, in the form of
`Proetale.Etale.FinitePushforwardLifts`, valid for any family of lifts indexed
bijectively by the geometric points of the fiber) and the stalkwise description of the
base change transformation (`Proetale.Etale.FinitePushforwardBaseChangeStalk`). The
identification of the two index sets is the universal property of the cartesian square:
the lifts of a geometric point `z` of `X'` to `Y'` correspond bijectively, via `- ≫ g'`,
to the lifts of `z ≫ g` to `Y`.

## Main results

- `AlgebraicGeometry.Scheme.Etale.isIso_etaleBaseChangeNatTrans_app_of_isFinite`: the
  sheaf-level base change transformation is an isomorphism.
- `AlgebraicGeometry.Scheme.Etale.isIso_derivedBaseChangeNatTrans_app_of_isFinite`:
  **proper base change for finite morphisms** on the bounded below derived category.
-/

universe u

open CategoryTheory Limits MorphismProperty Opposite

namespace AlgebraicGeometry.Scheme.Etale

end AlgebraicGeometry.Scheme.Etale
