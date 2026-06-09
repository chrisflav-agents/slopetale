# Analogy: build a ring map B → C from a continuous Spec C → Spec B over Spec A under stalk-bijection hypotheses

## Mode
cross-domain-inspiration

## Slug
ssp-redesign

## Iteration
154

## Structural problem (abstracted)

Given two ring objects `B`, `C` over a base `A` whose induced maps on
*stalks* are bijective, and a continuous map `φ : Spec C → Spec B` over
`Spec A`, construct a global morphism `f : B → C` in the algebraic
category whose induced spectral map is `φ` and which is `A`-linear. The
shape is "global-from-local synthesis": a *continuous* map on spectra
plus *pointwise* (stalkwise) algebraic data must lift to a *global*
algebraic morphism whose pointwise behaviour matches.

## Failed approaches (from directive)

- **SSP-spine (iter-145–149)**: build `q⁻¹ 𝒪_{Spec A} ≅ 𝒪_{Spec B}` as a
  sheaf iso. Stalled on `Sheaf.pullback`/`Cat`-valued vs `CommRingCat`-valued
  plumbing; the `sheafifyStalkIso_concrete` bridge existed but the route
  still required ~150 LOC of `Sheaf.pullback` infrastructure the project
  didn't have.
- **SSP-bypass (iter-150–153)**: amalgamate per-prime sections via
  `IsSheaf.amalgamate` + `StructureSheaf.globalSectionsIso` on the
  basic-open cover `{D(den p)}`. Mathematically broken — iter-153 counter-
  example (`B = ℚ[X]`, `C = ℚ[X,Y]`, primes `(X,Y)` vs `(X,Y−1)` with
  `α p_1 : X ↦ Y`, `α p_2 : X ↦ X`) shows the per-prime local-hom data
  alone is too weak: it does not encode that the `α_p`'s come from a
  single global construction.

## Analogues found

Ranked by porting cost (lowest first).

---

### Analogue 1: `AlgebraicGeometry.Spec.preimage` via `LocallyRingedSpace.Hom.mk` (FullyFaithful Spec)

- **Domain**: algebraic geometry — the `Γ ⊣ Spec` adjunction at the
  `LocallyRingedSpace` level, the very theorem Stacks 096L is the
  identifies-local-rings refinement of.
- **Same structural problem there**: `Hom_{LRS}(Spec C, Spec B) ≃
  Hom_{CRing}(B, C)`. Given a `LocallyRingedSpace.Hom (Spec C) (Spec B)`,
  `Spec.preimage` produces the ring hom; the adjunction round-trip
  identity `Spec.map_preimage` certifies it. The mathlib citation:
  - `AlgebraicGeometry.Spec.fullyFaithfulToLocallyRingedSpace`
    (`Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`):
    `AlgebraicGeometry.Spec.toLocallyRingedSpace.FullyFaithful`.
  - `AlgebraicGeometry.Spec.preimage`
    (`Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean`):
    `(Spec S ⟶ Spec R) → (R ⟶ S)`.
  - `AlgebraicGeometry.Spec.map_preimage`: `Spec.map (Spec.preimage f) = f`.
  - `AlgebraicGeometry.LocallyRingedSpace.homMk`
    (`Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean`): smart
    constructor that takes a `SheafedSpace.Hom` and an autoParam-defaulted
    locality witness on stalk maps, returning an `LRS.Hom`.
  - `AlgebraicGeometry.Scheme.arrowStalkMapSpecIso`
    (`Mathlib/AlgebraicGeometry/AffineScheme.lean`): characterises the
    stalk map of `Spec.map f` at `p` as (iso-isomorphic to)
    `Localization.localRingHom (comap p) p f rfl` — the very form the
    project's `BijectiveOnStalks` API produces.
- **Technique**: package the four data fields of a `PresheafedSpace.Hom`
  (`base : C(Spec C, Spec B)` and `c : 𝒪_{Spec B} ⟶ φ_* 𝒪_{Spec C}` of
  sheaves of commutative rings) plus stalk-IsLocalHom. The `base` is
  `φ.toContinuousMap`; the `c` morphism is the only nontrivial datum.
  Once built, `LocallyRingedSpace.homMk` discharges the LRS locality
  via the autoParam `infer_instance`, since each stalk map will
  factor through `Localization.localRingHom`'s of the project's
  `BijectiveOnStalks` chain (a composition of local ring homs).
- **Mapping to project**: directly construct
  ```
  Φ : Spec.toLocallyRingedSpace.obj (op (.of C)) ⟶
      Spec.toLocallyRingedSpace.obj (op (.of B))
  ```
  with `Φ.base = φ.toContinuousMap`. Then `f := Spec.preimage (Scheme.Hom.mk Φ)`
  gives `f : B →+* C`. A-linearity follows because the over-Spec-A
  structure of `Φ` (provable from `φ.comp_comap_algebraMap`) certifies
  `f.comp (algebraMap A B) = algebraMap A C`. The match
  `continuousMap_of_algHom f = φ` follows from `Spec.map_preimage` + the
  fact that `(Spec.map f).base = PrimeSpectrum.comap f` (cf.
  `AlgebraicGeometry.Spec.map_apply`).
- **Porting cost**: MEDIUM-HIGH. The construction of the `c` component
  (sheaf morphism on `Spec B`'s structure sheaf) is the real obstruction
  — this is the same `q⁻¹ 𝒪_{Spec A} ≅ 𝒪_{Spec Z}` content the SSP-spine
  attacked. *But* the LRS route does **not** require constructing the
  inverse-image sheaf as a separate object: the c-component can be
  defined section-by-section on basic opens `D(s) ⊆ Spec B` using
  - `AlgebraicGeometry.StructureSheaf.IsAffineOpen.isLocalization_of_eq_basicOpen`
    (`Γ(D(s)) ≅ B[s^{-1}]`) and the dual on `Spec C`,
  - `AlgebraicGeometry.StructureSheaf.toOpen_comp_comap_assoc`
    (compatibility between `toOpen` and a candidate comap),
  - the per-stalk maps from `BijectiveOnStalks` (composed
    `B_q ≅ A_{q∩A} = A_{p∩A} ≅ C_p`)

  giving a basic-open description of `c`. This bypasses the `Sheaf.pullback`
  / `Cat`-valued plumbing that stalled iter-145–149. Estimated LOC:
  100–200 — substantial but bounded, and the helper
  `AlgebraicGeometry.Scheme.arrowStalkMapSpecIso` directly bridges the
  per-stalk arithmetic to the `Spec.map` representation needed for
  `Spec.preimage` to round-trip cleanly.
- **Verdict**: **ANALOGUE_FOUND**. This is the principled algebraic-
  geometry route; it terminates because `Spec` is fully faithful into LRS
  by Mathlib's `fullyFaithfulToLocallyRingedSpace`. The bottleneck is
  *concrete c-component construction*, not abstract sheaf machinery.

---

### Analogue 2: `IsOpenImmersion.of_stalk_iso` / open-immersion-from-stalk-iso pattern

- **Domain**: algebraic geometry — open immersions characterised by
  topological + stalkwise data.
- **Same structural problem there**: given `f : X ⟶ Y` of schemes with
  underlying `f.base` an open embedding and `Scheme.Hom.stalkMap f x`
  an iso for every `x ∈ X`, conclude `IsOpenImmersion f`.
  - `AlgebraicGeometry.IsOpenImmersion.of_stalk_iso`
    (`Mathlib/AlgebraicGeometry/OpenImmersion.lean`):
    Topology.IsOpenEmbedding + per-stalk IsIso → `IsOpenImmersion`.
  - `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.stalk_iso`
    (`Mathlib/Geometry/RingedSpace/OpenImmersion.lean`).
- **Technique**: pre-supposes a `Scheme.Hom f` already exists; *adds*
  the stalk-iso property as a side condition. The interesting fragment
  for us is the dual direction: it shows Mathlib's design philosophy is
  "construct the morphism first, then certify the stalk property". The
  morphism construction is not factored out as a standalone lemma.
- **Mapping to project**: insufficient on its own — the project precisely
  lacks the `Scheme.Hom`. But it confirms the LRS-Hom shape is the
  canonical Mathlib carrier for "continuous map + stalk-level algebraic
  iso", reinforcing Analogue 1's structural choice.
- **Porting cost**: N/A — the technique requires the morphism already
  exists.
- **Verdict**: **PARTIAL_ANALOGUE**. Useful as a design-shape check
  confirming Analogue 1's route, not as an independent construction.

---

### Analogue 3: Gelfand duality — `WeakDual.CharacterSpace.compContinuousMap`

- **Domain**: functional analysis — C\* algebras and compact Hausdorff
  spaces. `Mathlib.Analysis.CStarAlgebra.GelfandDuality` realises the
  equivalence `CompHaus^op ≃ CommUnitalC*Algebra`. Continuous maps
  between character spaces are pulled back to star-algebra homs.
- **Same structural problem there**: given a continuous map
  `φ : X → Y` between *character spaces* (compact Hausdorff), produce a
  star-algebra hom `B → C` where `B = C(Y, ℂ)`, `C = C(X, ℂ)`. The
  cited construction is `WeakDual.CharacterSpace.compContinuousMap`
  (`Mathlib/Analysis/CStarAlgebra/GelfandDuality.lean`) and the more
  primitive `ContinuousMap.compRightAlgHom`
  (`Mathlib/Topology/ContinuousMap/Algebra.lean`) which sends
  `φ : C(α, β) → AlgHom_R(C(β, A), C(α, A))` by precomposition.
- **Technique**: the algebra hom is **literally precomposition with
  φ on global functions** — `f(g) = g ∘ φ`. No sheaf gluing, no stalk
  bookkeeping. Globally trivial because `B` and `C` are by construction
  function algebras, so the pullback is set-theoretic.
- **Mapping to project**: structurally identical (both are "continuous
  map on spectra ⇒ algebra hom"), but **the technique does not port**
  because `B`-as-affine-ring is NOT a function algebra on `Spec B` in
  the same way that `C(Y, ℂ)` is the C\*-algebra of `Y`. The "sections"
  here are *fractions*, not functions, and the basic-open localisation
  data (Analogue 1's c-component construction) is exactly the structural
  cost of the difference.
- **Porting cost**: HIGH (effectively reproduces the whole structure-
  sheaf machinery to recover function-like behaviour).
- **Verdict**: **NO_USEFUL_ANALOGUE**. Useful only as moral confirmation
  that the *shape* of "continuous map → algebra hom" recurs across
  dualities; the *technique* depends on the algebra-of-functions
  reduction which we do not have for Spec.

---

### Analogue 4: `IsLocalization.lift` — universal lifting through localizations

- **Domain**: commutative algebra — `IsLocalization` universal property.
- **Same structural problem there**: a ring hom `f : R → S` that sends a
  submonoid `M ⊆ R` to units of `S` extends uniquely to `f' : R[M^{-1}] → S`.
  - `IsLocalization.lift` (`Mathlib/RingTheory/Localization/Basic.lean`).
- **Technique**: universal property — `R[M^{-1}]` is the *initial*
  algebra over `R` making `M` invert. The hom is forced uniquely.
- **Mapping to project**: gives the per-prime local hom `B_q → C_p`
  *inside* the chain — exactly the `M_p` and `α_p` of the broken
  SSP-bypass. But the global hom `B → C` is **not** obtained by any
  universal property of localization, because `B` is not a localization
  of itself nor a colimit of localizations indexed compatibly with the
  primes of `C`. (`B = colim_{f ∈ B} B[f^{-1}]` over all elements is a
  colimit of *localizations* but the relevant "extends" diagram does not
  match this colimit.)
- **Porting cost**: LOW for the per-prime data (already used in the
  consumer at L482–485 of the file).
- **Verdict**: **PARTIAL_ANALOGUE** — gives the local-data construction
  but not the global assembly. The global step requires the
  `Spec`-side reasoning of Analogue 1.

---

### Analogue 5: `Profinite` / Stone duality `Profinite ⇔ BooleanAlgebra^op`

- **Domain**: topology / order theory.
- **Same structural problem there**: continuous maps between profinite
  spaces correspond exactly to Boolean-algebra homs of the clopen
  algebras (`Profinite.Clopens`).
- **Technique**: pullback of clopen sets along the continuous map; the
  Boolean algebra of clopens is a complete invariant. The duality
  functor sends each continuous map to its inverse-image action on
  clopens — purely set-theoretic.
- **Mapping to project**: structurally similar (duality between
  topological objects and algebraic ones) but again, the algebraic
  object (`BooleanAlgebra`) is reconstructed from the topology *directly*
  (clopens are subsets); `B`, `C` here are external commutative rings
  whose connection to `Spec`-topology is by `IsLocalization` /
  `algebraMap`, not by direct inverse-image.
- **Porting cost**: HIGH.
- **Verdict**: **NO_USEFUL_ANALOGUE**. The duality shape recurs but
  the construction relies on function-like / set-like recovery of the
  algebraic object that we don't have here.

---

### Analogue 6: Manifold theory — `SmoothManifoldWithCorners` morphisms

- **Domain**: differential geometry — `Mathlib/Geometry/Manifold/`.
- **Same structural problem there**: would be "given a continuous map
  between smooth manifolds with stalkwise smoothness, construct a smooth
  map". Mathlib's *actual* shape for `ContMDiff` is purely pointwise —
  smoothness is a property of a map, not a construction from continuous
  + stalk data. No "build smooth map from continuous + germ-of-rings"
  constructor exists in Mathlib.
- **Verdict**: **NO_USEFUL_ANALOGUE**. The shape is right, but the
  Mathlib infrastructure goes in the *opposite* direction (smoothness
  as a property of pre-existing maps).

---

## Top suggestion

**Adopt Analogue 1**: rebuild the LRS-bridge route, but with a
*concrete* construction of the `c`-component of the
`LocallyRingedSpace.Hom`, avoiding the abstract `Sheaf.pullback`
machinery that stalled iter-145–149. Concretely:

1. **Build the c-component basic-open-by-basic-open**, not as the
   unit of an inverse-image adjunction. The structure sheaf
   `𝒪_{Spec B}` is determined on basic opens by
   `IsAffineOpen.isLocalization_of_eq_basicOpen`:
   `Γ(D(s), 𝒪_{Spec B}) ≅ B[s^{-1}]`. So defining
   `c.app (op D(s)) : B[s^{-1}] → Γ(φ⁻¹ D(s), 𝒪_{Spec C})` reduces to
   producing a ring map out of `B[s^{-1}]` — solvable via
   `IsLocalization.lift` once we exhibit that `s` maps to a unit in
   `Γ(φ⁻¹ D(s), 𝒪_{Spec C})` (this uses `BijectiveOnStalks A C` and
   `φ.comp_comap_algebraMap`).
2. **Promote to a `PresheafedSpace.Hom`** by passing the basic-open
   data through `TopCat.Presheaf.SheafCondition.UniqueGluing` (or the
   universal property of the sheafification on the basis of basic
   opens — `StructureSheaf.openAlgebra` / `subsheaf_to_Types`).
3. **Lift to `LocallyRingedSpace.Hom`** via
   `AlgebraicGeometry.LocallyRingedSpace.homMk`. The stalk-locality
   autoParam discharges because each stalk map equals
   `Localization.localRingHom`(of a composition of local maps) by
   construction.
4. **Extract the ring hom** via `AlgebraicGeometry.Spec.preimage`.
   Verify `Spec.map_preimage` recovers `φ.toContinuousMap` on the base
   topology (`Spec.map_apply` + `PrimeSpectrum.comap`-functoriality).
5. **Lift to A-algebra hom** by `commutes'` lemma:
   `f.comp (algebraMap A B) = algebraMap A C` follows from the over-
   `Spec A` structure of the `Spec.preimage` round trip; the bundled
   `B →ₐ[A] C` then plugs into `HomOver.ext` to close the goal.

**The first Mathlib file to read**:
`Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean` (lines 327–569),
specifically `ΓSpec.locallyRingedSpaceAdjunction`,
`Spec.fullyFaithfulToLocallyRingedSpace`, and `Spec.preimage`.

**The first project file to touch**:
`Proetale/Algebra/IdentifiesLocalRings.lean:384-592` — the consumer's
`suffices hex : ∃ f : B →+* C, …` gets discharged by `Spec.preimage`
applied to the LRS-hom constructed above. The standalone
`exists_ringHom_of_compatible_localRingHom_family` helper (L194–316)
should be **retired** — its hypotheses are mathematically insufficient,
per the iter-153 counterexample.

**Estimated LOC**: 150–250 for the LRS-hom construction (mostly the
c-component on basic opens + sheaf-condition gluing); ~50 LOC for the
ring-hom-extraction and A-linearity verification; consumer shrinks
~50 LOC by retiring the broken helper. Net ~150 LOC growth on the
file (within budget for a load-bearing existence theorem).

**Confidence**: MEDIUM-HIGH. The route is principled (it's literally
the Mathlib idiom for affine schemes), the failure modes are concrete
(c-component on basic opens), and the auxiliary lemmas all exist in
Mathlib (`isLocalization_of_eq_basicOpen`, `toOpen_comp_comap`,
`localRingHom_comp_stalkIso`, `arrowStalkMapSpecIso`). The iter-145–149
stall was due to attacking the *abstract* `q⁻¹ 𝒪_X ≅ 𝒪_Y` framing
(sheaf-pullback adjunction); the basic-open construction sidesteps that
adjunction.

## Discarded

- **Bundled "morphism of sites" / topos-theoretic** route — Mathlib's
  `CategoryTheory.Sites` infrastructure exists but is heavyweight; for
  Spec-of-rings the punchline is exactly the LRS-Hom path of Analogue 1,
  with extra category-theoretic overhead.
- **Quotient/colimit-of-fg-subalgebras** route — `B = colim
  fg-A-subalgebras` does not preserve `BijectiveOnStalks` at the
  subalgebra level; the inductive step does not type-check.
- **Adic spaces / formal schemes route** — Mathlib's `AdicSpace`
  development is nascent; no "ring-from-continuous-spec-map" primitive
  is available there that beats the LRS path.
- **Direct re-attempt of SSP-bypass with stronger hypothesis** — Option
  II in the iter-153 task-result is equivalent to assuming the
  conclusion. The counterexample is structurally fatal to the
  standalone-helper framing; the only way forward in that framing is to
  inline into the consumer (Option I), which reduces to Analogue 1's
  LRS path.
