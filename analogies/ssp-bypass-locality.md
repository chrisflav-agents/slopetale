# Analogy: how to carry locality of a per-prime family of ring homs through an amalgamation helper

## Mode
api-alignment

## Slug
ssp-bypass-locality

## Iteration
153

## Question

Inside the private helper
`exists_ringHom_of_compatible_localRingHom_family` at
`Proetale/Algebra/IdentifiesLocalRings.lean:194`, the substantive
sheaf-amalgamation proof requires the locally-constant locally-a-fraction
property (chapter recipe `local-structure.tex` L1117), which the chapter
explicitly proves by invoking `α p` being a **local** ring hom. The helper
currently takes `α p` as a bare `RingHom` with no local-hom witness.

Should the helper signature be extended with a locality hypothesis on
`α p`? Choices:
- (A) explicit `(hαlocal : ∀ p, IsLocalHom (α p))`
- (B) typeclass binder `[∀ p, IsLocalHom (α p)]`
- (C) keep frozen, route locally-constant proof through ad-hoc reasoning
- (D) bundle `α p` into a `LocalRingHom` carrier

Sub-question: what is Mathlib's canonical idiom for "per-prime family of
local ring maps between localizations, amalgamated to a base ring map"?

## Project artifact(s)

- `Proetale/Algebra/IdentifiesLocalRings.lean:194-278` — helper signature + body with L257 sorry.
- `Proetale/Algebra/IdentifiesLocalRings.lean:347-555` — sole consumer `exists_algHom_of_continuousMap`; constructs `α p` as `Lp.comp Kinv` (a composite of `Localization.localRingHom` + the inverse of a `RingEquiv`).
- `blueprint/src/chapters/local-structure.tex:1086-1268` — chapter recipe `lem:exists-ringHom-of-compatible-localRingHom-family`. L1117 invokes locality.

## Decisions identified

### Decision: bundled-vs-predicate for "this ring hom is local"

- **Mathlib idiom**: `IsLocalHom` is a `Prop`-valued **typeclass** at
  `Mathlib/Algebra/Group/Units/Hom.lean:270` (`class IsLocalHom (f : F) : Prop`),
  applied as a side condition to a bare `R →+* S`. There is **no bundled
  `LocalRingHom` structure in Mathlib**. The function `Localization.localRingHom`
  at `Mathlib/RingTheory/Localization/AtPrime/Basic.lean:239` returns a plain
  `Localization.AtPrime I →+* Localization.AtPrime J`; locality is recorded
  separately as `@[instance] theorem isLocalHom_localRingHom` at L263.
- **Project's current path**: helper carries `α p : ... →+* ...` (bare ring hom)
  with NO locality witness anywhere in scope.
- **Gap**: divergent-with-cost. Project's current signature is structurally
  Mathlib-aligned for the bundling axis (bare ring hom, not bundled), but
  drops the locality property entirely; the chapter recipe cannot be
  followed without resurrecting it.
- **Verdict**: ALIGN_WITH_MATHLIB — keep bare ring hom + add `IsLocalHom`
  as a side condition. Reject option (D) (no bundled `LocalRingHom` exists
  in Mathlib; bundling would invent a parallel API).

### Decision: explicit-hypothesis-vs-typeclass-binder for the side condition

- **Mathlib idiom**: explicit hypothesis (often `Prop`-valued field on a
  bundled morphism). Best precedent:
  `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean:81`:
  ```
  structure Hom (X Y : LocallyRingedSpace.{u}) ...
    prop : ∀ x, IsLocalHom (toHom.stalkMap x).hom
  ```
  with a companion `@[instance] isLocalHomStalkMap` at L107 exposing each
  pointwise `IsLocalHom` to instance synthesis once the structure is in
  hand. The smart constructor `homMk` (L157) takes the locality as an
  explicit hypothesis with `(... := by infer_instance)` default. The
  pattern is: **carry the universally-quantified `IsLocalHom` as an
  explicit `Prop` argument; re-derive it as a typeclass instance at use
  sites if needed.**
- Typeclass binders of the form `[∀ p, IsLocalHom (α p)]` over a per-index
  family of *anonymous* / *let-bound* maps are NOT used in Mathlib;
  instance synthesis on `α p` would have to thread through the indexing
  type, which Mathlib does not set up.
- **Project's current path**: nothing carried; no precedent for the
  typeclass-over-family form.
- **Gap**: divergent-with-cost. Without locality the helper proof cannot
  go through (chapter L1117). Choosing (B) would also be divergent: no
  Mathlib precedent for instance-binders on per-index families of ring
  homs.
- **Verdict**: ALIGN_WITH_MATHLIB — use option **(A)**, the explicit
  hypothesis `(hαlocal : ∀ p, IsLocalHom (α p))`.

### Decision: does Mathlib package the amalgamation step?

- **Mathlib idiom**: NO single packaged "compatible per-prime family of
  ring maps `B → C_p` glues to a ring map `B → C`" lemma exists. The
  ingredients live separately:
  - `TopCat.Sheaf.existsUnique_gluing` at
    `Mathlib/Topology/Sheaves/SheafCondition/UniqueGluing.lean:180` —
    purely sheaf-theoretic, no locality in signature.
  - `AlgebraicGeometry.StructureSheaf.globalSectionsIso` at
    `Mathlib/AlgebraicGeometry/StructureSheaf.lean:939` — identifies
    `CommRingCat.of R` with `(structureSheaf R).1.obj (op ⊤)`.
  - `AlgebraicGeometry.StructureSheaf.isLocallyFraction` at
    `Mathlib/AlgebraicGeometry/StructureSheaf.lean:112` — sheafification
    of `isFractionPrelocal`; the "locally a fraction" predicate the
    chapter recipe Step 3 needs. **Does not use `IsLocalHom` at
    signature level** — locality is consumed inside the helper proof
    (not in the carrier's type).
- The `Γ-Spec` adjunction packages ring-hom ↔ scheme-morphism from a
  *single* `R → Γ(X)`, not from a per-prime family.
- **Project's current path**: helper plans to use `IsSheaf.amalgamate`
  on `structureSheaf C` + `globalSectionsIso` directly. This matches
  Mathlib's available primitives.
- **Gap**: identical at the amalgamation-primitives level. Mathlib does
  not have a higher-level "compatible-family" packaging, so the helper
  is genuinely building infrastructure on top of Mathlib's gluing API.
- **Verdict**: PROCEED. The locality of `α p` is consumed **inside the
  proof** (specifically, used to prove the locally-a-fraction property
  passed to `IsSheaf.amalgamate`), not at signature level of any Mathlib
  call. This corroborates the (A) verdict — explicit hypothesis is the
  right shape because the proof body internalises it.

## Recommendation

Adopt **option (A)**: extend the helper signature with an explicit
hypothesis

```
(hαlocal : ∀ p : PrimeSpectrum C, IsLocalHom (α p))
```

placed immediately after `α` and before `hM`. Concretely the new
signature is:

```lean
private theorem exists_ringHom_of_compatible_localRingHom_family
    {B C : Type*} [CommRing B] [CommRing C]
    (M : ∀ p : PrimeSpectrum C, B →+* Localization.AtPrime p.asIdeal)
    (φ : PrimeSpectrum C → PrimeSpectrum B)
    (α : ∀ p : PrimeSpectrum C,
      Localization.AtPrime (φ p).asIdeal →+* Localization.AtPrime p.asIdeal)
    (hαlocal : ∀ p, IsLocalHom (α p))
    (hM : ∀ p b, M p b = α p (algebraMap B (Localization.AtPrime (φ p).asIdeal) b)) :
    ∃ f : B →+* C, (PrimeSpectrum.toPiLocalization C).toRingHom.comp f = Pi.ringHom M := by ...
```

Rationale:
- Matches Mathlib's `LocallyRingedSpace.Hom.prop` pattern (universally-quantified
  `IsLocalHom` as an explicit prop), the only direct Mathlib precedent
  for per-index families of local-ring-hom data.
- Mathlib has NO bundled `LocalRingHom` carrier — option (D) would invent
  a parallel API and require consumer-site rework.
- Typeclass binders on per-index `α p` families (option B) are not used
  in Mathlib and would not synthesize cleanly when the family is built
  pointwise from `let`-bindings (as the consumer at L529–535 does).
- Option (C) is ruled out by the chapter recipe: L1117 explicitly uses
  locality of `α p` to prove the locally-a-fraction property feeding
  `IsSheaf.amalgamate`. Without it the chapter Step 3 cannot be
  formalised.

Consumer-site adjustment is trivial. At
`Proetale/Algebra/IdentifiesLocalRings.lean:529-535` the consumer passes
`α p := Lp.comp Kinv` where:
- `Lp := Localization.localRingHom _ p.asIdeal (algebraMap A C) _` —
  locality registered by `Localization.isLocalHom_localRingHom` at
  `Mathlib/RingTheory/Localization/AtPrime/Basic.lean:263`.
- `Kinv := (RingEquiv.ofBijective _ (hKbij p)).symm.toRingHom` — a
  `RingEquiv`'s underlying ring hom is a local hom because a `RingEquiv`
  preserves and reflects units in both directions
  (`RingEquiv.isLocalHom_symm` / via `MulEquiv.isUnit_map`, already used
  at L516–518).
- Composition of local ring homs is a local ring hom
  (`Mathlib`'s `IsLocalHom` composition lemma).

So the consumer simply supplies a one-line `fun p => (hLp.comp hKinv)`
style proof for the new `hαlocal` argument; no structural rework.

## Severity

high-stakes. The signature freeze decision is load-bearing for closing
the SSP-bypass route. Locking in (A) this iter licenses the prover round
to attack the L257 sorry against a fixed locality witness.
