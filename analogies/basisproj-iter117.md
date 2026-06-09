# Analogy: basis-projection ξ witness via Cayley–Hamilton collapse

## Mode
cross-domain-inspiration

## Slug
basisproj-iter117

## Iteration
117

## Structural problem (abstracted)
Given a finite free `A`-algebra `B` with a chosen basis `(b_l)`, an
element `r ∈ B` whose `A[X]`-charpoly `p` has `Polynomial.aeval r p =
0` (Cayley–Hamilton), and a family of "Newton increments" `Δ_m ∈ B`,
build a function `ξ : ℕ → Fin d → Fin k → A` whose value
`ξ m j l` is the `A`-coefficient of `r^{j+1}` in the unique degree-`< d`
polynomial representative of `BasisProj_l(Δ_m)` (i.e., reduce the
basis-coordinate `BasisProj_l(Δ_m)`'s lift to `A[X]` modulo `p`). The
construction must compose two existing Mathlib idioms — a
basis-coordinate functional `B → A` and a polynomial-modulo-charpoly
reduction — and the resulting `ξ` is the *unique* answer that makes
the downstream eval-zero identity hold.

## Failed approaches (from directive)
- γ-difference shifter `ξ m j l := γ((j:ℕ)-m) l - γ((j:ℕ)-m-1) l`:
  satisfies depth bound, **fails eval-zero conjunct in general**.
- Path B (consumer-side κ adjustment): creates two unidentifiable
  copies of κ on either side of the ∃; cannot reconcile them without
  proving the structural ξ formula anyway.

## Analogues found

Ranked by porting cost (lowest first).

### Analogue: `LinearMap.aeval_eq_aeval_mod_charpoly`

- **Domain**: linear algebra (Cayley–Hamilton corollary for module
  endomorphisms).
- **File**: `Mathlib.LinearAlgebra.Charpoly.Basic`.
- **Signature**: `∀ (f : M →ₗ[R] M) (p : R[X]), aeval f p = aeval f (p %ₘ f.charpoly)`.
- **Same structural problem there**: any polynomial in `f` collapses
  to its `%ₘ charpoly`-remainder of degree `< natDegree (charpoly)`,
  with the *coefficients of the remainder* being the unique
  `A`-coordinates of `aeval f p` in the basis `{1, f, f², …, f^{d-1}}`
  of `R[f] ⊂ Mod.End R M`. The `r_1^{d+m}` fold the directive
  describes is precisely the `Matrix.aeval_eq_aeval_mod_charpoly`
  twin (`Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`) applied to
  `M.charpoly` of the project's `M := Algebra.leftMulMatrix mBasis r1`.
  The `cCH_m(j)` coefficients in the project ARE the
  `(X^(d+m) %ₘ M.charpoly).coeff j` values, modulo a sign.
- **Technique**: take the `A[X]`-polynomial representative `P_m,l(X)`
  of `BasisProj_l(Δ_m)` (after expressing every `r_n` via
  `r_n_minus_r_1_in_gamma_finsupp` as a poly in `r_1`); then
  `ξ m j l := (P_m,l %ₘ M.charpoly).coeff (j+1)`. The depth bound
  `(P %ₘ M.charpoly).coeff (j+1) ∈ mA^((j:ℕ)-m)` reduces to depth
  control of the original `P_m,l`'s coefficients (which inherit
  depth from `η, μ, ρ`) propagated through `%ₘ` — and `%ₘ` only
  *preserves or improves* depth because `M.charpoly`'s coefficients
  are units mod `mA` (`hdet_unit`) and the higher coefficients of
  `M.charpoly` lie in `mA` (`hcCH_mem`-type bounds). The eval-zero
  conjunct is then the level-`(d-1)` instance of
  `aeval_eq_aeval_mod_charpoly` applied to the assembled telescope,
  rearranged via `Q3`–`Q5_lvl_succ` already banked at L2294 / L2503.
- **Mapping to project**: name `r₁ := r 1`, `Mφ : B →ₗ[A] B := LinearMap.mulLeft A r₁`,
  charpoly = `Mφ.charpoly = M.charpoly` (via
  `LinearMap.charpoly_toMatrix` and `Algebra.leftMulMatrix`). For each
  level `m`, *raw* witness `P_m,l : A[X]` is built by summing
  `r_n_minus_r_1_in_gamma_finsupp`'s `τ_{n,j,l}`-tuples weighted by
  `η_m / μ_{m+1} / ρ_m`. Then
  ```
  ξ m j l := (P_m,l %ₘ Mφ.charpoly).coeff (j + 1)
  ```
  is concrete `A`-arithmetic (no `Classical.choice`).
- **Porting cost**: medium. Need (a) the polynomial-side carrier
  `P_m,l : A[X]` (built from `η m`, `μm (m+1)`, `ρ_m`,
  `r_n_minus_r_1_in_gamma_finsupp`'s `τ`, all already in scope at
  L2127–L2680), (b) one application of
  `aeval_eq_aeval_mod_charpoly` to fold `r₁^{d+m}` slots, (c) a
  ~30-line transfer lemma showing `BasisProj_l(aeval Mφ P_m,l) = α-side`
  via `Algebra.leftMulMatrix_apply` / `Module.Basis.coord_apply`.
  No new Mathlib infrastructure required.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `IsAdjoinRootMonic.modByMonicHom` + `map_modByMonicHom`

- **Domain**: ring theory (presentation of `S = A[r]` as
  `A[X] / (charpoly r)` with an explicit `A`-linear retraction).
- **File**: `Mathlib.RingTheory.IsAdjoinRoot`.
- **Signature**: `modByMonicHom : S →ₗ[R] R[X]` (degree-`< natDegree f`
  representative), with `h.map (h.modByMonicHom x) = x`.
- **Same structural problem there**: every element `x ∈ A[r] ⊂ S` has
  a *canonical* polynomial representative `P_x ∈ A[X]` of degree
  `< d`, and the assignment `x ↦ P_x` is `A`-linear. The basis-
  coordinate `BasisProj_l(Δ_m)` lives in `A[r₁]` (a sub-`A`-algebra
  of `B`); `modByMonicHom` packages exactly the "coefficient
  extraction at `r₁^{j+1}` after C–H collapse" the directive needs.
- **Technique**: instantiate `IsAdjoinRootMonic.mk` with `S := A[r₁]`
  (the `Algebra.adjoin` of `r₁ : B`) and `f := M.charpoly` (monic by
  `Matrix.charpoly_monic`); the `IsAdjoinRoot` instance follows from
  `Polynomial.aeval_charpoly_eq_zero`-style data (already implicit in
  `hcCH_eq`). Then `modByMonicHom` is the polynomial representative
  of degree `< d`, and `ξ m j l := (modByMonicHom (BasisProj_l Δ_m)).coeff (j+1)`.
- **Mapping to project**: more bundled than the `aeval_eq_aeval_mod_charpoly`
  path, but produces a *first-class* `A`-linear hom `B →ₗ[A] A[X]`
  whose composition with `Polynomial.coeff (j+1) : A[X] →ₗ[A] A`
  gives the ξ-row at fixed `(m, l)` as a single LinearMap. This is
  nice for the eval-zero proof (everything stays linear).
- **Porting cost**: medium-high. Need to first verify that
  `A[r₁]` (`Algebra.adjoin A {r₁}`) carries an
  `IsAdjoinRootMonic` instance for `M.charpoly`; this is a tractable
  but non-trivial setup (~50 lines). Once banked, downstream is
  clean.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Polynomial.degreeLT.basis` + `Module.Basis.coord`

- **Domain**: linear algebra (the standard finite-rank basis of
  polynomials of bounded degree).
- **Files**: `Mathlib.RingTheory.Polynomial.DegreeLT` for
  `Polynomial.degreeLT.basis` (`Module.Basis (Fin n) R (degreeLT R n)`),
  `Mathlib.LinearAlgebra.Basis.Defs` for
  `Module.Basis.coord` (`b.coord i : M →ₗ[R] R`).
- **Same structural problem there**: extract the `j`-th coordinate of
  a polynomial of degree `< d` as an `R`-linear functional. This is
  Mathlib's idiom for the *very last* step of the recipe — after
  `%ₘ M.charpoly` reduction lands in `degreeLT A d`, applying
  `(degreeLT.basis A d).coord ⟨j+1, _⟩` returns the `r₁^{j+1}`
  coefficient as a clean `A`-linear functional.
- **Technique**: compose three Mathlib carriers:
  ```
  ξ m j l := ((degreeLT.basis A d).coord ⟨j+1, _⟩)
             (some_lift_to_degreeLT (P_m,l %ₘ M.charpoly))
  ```
  with `BasisProj_l := mBasis.coord l : B →ₗ[A] A` for the outer
  basis-projection.
- **Mapping to project**: this is *the* Lean idiom for
  "`A`-coefficient of `X^{j+1}` in a polynomial". Use it for the
  `coeff (j+1)` step only; the surrounding scaffold (charpoly
  reduction, basis projection) comes from the analogues above.
- **Porting cost**: low (these are utility lemmas, not new
  infrastructure). They slot into either of the two analogues above.
- **Verdict**: ANALOGUE_FOUND (supporting role).

### Analogue: `Module.Basis.coord_apply` for `BasisProj_l`

- **Domain**: linear algebra.
- **File**: `Mathlib.LinearAlgebra.Basis.Defs`.
- **Signature**: `b.coord i x = b.repr x i`. Identifies
  `b.coord i : M →ₗ[R] R` as `b.repr x` evaluated at `i`.
- **Same structural problem there**: extract the `l`-th
  basis-coordinate of `x ∈ M` as an `R`-linear functional.
- **Technique**: use `mBasis.coord l : B →ₗ[A] A` directly as
  `BasisProj_l`; combine with `Module.Basis.sum_repr` to recover
  `x = ∑ l, algebraMap A B (mBasis.coord l x) * basis l`.
- **Mapping to project**: `mBasis` is *already* defined at L2127. The
  needed functional is `mBasis.coord l` with no further work. The
  `hsum_repr := mBasis.sum_repr` lemma is in scope. The earlier ξ
  proof attempts didn't reach for `mBasis.coord` because the
  γ-difference path bypassed basis projection entirely; the new
  proof should make `BasisProj_l := mBasis.coord l` the primary
  vehicle.
- **Porting cost**: low (already-in-scope `mBasis`).
- **Verdict**: ANALOGUE_FOUND (supporting role).

### Analogue: `Module.AEval'` (R-module-via-endomorphism viewpoint)

- **Domain**: module theory.
- **File**: `Mathlib.Algebra.Polynomial.Module.AEval`.
- **Signature**: `Module.AEval' φ` makes `M` into an `R[X]`-module
  via `φ : M →ₗ[R] M`, with `X • m = φ m`.
- **Same structural problem there**: the C–H collapse of "powers of
  `φ`" is reflected as an `R[X]`-module structure on `M` quotiented
  by `(charpoly φ)`. Polynomials in `φ` acting on `m` factor
  through `R[X] / (charpoly φ)`.
- **Technique**: view `B` as an `A[X]`-module via `mulLeft r₁`, then
  the C–H quotient `A[X] / (M.charpoly)` acts on `B`, and any
  "polynomial expression in `r₁`" applied to `b₀` (or any `b ∈ B`)
  lifts to a degree-`< d` representative.
- **Mapping to project**: structurally elegant but more bundling work
  than the two `aeval_eq_aeval_mod_charpoly`/`IsAdjoinRootMonic`
  paths. The Mathlib API around `AEval'` is mostly definitional;
  it doesn't reduce the proof obligations the project already has.
- **Porting cost**: high (more re-bundling than the project gains).
- **Verdict**: PARTIAL_ANALOGUE.

## Top suggestion

**Try `LinearMap.aeval_eq_aeval_mod_charpoly`-style C–H reduction.**
Concretely: in the body of the `∃ ξ` proof at L2681–L2696, build the
polynomial `P_m,l : A[X]` by combining
`r_n_minus_r_1_in_gamma_finsupp`'s `τ`-tuples with the route-(A)
carriers `η`, `μm`, `ρ` (parent-scope at L2127–L2680), apply
`Matrix.aeval_eq_aeval_mod_charpoly` to fold every `r₁^{d+m}` slot
into the `{1, r₁, …, r₁^{d-1}}` range, then define
```
ξ m j l := (P_m,l %ₘ M.charpoly).coeff (j + 1)
```
where `M.charpoly` is `Matrix.charpoly (Algebra.leftMulMatrix mBasis r₁)`.
The depth bound and eval-zero conjunct both follow:
- **Depth**: `(P_m,l %ₘ M.charpoly).coeff (j+1)` inherits its
  `mA`-band from `P_m,l`'s coefficients (which inherit from
  `η, μ, ρ`) and `M.charpoly`'s subleading coefficients in `mA`
  (`hcCH_mem`/`hdet_unit` consequences).
- **Eval-zero**: by definition the LHS
  `α i · (C M.det − X ∑_j C(κ_{ij}(ξ)) X^j).eval (α i)` is the
  level-`(d-1)`-stabilised P4 identity, and the
  `aeval_eq_aeval_mod_charpoly` rewrite makes the right-hand side
  vanish in `A` by tracking it through the already-banked
  `hTele_Q3_lvl_succ` / `hQ3` chain (L2294/L2503), with no
  "extra hypothesis" beyond what's in scope.

The first project file to touch is
`Proetale/Mathlib/RingTheory/Etale/HenselianPair.lean` at line
2681 (the `∃ ξ` opener); the bulk of new code is the
`P_m,l : A[X]` constructor (~30–50 lines) plus a transfer lemma
from `B`-side to `A`-side coefficients (~20 lines).

## Discarded

- **`Module.AEval'` route** — works in principle but bundles more
  than it saves; same `%ₘ M.charpoly` content with extra
  scaffolding.
- **Pure `Module.Basis.repr` + telescoping** — collapses to the
  γ-difference witness already in the failed-approaches list.
