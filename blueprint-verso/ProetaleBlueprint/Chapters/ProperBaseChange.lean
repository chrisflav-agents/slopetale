import Verso
import VersoManual
import VersoBlueprint
import Proetale
import ProetaleBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Proper base change" =>

In this chapter we set up the base change machinery for abelian sheaves on small
étale sites and decompose the proof of the proper base change theorem
(SGA 4, Exposé XII). Throughout, consider a cartesian square of schemes

$$`\begin{array}{ccc} X' & \xrightarrow{g'} & X \\ \downarrow f' & & \downarrow f \\ S' & \xrightarrow{g} & S \end{array}`

with $`f` proper.

:::group "proper-base-change"
The base change formalism for étale cohomology and the proper base change theorem,
following SGA 4, Exposé XII.
:::

# The base change morphism

:::definition "def:etale-pushforward" (parent := "proper-base-change") (lean := "AlgebraicGeometry.Scheme.etalePushforward")
For a morphism of schemes $`f \colon X \to S`, base change of étale $`S`-schemes
induces a continuous morphism of small étale sites, and hence an adjunction
$`f^* \dashv f_*` between the categories of abelian sheaves on $`\et{X}` and
$`\et{S}`.
:::

:::lemma_ "lemma:etale-pullback-exact" (parent := "proper-base-change") (uses := "def:etale-pushforward") (lean := "AlgebraicGeometry.Scheme.preservesFiniteLimits_smallPullback")
The pullback functor $`f^*` on abelian étale sheaves is exact.
:::

:::proof "lemma:etale-pullback-exact"
$`f^*` is a left adjoint, hence right exact. For left exactness, the base change
functor on the small étale sites preserves finite limits, so it is representably
flat, so the left Kan extension on abelian presheaves is a filtered colimit
pointwise and therefore exact; sheafification is exact as well.
:::

:::definition "def:base-change-transformation" (parent := "proper-base-change") (uses := "def:etale-pushforward") (lean := "AlgebraicGeometry.Scheme.baseChangeNatTrans")
For a commutative square $`g' \circ f = f' \circ g` as above (not necessarily
cartesian), the *base change transformation*
$$`\tau \colon f_* \circ g^* \longrightarrow g'^* \circ f'_*`
is the mate of the canonical isomorphism $`g^* \circ f'^* \cong f^* \circ g'^*`,
which in turn is conjugate to the canonical isomorphism
$`g'_* \circ f_* \cong f'_* \circ g_*` of pushforward functors.
:::

:::definition "def:derived-category-plus" (parent := "proper-base-change") (lean := "DerivedCategoryPlus")
The *bounded below derived category* $`D^+(\mathcal{A})` of an abelian category
$`\mathcal{A}` is the localization of the category of bounded below cochain
complexes at the quasi-isomorphisms.
:::

:::lemma_ "lemma:fibrant-derives" (parent := "proper-base-change") (uses := "def:derived-category-plus") (lean := "CategoryTheory.Functor.fibrantObject_derives_mapCochainComplexPlus")
Let $`\mathcal{A}` be an abelian category with enough injectives. Bounded below
complexes of injectives are K-injective; consequently any quasi-isomorphism between
them is a homotopy equivalence and is inverted by $`G` followed by the localization,
for every additive functor $`G`.
:::

:::proof "lemma:fibrant-derives"
The fibrant objects of the injective model structure on bounded below complexes are
exactly the bounded below complexes of injectives. These are K-injective, so a
quasi-isomorphism between them is a homotopy equivalence; additive functors preserve
homotopy equivalences, and homotopy equivalences are quasi-isomorphisms.
:::

:::definition "def:derived-pushforward" (parent := "proper-base-change") (uses := "def:etale-pushforward, def:derived-category-plus, lemma:fibrant-derives") (lean := "AlgebraicGeometry.Scheme.derivedPushforward")
The *derived pushforward*
$`Rf_* \colon D^+(\mathrm{Ab}(\et{X})) \to D^+(\mathrm{Ab}(\et{S}))`
is the total right derived functor of $`f_*`, constructed via the derivability
structure of fibrant objects of the injective model structure on bounded below
complexes. Since $`g^*` is exact ({bpref "lemma:etale-pullback-exact"}[]), it descends
to the bounded below derived categories without derivation.
:::

:::definition "def:derived-base-change" (parent := "proper-base-change") (uses := "def:derived-pushforward, def:base-change-transformation") (lean := "AlgebraicGeometry.Scheme.derivedBaseChangeNatTrans")
The *derived base change transformation*
$$`Rf_* \circ g^* \longrightarrow g'^* \circ Rf'_*`
is obtained from the underived one ({bpref "def:base-change-transformation"}[]) by
the universal property of the total right derived functor: the composite
$`Rf_* \circ g^*` is itself a right derived functor of $`f_* \circ g^*` because
$`g^*` is exact.
:::

:::definition "def:locally-torsion" (parent := "proper-base-change") (lean := "CategoryTheory.Sheaf.IsLocallyTorsion")
An abelian sheaf $`F` on a site is *locally torsion* if every section is, locally on
a covering, killed by a positive integer.
:::

:::theorem "thm:proper-base-change" (parent := "proper-base-change") (uses := "def:derived-base-change, def:locally-torsion, lemma:pbc-devissage-K, cor:stalkwise-iso, thm:pbc-special-case") (lean := "AlgebraicGeometry.Scheme.isIso_derivedBaseChangeNatTrans_app")
(Proper base change, SGA 4 XII 5.1.) If the square is cartesian and $`f` is proper,
the derived base change transformation is an isomorphism on every bounded below
complex with locally torsion cohomology sheaves.
:::

:::proof "thm:proper-base-change"
By dévissage (truncation triangles and the five lemma) reduce to a single locally
torsion sheaf $`F`. Writing $`F` as the filtered colimit of its $`n`-torsion
subsheaves and using that étale cohomology of the qcqs schemes involved commutes with
filtered colimits, reduce to sheaves of $`\mathbb{Z}/n`-modules. Isomorphy may be
checked on stalks at geometric points of $`S'`; the stalk of $`R^q f'_*` at a
geometric point is the cohomology of the base change of $`X` to the strict
henselization, which is the special case {bpref "thm:pbc-special-case"}[].
:::

:::lemma_ "lemma:pbc-devissage-K" (parent := "proper-base-change") (uses := "def:derived-base-change, def:locally-torsion") (lean := "AlgebraicGeometry.Scheme.isIso_derivedBaseChangeNatTrans_app_of_singleFunctor")
If the derived base change transformation is an isomorphism on every locally torsion
abelian sheaf placed in degree zero, then it is an isomorphism on every bounded below
complex with locally torsion cohomology sheaves.
:::

:::proof "lemma:pbc-devissage-K"
Dévissage along the canonical truncation filtration. The transformation is computed on
a fibrant (degreewise injective) resolution by a concrete comparison map of complexes,
so isomorphy can be checked on homology in each degree; short exact sequences of
bounded below complexes admit componentwise injective resolutions (horseshoe lemma),
giving the two-out-of-three property via the homology ladder. Singles in arbitrary
degrees are reached from degree zero by the two-term acyclic complexes linking
consecutive singles, bounded complexes by induction on the cohomological amplitude,
and the general case follows because a bounded below complex of injectives that is
exact in low degrees has a partial contracting homotopy, so its image under any
additive functor remains exact in low degrees — each homology of the value therefore
only depends on a finite truncation.
:::

# Reduction to the strictly henselian case

:::definition "def:geometric-point" (parent := "proper-base-change") (lean := "AlgebraicGeometry.Scheme.Etale.geometricPoint")
A *geometric point* of a scheme `X` is a morphism `x̄ : Spec Ω ⟶ X` with `Ω`
separably closed. It defines a point of the small étale site of `X` in the sense of
topos theory: the fiber functor sends an étale `X`-scheme `U` to the set of lifts of
`x̄` to `U`, and the associated fiber functor on sheaves is the *stalk* at `x̄`.
:::

:::proof "def:geometric-point"
The fiber functor preserves finite limits because the étale neighbourhoods of a
geometric point form a cofiltered category (fiber products and equalizers of étale
`X`-schemes are again étale), it sends covering sieves to jointly surjective families
by lifting the geometric point along an étale cover through the separable residue
field extensions, and the affine étale neighbourhoods form an initial small
subfamily. In Lean, the point is obtained by restricting the point of the big étale
site defined by the fiber functor `Hom(Spec Ω, ·)` along the continuous inclusion of
the small étale site.
:::

:::theorem "thm:enough-points" (parent := "proper-base-change") (uses := "def:geometric-point") (lean := "AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_geometricPoint")
(SGA 4 VIII 3.5.) The small étale site of a scheme `X` has enough points: the
geometric points with values in the separable closures of the residue fields of `X`
form a conservative family. In particular, isomorphy of morphisms of étale sheaves
may be checked on stalks.
:::

:::proof "thm:enough-points"
By the site-theoretic criterion (SGA 4 IV 6.5 (a)) it suffices to show that a sieve
`S` on an étale `X`-scheme `U` whose fibers over every geometric point are jointly
surjective is a covering sieve. For a point `q` of `U` with image `p` in `X`, the
residue field extension `κ(q)/κ(p)` is finite separable because `U → X` is étale, so
it embeds into the separable closure of `κ(p)`; this produces a lift of the canonical
geometric point at `p` through `q`, which by hypothesis factors through an arrow of
`S`. Hence the arrows of `S` are jointly surjective and `S` refines an étale cover.
:::

:::corollary "cor:stalkwise-iso" (parent := "proper-base-change") (uses := "thm:enough-points") (lean := "AlgebraicGeometry.Scheme.isIso_iff_sheafFiber_geometricPoint")
A morphism of abelian sheaves on the small étale site of a scheme `X` is an
isomorphism if and only if it induces isomorphisms on the stalks at the geometric
points of `X` with values in the separable closures of the residue fields.
:::

:::proof "cor:stalkwise-iso"
Immediate from {bpref "thm:enough-points"}[], after lifting the fiber functors of the
conservative family of points to the universe over which the coefficient category is
concrete (postcomposition with the universe lift functor preserves cofilteredness and
initial smallness of the categories of étale neighbourhoods, and conservativity of
the family).
:::

The following statements require infrastructure that is not yet available: strictly
henselian local rings, and the computation of stalks of higher direct images at
geometric points as cohomology over the strict henselization.

:::definition "def:strictly-henselian" (parent := "proper-base-change") (uses := "def:geometric-point") (lean := "AlgebraicGeometry.Scheme.Etale.strictLocalization")
A local ring $`R` is *strictly henselian* if it is henselian with separably closed
residue field. For a geometric point $`\bar{s}` of a scheme $`S`, the *strict
localization* $`\mathcal{O}^{sh}_{S, \bar{s}}` is the filtered colimit of the rings
of functions over the étale neighbourhoods of $`\bar{s}`.
:::

:::theorem "thm:strict-localization-henselian" (parent := "proper-base-change") (uses := "def:strictly-henselian") (lean := "AlgebraicGeometry.Scheme.Etale.isStrictlyHenselianLocalRing_strictLocalization")
The strict localization of a scheme at a geometric point is a strictly henselian
local ring.
:::

:::proof "thm:strict-localization-henselian"
The strict localization is local: a germ is invertible if and only if its value at the
geometric point is nonzero, because the basic open on which a function is invertible
is again an étale neighbourhood. By the retraction criterion
({bpref "lemma:retractions-strictly-henselian"}[]) it then suffices to show that every étale algebra over the strict localization with
surjective spectrum map admits a retraction: such an algebra descends to an étale
algebra over the functions of some affine étale neighbourhood (étale ring maps spread
out through filtered colimits), the geometric point lifts to the corresponding étale
scheme (étale algebras over the evaluation character acquire points valued in the
separably closed field), and the germ map of the resulting refined étale neighbourhood
provides the retraction.
:::

:::theorem "thm:pbc-special-case" (parent := "proper-base-change") (uses := "def:strictly-henselian, lemma:pbc-degree-zero, lemma:pbc-finite, thm:pbc-curves, lemma:pbc-devissage")
Let $`S` be the spectrum of a strictly henselian local ring with closed point $`s`,
let $`f \colon X \to S` be proper and let $`F` be a torsion abelian sheaf on
$`\et{X}`. Then restriction induces isomorphisms
$$`H^q(X, F) \xrightarrow{\ \sim\ } H^q(X_s, F|_{X_s})`
for all $`q \geq 0`.
:::

# Degree zero and finite morphisms

:::lemma_ "lemma:pbc-degree-zero" (parent := "proper-base-change") (uses := "def:strictly-henselian, lemma:pbc-finite")
In the situation of {bpref "thm:pbc-special-case"}[], the restriction
$`\Gamma(X, F) \to \Gamma(X_s, F|_{X_s})` is bijective.
:::

:::proof "lemma:pbc-degree-zero"
By Stein factorization and the finite case one reduces to the statement that the
connected components of $`X` and of the closed fiber $`X_s` correspond bijectively;
this is the lifting of idempotents along the finite $`\mathcal{O}_S`-algebra
$`f_* \mathcal{O}_X` over the henselian local base.
:::

:::lemma_ "lemma:finite-split-henselian" (parent := "proper-base-change") (uses := "thm:strict-localization-henselian") (lean := "IsLocalRing.finite_maximalSpectrum_and_bijective_pi_localization_of_forall_retraction, AlgebraicGeometry.Scheme.Etale.finite_maximalSpectrum_and_bijective_pi_localization_of_finite")
A finite algebra over the strict localization at a geometric point — more generally,
over a local ring in which every étale algebra with a prime over the maximal ideal
admits a retraction — has finitely many maximal ideals, and the canonical map to the
product of its localizations at the maximal ideals is bijective.
:::

:::proof "lemma:finite-split-henselian"
All maximal ideals contract to the maximal ideal of the base by integrality, and there
are finitely many of them because the fiber over the residue field is Artinian. For
each maximal ideal, Zariski's main theorem in its étale-idempotent form produces an
étale algebra over the base with a prime of trivial residue extension and an
idempotent in the base change isolating the given maximal ideal; after shrinking the
étale algebra so that this prime is the unique one over the maximal ideal, the
retraction transports the idempotent into the finite algebra itself, where it is
primitive at the given maximal ideal. Orthogonalizing the resulting family and
observing that the sum is congruent to `1` modulo every maximal ideal yields a
complete orthogonal family of idempotents; each factor is identified with the
localization at the corresponding maximal ideal.
:::

:::lemma_ "lemma:etale-section-split" (parent := "proper-base-change") (uses := "lemma:finite-split-henselian") (lean := "IsLocalRing.bijective_algebraMap_localization_atPrime_of_etale, IsLocalRing.exists_retraction_of_etale_of_ker_comp_eq, IsLocalRing.retraction_eq_of_comp_eq, IsStrictlyHenselianLocalRing.of_forall_module_finite_bijective_pi")
Let $`L` be a local ring with separably closed residue field whose module-finite
algebras all decompose as the products of their localizations at maximal ideals. Then
for every étale $`L`-algebra $`B` and every prime $`q` of $`B` over the maximal ideal,
the canonical map $`L \to B_q` is bijective. Consequently for every character
$`\chi \colon B \to \Omega` to a field whose restriction to $`L` has kernel the
maximal ideal there is a unique retraction $`\sigma \colon B \to L` compatible with
$`\chi`, and $`L` is strictly henselian.
:::

:::proof "lemma:etale-section-split"
This is Stacks 04GG, (10) ⇒ (8). By Zariski's main theorem, $`B` coincides near `q`
with a localization of a module-finite subalgebra $`S' \subseteq B`; the splitting
hypothesis applied to $`S'` shows that $`B_q` is a localization of $`S'` at a maximal
ideal, hence a direct factor, hence module-finite over $`L`. Being also flat, it is
free, and its fiber over the residue field is trivial: it is the residue field of `q`,
a finite separable extension of the separably closed residue field of $`L`. Nakayama's
lemma applied twice gives bijectivity. A compatible retraction inverts the complement
of `q`, so it factors uniquely through $`B_q \cong L`; conversely the localization map
composed with this isomorphism is a compatible retraction.
:::

:::theorem "thm:fiber-sections-henselian" (parent := "proper-base-change") (uses := "lemma:etale-section-split, lemma:finite-split-henselian, thm:strict-localization-henselian") (lean := "AlgebraicGeometry.Scheme.Etale.isStrictlyHenselianLocalRing_localization_atPrime_fiberSections")
Let $`f \colon Y \to X` be a finite morphism and $`\bar{x}` a geometric point of
$`X`. The localization of the ring of sections of the fiber of $`f` over the strict
localization at every maximal ideal is a strictly henselian local ring (Stacks 04GH).
:::

:::proof "thm:fiber-sections-henselian"
The fiber sections are module-finite over the strict localization
({bpref "thm:strict-localization-henselian"}[]), so each localization at a maximal
ideal is a direct factor, hence again module-finite; its finite algebras are then
module-finite over the strict localization and split by
{bpref "lemma:finite-split-henselian"}[], and its residue field is a finite, hence
algebraic, extension of the separably closed residue field of the strict
localization, hence separably closed. Now apply {bpref "lemma:etale-section-split"}[].
:::

:::lemma_ "lemma:pbc-finite" (parent := "proper-base-change") (uses := "def:etale-pushforward, lemma:finite-split-henselian, thm:fiber-sections-henselian")
For a finite morphism $`f`, one has $`R^q f_* F = 0` for $`q > 0`, and the base
change transformation is an isomorphism for every abelian sheaf $`F`.
:::

:::proof "lemma:pbc-finite"
The stalk of $`f_* F` at a geometric point $`\bar{s}` is
$`\prod_{\bar{x} \mapsto \bar{s}} F_{\bar{x}}`, because a finite algebra over a
strictly henselian local ring decomposes as a finite product of strictly henselian
local algebras. Exactness of $`\prod` and the same computation after base change give
both claims.
:::

# Cohomology of curves

:::theorem "thm:pbc-curves" (parent := "proper-base-change")
Let $`C` be a proper curve over an algebraically closed field $`k` and let `n` be an
integer. Then $`H^q(C, \mathbb{Z}/n) = 0` for $`q > 2`, and for $`C` smooth connected
and $`n` invertible in $`k` there are canonical isomorphisms
$`H^0 = \mathbb{Z}/n`, $`H^1 = \operatorname{Pic}(C)[n]`, $`H^2 = \mathbb{Z}/n`.
:::

:::proof "thm:pbc-curves"
Via the Kummer sequence this reduces to the computation of
$`H^q(C, \mathbb{G}_m)`: $`H^1` is the Picard group, and $`H^q = 0` for
$`q \geq 2` by Tsen's theorem (the function field of $`C` is $`C_1`, so its Brauer
group and higher Galois cohomology vanish). This chapter of the formalization —
Kummer theory, Picard schemes, Tsen's theorem — is the deepest missing prerequisite
and deserves a blueprint chapter of its own.
:::

# Dévissage

:::lemma_ "lemma:pbc-devissage" (parent := "proper-base-change") (uses := "lemma:pbc-finite, thm:pbc-curves, lemma:pbc-degree-zero")
The special case {bpref "thm:pbc-special-case"}[] holds in general if it holds for
$`f` of relative dimension $`\leq 1`.
:::

:::proof "lemma:pbc-devissage"
Locally on $`X`, the morphism $`f` factors through a projective space over $`S`; by
the finite case and Čech arguments one reduces to $`f = \mathbb{P}^n_S \to S`, which
is an iterated fibration in curves. The Leray spectral sequence for a fibration in
curves, together with induction on the fiber dimension and
{bpref "thm:pbc-curves"}[] for the fibers, yields the general case.
:::

# Finiteness of étale cohomology

:::theorem "thm:pbc-finiteness" (parent := "proper-base-change") (uses := "thm:proper-base-change, thm:pbc-curves, lemma:pbc-finite") (lean := "AlgebraicGeometry.Scheme.finite_H_of_isProper")
(SGA 4 XIV.) Let $`X` be proper over a separably closed field and let $`M` be a
finite abelian group. Then the étale cohomology groups $`H^q(X, M)` are finite.
:::

:::proof "thm:pbc-finiteness"
Induction on the dimension. After reducing to projective $`X` by Chow's lemma and the
finite case ({bpref "lemma:pbc-finite"}[]), fiber $`X` in curves over a base of
smaller dimension. By proper base change ({bpref "thm:proper-base-change"}[]) the
stalks of the higher direct images along the fibration are the cohomologies of the
fibers, which are finite by the curve case ({bpref "thm:pbc-curves"}[]), and the
higher direct images are constructible; the Leray spectral sequence and the induction
hypothesis (extended from constant to constructible coefficients by dévissage)
conclude.
:::

:::theorem "thm:elladic-comparison-proper" (parent := "proper-base-change") (uses := "thm:pbc-finiteness") (lean := "AlgebraicGeometry.Scheme.existsUnique_ellAdicCohomology_addEquiv_limit_of_isProper")
For $`X` proper over a separably closed field and $`\ell` prime, there is a unique
additive equivalence
$$`H^{i+1}(X_{\mathrm{pro\acute{e}t}}, \widehat{\mathbb{Z}}_\ell) \simeq
\varprojlim_n H^{i+1}(X_{\acute{e}t}, \mathbb{Z}/\ell^n)`
compatible with the canonical comparison maps — the finiteness hypothesis of the
general comparison theorem holds automatically by
{bpref "thm:pbc-finiteness"}[].
:::

:::proof "thm:elladic-comparison-proper"
Immediate from the general comparison theorem and
{bpref "thm:pbc-finiteness"}[] applied to $`M = \mathbb{Z}/\ell^n`. This deduction
is a complete Lean proof.
:::
