# Elliptic Curves

This project formalizes some of the arithmetic of elliptic curves over number fields (and, more
generally, over fraction fields of Dedekind domains) in Lean 4. Its centerpieces are a complete
proof of the **Mordell-Weil Theorem** and the machinery of **explicit 2-descent**: the 2-Selmer
group, the formal group of an elliptic curve over a local field, and the local computations that
feed a rank bound. The development is `sorry`-free.

It grew out of the [Heights](https://github.com/MichaelStollBayreuth/Heights) project and was split
off from it once it became independent of the heights implementation there: the general theory of
height functions (admissible absolute values, the Northcott property, heights on projective space,
heights under polynomial maps) has meanwhile been upstreamed to Mathlib
(`Mathlib.NumberTheory.Height`), and this repository builds on it.

Everything under [`EllipticCurves/Mathlib/`](EllipticCurves/Mathlib) is general-purpose support
that has nothing intrinsically to do with the elliptic-curve application and is intended for
eventual upstreaming to Mathlib; the elliptic-curve-specific development lives directly under
[`EllipticCurves/`](EllipticCurves).

## The Mordell-Weil Theorem

The group `E(K)` of `K`-rational points of an elliptic curve `E` over a number field `K` is
finitely generated. The end result is `WeierstrassCurve.Affine.fg_point_of_numberField` in
[`MordellWeil.lean`](EllipticCurves/MordellWeil.lean), for arbitrary Weierstrass models. It is
deduced from the more general `fg_point`, which works for `E` given by a Weierstrass equation
`y² = x³ + a₂·x² + a₄·x + a₆` (so with `a₁ = a₃ = 0`) over the fraction field `K` of a Dedekind
domain `R` such that `K` has admissible absolute values satisfying the Northcott property and such
that for each irreducible factor `p` of the cubic, the integral closure of `R` in `K[X]/(p)` has
finite class group and finitely generated unit group. (These per-factor hypotheses cannot be
replaced by the corresponding hypotheses on `R` itself; see the docstring of `fg_point`.) The
reduction to this normal form (`fg_point_of_variableChange`) completes the square via an admissible
change of variables, which is possible whenever `2` is invertible in `K`, and uses the induced
computable isomorphism of point groups `(C • W).Point ≃+ W.Point` from
[`VariableChange.lean`](EllipticCurves/VariableChange.lean) (shared with the FLT project).

The proof follows the classical route:

* The **descent** step is Mathlib's `AddCommGroup.fg_of_descent'` (an abelian group carrying a
  suitable height function with `G/2G` finite is finitely generated), originally developed in the
  Heights project and since upstreamed.
* The **height function**: [`MordellWeil.lean`](EllipticCurves/MordellWeil.lean) shows that the
  naïve height `h(P) = logHeight (x(P))` on `E(K)` satisfies the *approximate parallelogram law*
  `|h(P+Q) + h(P−Q) − 2·h(P) − 2·h(Q)| ≤ C` (`approx_parallelogram_law`), using Mathlib's bounds
  on heights of images under tuples of homogeneous polynomials, and that sets of points of bounded
  height are finite when `K` has the Northcott property (`finite_naiveHeight_le`). This also yields
  the finiteness of the torsion subgroup of `E(K)` (`finite_torsion`).
* The **Weak Mordell-Weil Theorem** (below) supplies the finiteness of `E(K)/2E(K)`.

## Explicit 2-descent and the 2-Selmer group

* The **Weak Mordell-Weil Theorem**: `E(K)/2E(K)` is finite. This is
  `finite_index_range_nsmulAddMonoidHom_two` in
  [`WeakMordellWeil.lean`](EllipticCurves/WeakMordellWeil.lean), proved over fraction fields of
  Dedekind domains (with the finiteness hypotheses above) via the `x − T` descent map: `E(K)/2E(K)`
  embeds into the group `Aˣ/(Aˣ)²` of square classes of the étale algebra `A = K[X]/(f)` for the
  cubic `f` with `y² = f(x)`, with image contained in the 2-Selmer group `A(S, 2)` for the finite
  set `S` of bad primes, and the latter group is finite
  (`IsDedekindDomain.finite_selmerGroup`). The image also lies in the kernel of the norm map, which
  is not needed for finiteness but cuts the group down in explicit computations
  (`AdjoinRoot.norm_mk_eq_resultant`).

* The **2-Selmer group** of an elliptic curve is set up in
  [`SelmerGroup.lean`](EllipticCurves/SelmerGroup.lean): the local conditions
  `W.localCondition L ≤ Units.modPow W.A 2` at the completions of `K`, the Selmer group
  `W.selmerGroup₂` as a subgroup of the square classes of the étale algebra cut out by them, and:
  * `range_μ_le_selmerGroup₂` together with `ker μ = 2E(K)` bounds `E(K)/2E(K)` by the Selmer group;
  * `card_range_μ` gives `#(im μ) = 2^(rank E(K)) · #E(K)[2]`, whence the rank bound
    `pow_rank_le_card_of_range_μ_le`;
  * `selmerGroup₂_eq_badPrimes` (over a number field) reduces membership to the *finitely many*
    local conditions at the bad and infinite places, inside the finite group `A(S,2) ⊓ ker N`, so
    the Selmer group is finite (`finite_selmerGroup₂`);
  * the local image sizes `#E(K_v)[2] · ‖2‖_v⁻¹` are computed at every place
    (`card_range_μ_adicCompletion`, `card_range_μ_completion_isReal`,
    `card_range_μ_completion_isComplex`) — the real case by the sign analysis over `ℝ` of
    [`Mathlib/RealEtale.lean`](EllipticCurves/Mathlib/RealEtale.lean).

  The whole reduction is fully proved; it rests on the formal-group results described next.

The goal towards which this machinery is aimed is a formal proof that the Mordell-Weil group of
`y² = x³ − x + 1` over `ℚ` is isomorphic to `ℤ`, as a show-piece for formalized explicit 2-descent.

## Formal groups over local fields

The local input to the 2-descent — the structure of `E(K_v)` and the size of the group of
everywhere-unramified square classes — comes from the theory of formal groups, developed here in
full (in the Heights project these statements were `sorry`ed).

* [`WeierstrassFormalGroup/`](EllipticCurves/WeierstrassFormalGroup) (seven files)
  builds the formal group of a Weierstrass curve and its consequences: the fixed-point series
  `w(t)` and the chord data ([`Chord.lean`](EllipticCurves/WeierstrassFormalGroup/Chord.lean),
  [`ThirdPoint.lean`](EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean)), the formal
  group law `WeierstrassCurve.formalGroupLaw`
  ([`GroupLaw.lean`](EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean)), the valuation
  estimates for an integral model
  ([`Foundations.lean`](EllipticCurves/WeierstrassFormalGroup/Foundations.lean),
  [`Eval.lean`](EllipticCurves/WeierstrassFormalGroup/Eval.lean)), the formal point, the
  filtration `E_{n+1}(K_v)` and the structure theorem — `E(K_v)` has a finite-index subgroup
  isomorphic to `(𝒪_v, +)`, and `E₁(K_v)` is torsion-free under the standard ramification condition
  ([`Filtration.lean`](EllipticCurves/WeierstrassFormalGroup/Filtration.lean)) — and the
  point-level reduction homomorphism `redHom : E(K_v) → Ẽ(k_v)`, injective on torsion and
  order-preserving there
  ([`Reduction.lean`](EllipticCurves/WeierstrassFormalGroup/Reduction.lean)).
* [`Mathlib/AdicFormalGroupLog.lean`](EllipticCurves/Mathlib/AdicFormalGroupLog.lean): the
  `π^e`-scaled formal logarithm over `𝒪_v`, which has integral coefficients and an integral
  compositional inverse, giving the isomorphism of a deep filtration step with `(𝒪_v, +)`.
* [`Mathlib/Chabauty/`](EllipticCurves/Mathlib/Chabauty): a general multivariate formal-group-law
  kit (vendored from the author's Chabauty–Coleman formalization) — `ChabautyColeman.FormalGroupLaw`
  and its `𝔪`-points, the formal logarithm/exponential and their `p`-adic estimates, and the
  logarithm isomorphism, over the multivariate power-series evaluation layer of `MvPSeries.lean`.
* [`IntegralModel.lean`](EllipticCurves/IntegralModel.lean): every Weierstrass curve over `K_v`
  has an integral model — after an admissible change of variables its coefficients lie in `𝒪_v`
  (`exists_variableChange_map_eq`) — the input to the finite-index structure theorem above.
* [`Mathlib/FormalGroup.lean`](EllipticCurves/Mathlib/FormalGroup.lean): the multiplicative (`𝔾ₘ`)
  analogue of that structure theorem, `card_selmerGroup_integralClosure` — for odd residue
  characteristic, the group of everywhere-unramified square classes of a finite separable extension
  of `K_v` has order `2` (proved via Henselianity of `𝒪_v`, using
  [`Mathlib/Henselian.lean`](EllipticCurves/Mathlib/Henselian.lean)).

## An infinite-order certificate

[`InfiniteOrder.lean`](EllipticCurves/InfiniteOrder.lean) turns the reduction map into a certificate
for a point of `E(K)` to have **infinite order**: since base change `E(K) → E(K_v)` is injective
(`pointMap_injective`) and reduction is injective on torsion, a nonzero point whose reductions at
two good primes are torsion of *coprime* orders cannot itself be torsion
(`not_isOfFinAddOrder_of_coprime_red`, with the single-prime bridge
`nsmul_eq_zero_of_red_pointMap_nsmul_eq_zero`).

[`InfiniteOrderExample.lean`](EllipticCurves/InfiniteOrderExample.lean) instantiates the input for
`P = (1, 1)` on `y² = x³ − x + 1`: modulo `3` the reduced point is killed by `7` (`#E(𝔽₃) = 7`) and
modulo `5` by `8` (`#E(𝔽₅) = 8`), and `gcd(7, 8) = 1`. Because Mathlib's point addition is
noncomputable, these torsion facts (`nsmul_seven_eq_zero_mod_three`, `nsmul_eight_eq_zero_mod_five`)
are computed by hand from the explicit group-law formulas rather than by `decide`. Assembling the
full statement that `(1, 1) ∈ E(ℚ)` has infinite order — which additionally needs the abstract
residue field of `𝒪_v` identified with `ZMod p` and the `p`-adic integral model — is left as future
work.

## Supporting theory intended for Mathlib

Beyond the formal-group files above, [`EllipticCurves/Mathlib/`](EllipticCurves/Mathlib) contains:

* [`FractionalIdeal.lean`](EllipticCurves/Mathlib/FractionalIdeal.lean): the group of invertible
  fractional ideals of a Dedekind domain is free abelian on the height one primes
  (`FractionalIdeal.factorization`); `n`-th roots of `n`-divisible fractional ideals
  (`exists_pow_eq`).
* [`SIntegers.lean`](EllipticCurves/Mathlib/SIntegers.lean): the ring `𝒪_S` of `S`-integers of `K`
  is a Dedekind domain with fraction field `K`; its height one primes are exactly the `v ∉ S`; and
  its class group is `Cl(R)` modulo the classes of the primes in `S`. (`𝒪_S` is in general *not* a
  localization of `R`; see the file for a warning.)
* [`SelmerGroup.lean`](EllipticCurves/Mathlib/SelmerGroup.lean): the fundamental exact sequence
  `1 → 𝒪_S^× / (𝒪_S^×)ⁿ → K(S, n) → Cl_S(R)[n] → 1` for the Selmer group `K(S, n)`, whence `K(S, n)`
  is finite when `S` is finite, `Cl(R)` is finite and `R^×` is finitely generated
  (`finite_selmerGroup`; a `TODO` in Mathlib), together with the version for étale algebras. On the
  way, Dirichlet's `S`-unit theorem (`𝒪_S^×` finitely generated, of rank `rank R^× + #S`).
* [`Basic.lean`](EllipticCurves/Mathlib/Basic.lean): general-purpose ingredients, e.g. the group
  `Units.modPow A n` of units modulo `n`-th powers, the decomposition of an étale algebra
  `K[X]/(f)` (for `f` squarefree) into a product of field factors, norms on `AdjoinRoot` via
  resultants (`AdjoinRoot.norm_mk_eq_resultant`), and the primes of an extension lying above a set
  of primes.
* [`AdicCompletionExtension.lean`](EllipticCurves/Mathlib/AdicCompletionExtension.lean): the
  extension `K_v →+* L_w` of adic completions along an extension of Dedekind domains with `w ∣ v`,
  its compatibility with the valuations (up to ramification) and rings of integers (adapted from the
  FLT project), and the Henselianity of the complete DVR `𝒪_v`.
* [`RealEtale.lean`](EllipticCurves/Mathlib/RealEtale.lean): the sign decomposition of `ℝ[X]/f` and
  the square classes of its units as sign patterns at the real roots (used at the real places, and
  intended to generalize to hyperelliptic descent maps).
* [`Henselian.lean`](EllipticCurves/Mathlib/Henselian.lean): finite algebras over a Henselian local
  ring are products of local rings, and finite local ones are again Henselian (vendored from the FLT
  project).

## Layout

The Lean source lives under [`EllipticCurves/`](EllipticCurves); the root module
[`EllipticCurves.lean`](EllipticCurves.lean) imports every module in the project (regenerate with
`lake exe mk_all`). The project is built against a pinned version of Mathlib (see
[`lakefile.toml`](lakefile.toml) and [`lean-toolchain`](lean-toolchain)); run
`lake exe cache get` before `lake build`.
