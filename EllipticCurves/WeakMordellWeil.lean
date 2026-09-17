/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import EllipticCurves.Mathlib.Basic
public import EllipticCurves.Mathlib.SelmerGroup
public import Mathlib

@[expose] public section

/-!
# The Weak Mordell-Weil Theorem

Let `E` be an elliptic curve given by a Weierstrass equation `y² = x³ + a₂x² + a₄x + a₆ =: f(x)`
(so with `a₁ = a₃ = 0`, which is always achievable when the characteristic is not `2`) over the
fraction field `K` of a Dedekind domain `R`. This file shows that `E(K)/2E(K)` is finite under
finiteness hypotheses — finite class group and finitely generated unit group for the rings of
integers of the field factors of `K[X]/⟨f⟩` — that are theorems when `K` is a number field. The
proof is the classical `x - T` map argument; the general-purpose material developed along the way
lives in `EllipticCurves.Mathlib.Basic`.

## Main definitions

* `WeierstrassCurve.Affine.f`: the cubic `X ^ 3 + a₂ X ^ 2 + a₄ X + a₆`, and
  `WeierstrassCurve.Affine.A`: the étale algebra `K[X]/⟨f⟩`.
* `WeierstrassCurve.Affine.M`: the group `Aˣ/(Aˣ)²` of square classes, and
  `WeierstrassCurve.Affine.μ : Multiplicative E(K) →* M`, the `x - T` map: `μ (x, y)` is the
  class of `x - T` if `f x ≠ 0` and the class of `f' T` otherwise (the underlying plain map is
  `WeierstrassCurve.Affine.μ₀`).
* `WeierstrassCurve.Affine.badPrimes`: the primes of `R` dividing `2` or `Δ` or occurring in a
  denominator of a coefficient, and `WeierstrassCurve.Affine.selmerGroupA`: the subgroup `A(S,2)`
  of `M` of the classes whose valuation is even at every prime of a field factor of `A` not lying
  above `S`.

## Main statements

* `WeierstrassCurve.Affine.ker_μ_eq`: the kernel of `μ` is `2E(K)`.
* `WeierstrassCurve.Affine.range_μ_le_selmerGroupA`: `im μ ⊆ A(S,2)` for every `S` outside of
  which the coefficients of `f` are integral and `disc f` is a unit.
* `WeierstrassCurve.Affine.finite_selmerGroupA`: `A(S,2)` is finite for finite `S`, given that
  the ring of integers of each field factor has finite class group and finitely generated unit
  group, and `WeierstrassCurve.Affine.finite_index_range_nsmulAddMonoidHom_two`: **the weak
  Mordell-Weil theorem**, `2E(K)` has finite index in `E(K)`.

## Outline of the proof

1. `A := K[X]/⟨f⟩` is a finite étale `K`-algebra, as `f` is separable
   (`WeierstrassCurve.Affine.separable_f`).
2. `M := Aˣ/(Aˣ)²`, and the plain map `μ₀ : E(K) → M`.
3. `μ₀` is multiplicative (`WeierstrassCurve.Affine.μ₀_mul_mul_eq_one_of_add_add_eq_zero`, from
   the collinearity of three points summing to `0`), so it is a group homomorphism `μ`.
4. `ker μ = 2E(K)` (`WeierstrassCurve.Affine.exists_eq_two_smul_iff` and
   `WeierstrassCurve.Affine.eq_two_smul_of_μ_eq_one`).
5. `im μ ⊆ ker (norm)`: not needed for finiteness, so it lives in `EllipticCurves.SelmerGroup`
   (`WeierstrassCurve.Affine.range_μ_le_ker_normM`).
6. `im μ ⊆ A(S,2)`, checked factor by factor by a valuation computation inside each field factor
   `K[X]/⟨p⟩` (`WeierstrassCurve.Affine.even_valuationOfNeZero_sub_root`).
7. `A(S,2)` is finite: the `2`-Selmer group of each field factor is finite by
   `IsDedekindDomain.finite_selmerGroup` (in `EllipticCurves.Mathlib.SelmerGroup`).

The material about `μ` that the finiteness proof does not use — the norm computation of Step 5,
the `2`-torsion of `E(K)`, the refined sets of bad primes and the cardinality bound for `A(S,2)` —
lives in `EllipticCurves.SelmerGroup`.
-/

/-!
### Two commutative-ring identities

These are used in Step 3 (`μ` is a homomorphism); they encode the multiplicativity of the
`x - T` map on the level of coordinates.
-/

section CommRing

variable {R : Type*} [CommRing R]

/-- If `a * b * c = 0`, then `a * b + a * c + b * c` is a square root of the product
of the `b * c - a` and its two analogues. -/
lemma sq_add_add_eq_mul_mul_of_mul_mul_eq_zero {a b c : R} (h : a * b * c = 0) :
    (a * b + a * c + b * c) ^ 2 = (b * c - a) * (a * c - b) * (a * b - c) := by
  linear_combination (a ^ 2 - a * b * c + 2 * a + b ^ 2 + 2 * b + c ^ 2 + 2 * c + 1) * h

/-- If `a * d = 0` and `b * c = d - e ^ 2 * a`, then `d + e * a` is a square root
of `(d - a) * b * c`. -/
lemma sq_add_mul_eq_mul_mul_of_mul_eq_zero {a b c d e : R} (had : a * d = 0)
    (h : b * c = d - e ^ 2 * a) : (d + e * a) ^ 2 = (d - a) * b * c := by
  grobner

end CommRing

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

/-!
### Step 1: define `A`
-/

open Polynomial

/-- The polynomial on the right hand side of a Weierstrass equation with `a₁ = a₃ = 0`. -/
noncomputable abbrev f : K[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

lemma natDegree_f : W.f.natDegree = 3 := by
  simp only [f]
  compute_degree!

lemma monic_f : W.f.Monic := by
  simp only [f]
  monicity!

lemma f_ne_zero : W.f ≠ 0 := W.monic_f.ne_zero

lemma degree_f : W.f.degree = 3 := by
  rw [degree_eq_natDegree W.f_ne_zero, natDegree_f]; rfl

/-- The discriminant of the cubic `f`, in terms of the coefficients of `W`. -/
lemma discr_f : W.f.discr = W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆
    - 27 * W.a₆ ^ 2 + 18 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Polynomial.discr_of_degree_eq_three W.degree_f]
  simp only [f, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- In char ≠ 2 normal form, `Δ = 16 · disc f`; in particular the two agree up to a unit away
from `2`, but *not* at even places, where `disc f` is the finer invariant. -/
lemma Δ_eq_discr_f [W.IsCharNeTwoNF] : W.Δ = 16 * W.f.discr := by
  rw [Δ_of_isCharNeTwoNF W, W.discr_f]; ring

lemma discr_f_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] : W.f.discr ≠ 0 := fun h ↦
  W.isUnit_Δ.ne_zero (by rw [W.Δ_eq_discr_f, h, mul_zero])

/-- The base field of an elliptic curve in the normal form `a₁ = a₃ = 0` has characteristic
different from `2`: its discriminant is `16` times the discriminant of
`WeierstrassCurve.Affine.f`. -/
protected lemma two_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] : (2 : K) ≠ 0 := fun h2 ↦
  W.isUnit_Δ.ne_zero <| by rw [Δ_eq_discr_f]; grind [W.discr_f_ne_zero]

lemma derivative_f : derivative W.f = C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄ := by
  simp [f, C_ofNat]
  ring

/-- The derivative of the cubic `f` is honestly quadratic when `3 ≠ 0` in `K`. -/
lemma natDegree_derivative_f (h3 : (3 : K) ≠ 0) : (derivative W.f).natDegree = 2 :=
  W.derivative_f ▸ natDegree_quadratic h3

/-- The Bézout identity between the cubic `f` and its derivative, with the discriminant on the
right: `f * d + f' * c = disc f` for an explicit linear `d` and quadratic `c`, stated in an
arbitrary `K`-algebra. The coefficients of `c` and `d` are integer polynomials in `a₂`, `a₄`,
`a₆`, so they are integral wherever the coefficients of `W` are. -/
lemma aeval_f_mul_add_aeval_derivative_f_mul_eq_discr {A : Type*} [CommRing A] [Algebra K A]
    (t : A) :
    aeval t W.f * ((18 * algebraMap K A W.a₄ - 6 * algebraMap K A W.a₂ ^ 2) * t
        + (15 * algebraMap K A W.a₂ * algebraMap K A W.a₄ - 4 * algebraMap K A W.a₂ ^ 3
          - 27 * algebraMap K A W.a₆))
      + aeval t (derivative W.f) * ((2 * algebraMap K A W.a₂ ^ 2 - 6 * algebraMap K A W.a₄) * t ^ 2
        + (2 * algebraMap K A W.a₂ ^ 3 - 7 * algebraMap K A W.a₂ * algebraMap K A W.a₄
          + 9 * algebraMap K A W.a₆) * t
        + (algebraMap K A W.a₂ ^ 2 * algebraMap K A W.a₄ - 4 * algebraMap K A W.a₄ ^ 2
          + 3 * algebraMap K A W.a₂ * algebraMap K A W.a₆)) = algebraMap K A W.f.discr := by
  rw [derivative_f, discr_f]
  simp only [f, map_add, map_mul, map_pow, map_sub, map_ofNat, aeval_C, aeval_X]
  ring

lemma separable_f [W.IsElliptic] [W.IsCharNeTwoNF] : W.f.Separable := by
  have h := W.aeval_f_mul_add_aeval_derivative_f_mul_eq_discr (X : K[X])
  simp only [aeval_X_left, AlgHom.id_apply, algebraMap_eq] at h
  obtain ⟨d, c, h⟩ : ∃ d c : K[X], W.f * d + derivative W.f * c = C W.f.discr := ⟨_, _, h⟩
  refine ⟨C W.f.discr⁻¹ * d, C W.f.discr⁻¹ * c, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, mul_comm d, mul_comm c, h, ← C_mul,
    inv_mul_cancel₀ W.discr_f_ne_zero, C_1]

lemma squarefree_f [W.IsElliptic] [W.IsCharNeTwoNF] : Squarefree W.f :=
  (separable_f W).squarefree

lemma eval_f (x : K) : W.f.eval x = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by simp [f]

lemma map_eval_f {L : Type*} [CommRing L] [Algebra K L] (x : K) :
    algebraMap K L (W.f.eval x) = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
  simp [f]

lemma equation_iff_eval_f_eq_sq [W.IsCharNeTwoNF] (x y : K) :
    W.Equation x y ↔ W.f.eval x = y ^ 2 := by
  rw [equation_iff x y, eq_comm]
  simp [f]

@[simp]
lemma negY_of_isCharNeTwoNF [W.IsCharNeTwoNF] (x y : K) : W.negY x y = -y := by
  rw [negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring

/-- For a curve in the normal form `a₁ = a₃ = 0`, the slope of the tangent at `(x, y)` is
`(3 * x ^ 2 + 2 * a₂ * x + a₄) / (2 * y)`; the hypothesis `y ≠ W.negY x y` says `2 * y ≠ 0`. -/
lemma slope_self_of_isCharNeTwoNF [DecidableEq K] [W.IsCharNeTwoNF] {x y : K}
    (hy : y ≠ W.negY x y) :
    W.slope x x y y = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) / (2 * y) := by
  rw [slope_of_Y_ne rfl hy, negY_of_isCharNeTwoNF, a₁_of_isCharNeTwoNF, zero_mul, sub_zero,
    sub_neg_eq_add, ← two_mul]

/-- On a point of `W`, the value `f x` is a square, so it vanishes exactly when `y` does. -/
lemma ne_zero_of_eval_f_ne_zero [W.IsCharNeTwoNF] {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) : y ≠ 0 :=
  fun h0 ↦ hx <| by simp [(equation_iff_eval_f_eq_sq W x y).mp h, h0]

/-- The quotient of `f` by `X - x`. -/
noncomputable abbrev fCofactor (x : K) : K[X] :=
  X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)

lemma natDegree_fCofactor (x : K) : (W.fCofactor x).natDegree = 2 := by
  simp only [fCofactor]
  compute_degree!

lemma monic_fCofactor (x : K) : (W.fCofactor x).Monic := by
  simp only [fCofactor]
  monicity!

lemma eval_fCofactor_self (x : K) :
    (W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
  simp [fCofactor]
  ring

lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp [fCofactor, f]
  algebra

/-- Dividing `W.fCofactor x` by `X - C x` once more leaves the remainder
`3 * x ^ 2 + 2 * W.a₂ * x + W.a₄`, the derivative of `WeierstrassCurve.Affine.f` at `x`; so
`C x - X` is invertible modulo `W.fCofactor x` as soon as that derivative is nonzero. -/
lemma C_sub_X_mul_eq_C_sub_fCofactor (x : K) :
    (C x - X) * (X + C (2 * x + W.a₂)) = C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) - W.fCofactor x := by
  simp only [fCofactor, C_eq_algebraMap]
  algebra

lemma f_eq_mul_of_eval_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.f = W.fCofactor x * (X - C x) := by
  simp [fCofactor_mul_eq, hx]

lemma discr_fCofactor (x : K) :
    (W.fCofactor x).discr = (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) := by
  have hdeg : (W.fCofactor x).degree = 2 := by
    rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, W.natDegree_fCofactor x]; rfl
  rw [discr_of_degree_eq_two hdeg]
  simp only [fCofactor, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- If `x` is a root of `f`, splitting off the factor `X - x` writes `disc f` as
`(fCofactor x).discr * f'(x) ^ 2`. -/
lemma discr_f_eq_discr_fCofactor_mul_sq {x : K} (hx : W.f.eval x = 0) :
    W.f.discr = (W.fCofactor x).discr * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ^ 2 := by
  conv_lhs => rw [W.f_eq_mul_of_eval_eq_zero hx, mul_comm]
  rw [discr_X_sub_C_mul (W.monic_fCofactor x) (by rw [W.natDegree_fCofactor]; norm_num) x,
    W.eval_fCofactor_self x]

/- Dividing the relation `(r X + s)² ≡ x - X mod (fCofactor x)` by `r²` yields the polynomial
identity certifying that a point with `2`-torsion `x`-coordinate `x` is divisible by `2`
(used in Step 4). -/
private lemma f_dvd_of_fCofactor_dvd {x r s : K} (hx : W.f.eval x = 0) (hr : r ≠ 0)
    (hdvd : W.fCofactor x ∣ (C r * X + C s) ^ 2 - (C x - X)) :
    W.f ∣ (X - C (-s / r)) ^ 2 * (X - C x) - -(C (1 / r) * X + C (-x / r)) ^ 2 := by
  obtain ⟨q, hq⟩ := hdvd
  have hu : C r * C r⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hr, C_1]
  refine ⟨C (r⁻¹ ^ 2) * q, ?_⟩
  rw [W.f_eq_mul_of_eval_eq_zero hx]
  simp only [div_eq_mul_inv, map_mul, map_neg, one_mul, map_pow]
  grobner

/- A square of a class of degree `< g.natDegree / 2` is not the class of `C x - X` modulo a
monic `g` of degree `≥ 2`: both sides have degree `< g.natDegree`, so they would be equal as
polynomials, but a square has even degree (used in Step 4). -/
private lemma mk_sq_ne_mk_C_sub_X {g : K[X]} (hg : g.Monic) (hg2 : 2 ≤ g.natDegree) {q : K[X]}
    (hq : 2 * q.natDegree < g.natDegree) (x : K) :
    AdjoinRoot.mk g q ^ 2 ≠ AdjoinRoot.mk g (C x - X) := by
  have hx : (C x - X).natDegree = 1 := by compute_degree!
  rw [← map_pow, Ne, AdjoinRoot.mk_eq_mk_iff_of_degree_lt hg
    (degree_lt_degree (natDegree_pow_le.trans_lt hq)) (degree_lt_degree (by lia))]
  intro h
  have := congrArg natDegree h
  rw [natDegree_pow, hx] at this
  lia

lemma fCofactor_eq_of_f_eq {xP xQ xR : K} (hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR)) :
    W.fCofactor xP = (X - C xQ) * (X - C xR) ∧ W.fCofactor xQ = (X - C xP) * (X - C xR) ∧
      W.fCofactor xR = (X - C xP) * (X - C xQ) := by
  have key {u v w : K} (h : W.f = (X - C u) * ((X - C v) * (X - C w))) :
      W.fCofactor u = (X - C v) * (X - C w) := by
    have h₀ : W.f.eval u = 0 := by rw [h]; simp
    refine mul_left_cancel₀ (X_sub_C_ne_zero u) ?_
    rw [← h, W.f_eq_mul_of_eval_eq_zero h₀, mul_comm]
  exact ⟨key <| by rw [hf]; ring, key <| by rw [hf]; ring, key <| by rw [hf]; ring⟩

/-- `f'` does not vanish at a root of `f`: evaluating the Bézout identity
`WeierstrassCurve.Affine.aeval_f_mul_add_aeval_derivative_f_mul_eq_discr` there leaves
`f'(x) * c(x) = disc f ≠ 0`. -/
lemma deriv_f_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := by
  have h := W.aeval_f_mul_add_aeval_derivative_f_mul_eq_discr x
  simp only [coe_aeval_eq_eval, Algebra.algebraMap_self, RingHom.id_apply, hx, zero_mul, zero_add,
    derivative_f, eval_add, eval_mul, eval_C, eval_X, eval_pow] at h
  exact left_ne_zero_of_mul (h ▸ W.discr_f_ne_zero)

/-- The étale algebra associated to a Weierstrass curve with `a₁ = a₃ = 0`. -/
abbrev A : Type _ := AdjoinRoot W.f

lemma finrank_A : Module.finrank K W.A = 3 := by
  rw [(AdjoinRoot.powerBasis W.f_ne_zero).finrank, AdjoinRoot.powerBasis_dim, natDegree_f]

lemma exists_mk_eq (a : W.A) :
    ∃ r s t, a = AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq W.monic_f a
  rw [degree_eq_natDegree W.monic_f.ne_zero, natDegree_f] at hp
  exact ⟨_, _, _, congrArg (AdjoinRoot.mk W.f) <|
    eq_quadratic_of_degree_le_two <| Order.lt_succ_iff.mp hp⟩

lemma exists_X_sub_C_mul_eq (r s t : K) (hr : r ≠ 0) :
    ∃ ξ l m, AdjoinRoot.mk W.f (X - C ξ) * AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) =
       AdjoinRoot.mk W.f (C l * X + C m) := by
  have hu : C r * C r⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hr, C_1]
  refine ⟨s / r - W.a₂, t - W.a₄ * r - s ^ 2 / r + W.a₂ * s,
    -W.a₆ * r - t * s / r + W.a₂ * t, ?_⟩
  rw [← map_mul, ← sub_eq_zero, ← map_sub, AdjoinRoot.mk_eq_zero]
  refine ⟨C r, ?_⟩
  simp only [f, div_eq_mul_inv, map_sub, map_add, map_mul, map_pow, map_neg]
  grobner

/-- The étale algebra associated to the cofactor of `f`. -/
abbrev A' (x : K) : Type _ := AdjoinRoot (W.fCofactor x)

lemma exists_mk_eq' {x : K} (a : W.A' x) :
    ∃ r s, a = AdjoinRoot.mk (W.fCofactor x) (C r * X + C s) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq (W.monic_fCofactor x) a
  rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, natDegree_fCofactor] at hp
  exact ⟨_, _, congrArg (AdjoinRoot.mk (W.fCofactor x)) <|
    eq_X_add_C_of_natDegree_le_one <| natDegree_le_of_degree_le <| Order.lt_succ_iff.mp hp⟩

/-- The Chinese Remainder Theorem isomorphism `K[X]⧸f ≃ K × K[X]/cf`, where `cf` is the cofactor
`f / (X - x)`. -/
noncomputable def equivProdA' [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    W.A ≃+* K × W.A' x :=
  let eA : W.A ≃+* K[X] ⧸ (Ideal.span {X - C x} * Ideal.span {W.fCofactor x}) :=
    Ideal.quotEquivOfEq <| by
      rw [Ideal.span_singleton_mul_span_singleton, mul_comm, ← W.f_eq_mul_of_eval_eq_zero hx]
  have H : IsCoprime (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr <|
      (W.f_eq_mul_of_eval_eq_zero hx ▸ separable_f W).isCoprime.symm
  eA.trans <|
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x})
      H).trans <|
    RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv x |>.toRingEquiv) (RingEquiv.refl _)

lemma equivProdA'_apply [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) (p : K[X]) :
    W.equivProdA' hx (AdjoinRoot.mk W.f p) = (p.eval x, AdjoinRoot.mk (W.fCofactor x) p) :=
  rfl

lemma mk_eq_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p q : K[X]} :
    AdjoinRoot.mk W.f p = AdjoinRoot.mk W.f q ↔
      p.eval x = q.eval x ∧ AdjoinRoot.mk (W.fCofactor x) p = AdjoinRoot.mk (W.fCofactor x) q := by
  rw [← EquivLike.apply_eq_iff_eq <| W.equivProdA' hx]
  simpa only [equivProdA'_apply] using Prod.mk_inj

lemma isUnit_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p : K[X]} :
    IsUnit (AdjoinRoot.mk W.f p) ↔
      IsUnit (p.eval x) ∧ IsUnit (AdjoinRoot.mk (W.fCofactor x) p) := by
  let e := W.equivProdA' hx
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · have : IsUnit (e _) := e.toRingHom.isUnit_map H
    rwa [W.equivProdA'_apply hx, Prod.isUnit_iff] at this
  · have : IsUnit (eval x p, AdjoinRoot.mk (W.fCofactor x) p) := by rwa [Prod.isUnit_iff]
    have : IsUnit (e.symm _) := e.symm.toRingHom.isUnit_map this
    convert this
    rw [RingEquiv.eq_symm_apply, W.equivProdA'_apply hx]

variable {W}

lemma isUnit_mk_sub_X_of_eval_f_ne_zero {x : K} (h : W.f.eval x ≠ 0) :
    IsUnit <| AdjoinRoot.mk W.f (C x - X) := by
  refine .of_mul_eq_one (AdjoinRoot.mk W.f (C (W.f.eval x)⁻¹ * W.fCofactor x)) ?_
  rw [← map_mul, mul_left_comm,
    show (1 : W.A) = AdjoinRoot.mk W.f (1 - C (eval x W.f)⁻¹ * W.f) by simp]
  congr 1
  have h1 : (C x - X) * W.fCofactor x = C (W.f.eval x) - W.f := by
    linear_combination -W.fCofactor_mul_eq x
  rw [h1, mul_sub, ← C_mul, inv_mul_cancel₀ h, map_one]

section

variable [W.IsCharNeTwoNF]

lemma y_eq_zero_of_eval_f_eq_zero {x y : K} (h : W.Equation x y) (hf : W.f.eval x = 0) :
    y = 0 := by
  rwa [equation_iff_eval_f_eq_sq, hf, eq_comm, sq_eq_zero_iff] at h

variable [W.IsElliptic]

lemma isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero {x : K} (h : W.f.eval x = 0) :
    IsUnit <| AdjoinRoot.mk W.f <| C x - X + W.fCofactor x := by
  have H : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := deriv_f_ne_zero W h
  rw [isUnit_mk_iff W h, map_add, AdjoinRoot.mk_self, add_zero]
  refine ⟨?_, .of_mul_eq_one (AdjoinRoot.mk _
    (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂)))) ?_⟩
  · simpa [isUnit_iff_ne_zero, W.eval_fCofactor_self] using H
  · rw [← map_mul, mul_left_comm, W.C_sub_X_mul_eq_C_sub_fCofactor, mul_sub, ← C_mul]
    simp [inv_mul_cancel₀ H]

/-- The point `(x, 0)` at a root of `f` lies on the curve. -/
lemma nonsingular_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.Nonsingular x 0 :=
  (equation_iff_nonsingular_of_Δ_ne_zero W.isUnit_Δ.ne_zero).mp
    (by rw [equation_iff_eval_f_eq_sq, hx]; ring)

end

/-!
### Step 2: define `M` and `μ` as a plain map `μ₀`
-/

/-- The group of square classes of units of `W.A`. -/
abbrev M : Type _ := Units.modPow W.A 2

lemma M.sq_eq_one (m : W.M) : m ^ 2 = 1 := Units.modPow.pow_eq_one m

lemma M.mul_self (m : W.M) : m * m = 1 := by rw [← sq, sq_eq_one]

@[simp] lemma M.inv_eq_self (m : W.M) : m⁻¹ = m := inv_eq_of_mul_eq_one_right (M.mul_self m)

variable [DecidableEq K] [W.IsCharNeTwoNF]

section μ₀

variable [W.IsElliptic]

/-- The descent or `x - T` map on `x`-coordinates: it sends `x` to the square class of
`x - T` if `f x ≠ 0`, and to the square class of `f' T` otherwise. -/
noncomputable def μX (x : K) : W.M :=
  if hx : W.f.eval x = 0
    then (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit
    else (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit

@[simp] lemma μX_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.μX x = (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit := by
  simp only [μX, dite_eq_left hx]

@[simp] lemma μX_of_eval_f_ne_zero {x : K} (hx : W.f.eval x ≠ 0) :
    W.μX x = (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit := by
  simp only [μX, dite_eq_right hx]

/-- The descent or `x - T` map `μ₀` on the group of points of an affine Weierstrass curve.
This is a plain map; `WeierstrassCurve.Affine.μ` is the same map as a group homomorphism. -/
noncomputable def μ₀ : W.Point → W.M
  | 0 => 1
  | .some x _ _ => W.μX x

@[simp] lemma μ₀_zero : W.μ₀ 0 = 1 := rfl

@[simp] lemma μ₀_some {x y : K} (h : W.Nonsingular x y) : W.μ₀ (.some x y h) = W.μX x := rfl

end μ₀

/-!
### Step 3: show that `μ` is a homomorphism `Multiplicative W.Point → M`
-/

/-- If `P + Q + R = 0` for three affine points `P`, `Q`, `R` on `W`, then their
`x`-coordinates are the roots of `W.f - ℓ ^ 2` for a polynomial `ℓ` of degree at most `1`
(the line through the three points). -/
lemma Point.exists_eq_f_sub_sq_of_add_add_eq_zero {xP yP xQ yQ xR yR : K}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) :
    ∃ pol, (X - C xP) * (X - C xQ) * (X - C xR) = W.f - pol ^ 2 ∧ pol.natDegree ≤ 1 := by
  refine ⟨linePolynomial xP yP <| W.slope xP xQ yP yQ, ?_, ?_⟩
  · have hgeneric : ¬(xP = xQ ∧ yP = W.negY xQ yQ) := by
      by_contra H
      simp [add_of_Y_eq H.1 H.2] at hPQR
    have := addPolynomial_slope hP.1 hQ.1 hgeneric |>.symm
    rw [neg_eq_iff_eq_neg] at this
    convert this using 1
    · congr
      rw [add_eq_zero_iff_eq_neg, neg_some, add_some hgeneric] at hPQR
      grind
    · simp [addPolynomial, polynomial]
  · simp only [linePolynomial, natDegree_add_C]
    compute_degree

open Point in
private lemma xQ_ne_xP_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h : W.f.eval xP = 0) :
    xQ ≠ xP := by
  contrapose! hPQR
  rw! [hPQR] at hQ ⊢
  rw! [y_eq_zero_of_eval_f_eq_zero hP.1 h, y_eq_zero_of_eval_f_eq_zero hQ.1 h]
  rw [add_self_of_Y_eq <| by simp, zero_add]
  exact some_ne_zero hR

open Point in
/- If two of three collinear points have distinct `2`-torsion `x`-coordinates, then the line
through them is horizontal, and `f` splits off all three `x`-coordinates. -/
private lemma f_eq_prod_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.f = (X - C xP) * (X - C xQ) * (X - C xR) := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eval_f_eq_zero hP hQ hR hPQR h₁
  obtain ⟨pol, hpol, hpol₁⟩ := Point.exists_eq_f_sub_sq_of_add_add_eq_zero hP hQ hR hPQR
  have hpol₀ : pol = 0 := by
    refine pol.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {xP, xQ} (fun x hx ↦ ?_) ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      apply_fun (·.eval x) at hpol
      rcases hx with rfl | rfl <;>
        rw [eval_sub, ‹eval x (f W) = 0›] at hpol <;>
        simpa using hpol
    · grind
  rwa [hpol₀, zero_pow two_ne_zero, sub_zero, eq_comm] at hpol

/- Forward direction of `exists_eq_two_smul_iff`: if `(x, y)` is divisible by `2`, then the
polynomial identity holds, with `ξ` the `x`-coordinate of a halving point. -/
private lemma exists_pol_of_eq_two_smul {x y : K} (h : W.Nonsingular x y) {P : W.Point}
    (hP : Point.some x y h = 2 • P) :
    ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  match P with
  | 0 => simp at hP -- cannot occur
  | .some ξ η h' =>
    rw [← sub_eq_zero, sub_eq_add_neg, two_smul, neg_add, ← add_assoc, add_rotate,
      Point.neg_some] at hP
    have H : W.Nonsingular ξ (W.negY ξ η) := (nonsingular_neg ξ η).mpr h'
    obtain ⟨pol, hpol, hpol₁⟩ := Point.exists_eq_f_sub_sq_of_add_add_eq_zero H H h hP
    rw [← sq] at hpol
    obtain ⟨l, m, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hpol₁
    exact ⟨_, _, _, hpol⟩

variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point

lemma μ₀_mul_eq_one (P : W.Point) : W.μ₀ P * W.μ₀ (-P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => rw [Point.neg_some h, μ₀_some, μ₀_some, M.mul_self]

variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  have hf := f_eq_prod_of_eval_f_eq_zero hP hQ hR hPQR h₁ h₂
  have h₃ : W.f.eval xR = 0 := by rw [hf]; simp
  obtain ⟨hfcP, hfcQ, hfcR⟩ := W.fCofactor_eq_of_f_eq hf
  rw [μX_of_eval_f_eq_zero h₁, μX_of_eval_f_eq_zero h₂, μX_of_eval_f_eq_zero h₃,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  simp only [hfcP, hfcQ, hfcR,
    show ∀ (a b c : K), C a - X + (X - C b) * (X - C c) =
      (X - C b) * (X - C c) - (X - C a) by intro a b c; ring]
  rw [map_sub, map_sub _ _ (X - C xQ), map_sub _ _ (X - C xR)]
  simp only [map_mul]
  rw [← sq_add_add_eq_mul_mul_of_mul_mul_eq_zero <| by rw [← map_mul, ← map_mul, ← hf]; simp]
  exact ⟨_, rfl⟩

/- The case where only `xP` is a `2`-torsion `x`-coordinate. -/
private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne (h : W.f.eval xP = 0)
    (hQ₀ : W.f.eval xQ ≠ 0) (hR₀ : W.f.eval xR ≠ 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rw [μX_of_eval_f_eq_zero h, μX_of_eval_f_ne_zero hQ₀, μX_of_eval_f_ne_zero hR₀,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.exists_eq_f_sub_sq_of_add_add_eq_zero hP hQ hR hPQR
  obtain ⟨γ, rfl⟩ : ∃ γ, pol = C γ * (X - C xP) := by
    apply_fun (·.eval xP) at hpol
    rw [eval_sub, h] at hpol
    exact exists_eq_C_mul_X_sub_C_of_natDegree_le_one hpol₁ (by simpa using hpol)
  rw [W.f_eq_mul_of_eval_eq_zero h, mul_assoc, mul_comm (W.fCofactor _),
    show (C γ * (X - C xP)) ^ 2 = (X - C xP) * (C γ ^ 2 * (X - C xP)) by ring, ← mul_sub] at hpol
  replace hpol := mul_left_cancel₀ (X_sub_C_ne_zero xP) hpol
  simp only [← map_mul]
  rw [show (C xP - X + fCofactor W xP) * (C xQ - X) * (C xR - X) =
    (fCofactor W xP - (X - C xP)) * (X - C xQ) * (X - C xR) by ring, map_mul, map_mul, map_sub]
  rw [← sq_add_mul_eq_mul_mul_of_mul_eq_zero (e := AdjoinRoot.mk W.f (C γ)) ?H₁ ?H₂]
  case H₁ =>
    rw [← map_mul, mul_comm, ← f_eq_mul_of_eval_eq_zero W h]
    simp
  case H₂ => simp only [← map_mul, ← map_pow, ← map_sub, hpol]
  exact ⟨_, rfl⟩

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero (h : W.f.eval xP = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  by_cases hQ₀ : W.f.eval xQ = 0
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hQ hR hPQR h hQ₀
  by_cases hR₀ : W.f.eval xR = 0
  · rw [mul_right_comm]
    rw [add_right_comm] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hR hQ hPQR h hR₀
  exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne hP hQ hR hPQR h hQ₀ hR₀

lemma μX_mul_mul_eq_one : W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rcases eq_or_ne (W.f.eval xP) 0 with HP | HP
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero hP hQ hR hPQR HP
  rcases eq_or_ne (W.f.eval xQ) 0 with HQ | HQ
  · rw [mul_comm (W.μX xP)]
    rw [add_comm (Point.some xP ..)] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hQ hP hR hPQR HQ
  rcases eq_or_ne (W.f.eval xR) 0 with HR | HR
  · rw [mul_comm, ← mul_assoc]
    rw [add_comm, ← add_assoc] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hR hP hQ hPQR HR
  rw [μX_of_eval_f_ne_zero HP, μX_of_eval_f_ne_zero HQ, μX_of_eval_f_ne_zero HR,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.exists_eq_f_sub_sq_of_add_add_eq_zero hP hQ hR hPQR
  simp only [← map_mul, hpol, neg_sub,
    show (C xP - X) * (C xQ - X) * (C xR - X) = -((X - C xP) * (X - C xQ) * (X - C xR))
      by algebra]
  simp

end μ₀_helper_lemmas

lemma μ₀_mul_mul_eq_one_of_add_add_eq_zero {P Q R : W.Point} (hPQR : P + Q + R = 0) :
    μ₀ P * μ₀ Q * μ₀ R = 1 := by
  match P, Q, R with
  | 0, _, _ =>
    rw [zero_add, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, one_mul, hPQR, μ₀_mul_eq_one]
  | .some .., 0, _
  | .some .., .some .., 0 =>
    rw [add_zero, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, mul_one, hPQR, μ₀_mul_eq_one]
  | .some xP yP hP, .some xQ yQ hQ, .some xR yR hR =>
    simp only [μ₀_some]
    exact μX_mul_mul_eq_one hP hQ hR hPQR

/-- The descent map as a group homomorphism. -/
noncomputable def μ : Multiplicative W.Point →* W.M :=
  .ofMapMulMulEqOne (f := μ₀ ∘ Multiplicative.toAdd) (by simp) fun P' Q' R' ↦ by
    simp_rw [← toAdd_eq_zero, toAdd_mul, Function.comp_apply]
    exact μ₀_mul_mul_eq_one_of_add_add_eq_zero

@[simp]
lemma μ_apply (P : W.Point) : μ (.ofAdd P) = μ₀ P := rfl

@[simp]
lemma μ₀_two_nsmul (P : W.Point) : W.μ₀ (2 • P) = 1 := by
  rw [← μ_apply, ofAdd_nsmul, map_pow, M.sq_eq_one]

/-!
### Step 4: show that `μ` has kernel `2 • W(K)`.
-/

/- Reverse direction of `exists_eq_two_smul_iff`, in terms of the coefficient identities of
the polynomial identity: the point `(ξ, lξ + m)` lies on `W` and doubles to `(x, ±y)`. -/
private lemma exists_eq_two_smul_of_identities {x y ξ l m : K} (h : W.Nonsingular x y)
    (H₂ : x + 2 * ξ = l ^ 2 - W.a₂) (H₁ : 2 * x * ξ + ξ ^ 2 = W.a₄ - 2 * l * m)
    (H₀ : x * ξ ^ 2 = -W.a₆ + m ^ 2) :
    ∃ P, Point.some x y h = 2 • P := by
  -- if `lξ + m = 0`, then `ξ` is a root of `f` at which `f' ξ = 2l(lξ + m)` vanishes too
  have hy₀ : l * ξ + m ≠ 0 := fun h0 ↦ W.deriv_f_ne_zero (x := ξ)
    (by rw [eval_f]; linear_combination ξ ^ 2 * H₂ - ξ * H₁ + H₀ + (l * ξ + m) * h0)
    (by linear_combination 2 * ξ * H₂ - H₁ + 2 * l * h0)
  have h2y : 2 * (l * ξ + m) ≠ 0 := mul_ne_zero W.two_ne_zero hy₀
  have hy : l * ξ + m ≠ W.negY ξ (l * ξ + m) :=
    sub_ne_zero.mp <| by rwa [negY_of_isCharNeTwoNF, sub_neg_eq_add, ← two_mul]
  have hsl : W.slope ξ ξ (l * ξ + m) (l * ξ + m) = l := by
    rw [W.slope_self_of_isCharNeTwoNF hy, div_eq_iff h2y]
    linear_combination 2 * ξ * H₂ - H₁
  let P : W.Point := .some ξ (l * ξ + m) <| equation_iff_nonsingular.mp <| by
    rw [equation_iff_eval_f_eq_sq, eval_f]; linear_combination ξ ^ 2 * H₂ - ξ * H₁ + H₀
  suffices .some x y h = 2 • P ∨ .some x y h = 2 • (-P) from this.casesOn (⟨_, ·⟩) (⟨_, ·⟩)
  simp only [smul_neg, P, two_smul, Point.add_self_of_Y_ne hy, ← Point.X_eq_iff, hsl, addX,
    a₁_of_isCharNeTwoNF, zero_mul, add_zero]
  linear_combination H₂

/-- A criterion for a nonsingular point in affine coordinates to be divisible by 2,
in terms of an identity of polynomials. -/
lemma exists_eq_two_smul_iff {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  refine ⟨fun ⟨P, hP⟩ ↦ exists_pol_of_eq_two_smul h hP, fun ⟨ξ, l, m, H⟩ ↦ ?_⟩
  have H' : X ^ 3 - C (x + 2 * ξ) * X ^ 2 + C (2 * x * ξ + ξ ^ 2) * X - C (x * ξ ^ 2) =
      X ^ 3 - C (l ^ 2 - W.a₂) * X ^ 2 + C (W.a₄ - 2 * l * m) * X - C (-W.a₆ + m ^ 2) := by
    simp only [f] at H
    convert H using 1 <;> { simp only [C_eq_algebraMap]; algebra }
  replace H' n := congrArg (fun p ↦ p.coeff n) H'
  simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at H'
  exact exists_eq_two_smul_of_identities h (by simpa using congrArg (-·) (H' 2))
    (by simpa using H' 1) (by simpa using congrArg (-·) (H' 0))

/-- A criterion for a nonsingular point in affine coordinates to be divisible by 2,
in terms of an identity in `W.A`. -/
lemma exists_eq_two_smul_iff' {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, AdjoinRoot.mk W.f ((X - C ξ) ^ 2 * (X - C x)) =
        AdjoinRoot.mk W.f (-(C l * X + C m) ^ 2) := by
  rw [exists_eq_two_smul_iff]
  refine ⟨fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩, fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩⟩
  · rw [H, map_sub, sub_eq_add_neg, map_neg, add_eq_right]
    simp
  · rw [AdjoinRoot.mk_eq_mk, sub_neg_eq_add] at H
    have hmon : ((X - C ξ) ^ 2 * (X - C x) + (C l * X + C m) ^ 2).Monic := by monicity!
    have hf := eq_of_dvd_of_natDegree_le_of_leadingCoeff H
      (by rw [natDegree_f]; compute_degree!) (by rw [W.monic_f.leadingCoeff, hmon.leadingCoeff])
    linear_combination -hf

section kernel

variable {x y : K} (h : W.Nonsingular x y)

include h

private lemma eq_two_smul_of_μ_eq_one_of_ne (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x ≠ 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨r, s, t, rfl⟩ := W.exists_mk_eq z
  have hr : r ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_mul, zero_add] at hz
    exact mk_sq_ne_mk_C_sub_X W.monic_f (by rw [natDegree_f]; norm_num)
      (by have := natDegree_linear_le (a := s) (b := t); rw [natDegree_f]; lia) x hz
  obtain ⟨ξ, l, m, H⟩ := W.exists_X_sub_C_mul_eq r s t hr
  rw [← map_mul] at H
  refine ⟨ξ, l, m, ?_⟩
  apply_fun (fun p ↦ AdjoinRoot.mk W.f (X - C ξ) ^ 2 * p) at hz
  rw [← neg_inj, eq_comm, ← map_pow, ← map_mul, ← map_neg] at hz
  conv_rhs at hz => rw [← map_pow, ← map_mul, ← mul_pow, map_pow, H, ← map_pow, ← map_neg]
  convert hz
  ring

private lemma eq_two_smul_of_μ_eq_one_of_eq (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x = 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_eq_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨r, s, hrs⟩ := W.exists_mk_eq' (AdjoinRoot.mk (W.fCofactor x) p)
  rw [← map_pow, AdjoinRoot.mk_eq_mk] at hz
  have hdvd : W.fCofactor x ∣ W.f := ⟨X - C x, W.f_eq_mul_of_eval_eq_zero hx⟩
  have hz' : AdjoinRoot.mk (W.fCofactor x) (p ^ 2) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X + W.fCofactor x) :=
    AdjoinRoot.mk_eq_mk.mpr <| hdvd.trans hz
  rw [map_pow, hrs, map_add _ _ (fCofactor ..), AdjoinRoot.mk_self, add_zero] at hz'
  have hr₀ : r ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_mul, zero_add] at hz'
    exact mk_sq_ne_mk_C_sub_X (W.monic_fCofactor x) (W.natDegree_fCofactor x).ge
      (by rw [natDegree_fCofactor, natDegree_C]; norm_num) x hz'
  rw [← map_pow, AdjoinRoot.mk_eq_mk] at hz'
  exact ⟨-s / r, 1 / r, -x / r, AdjoinRoot.mk_eq_mk.mpr (W.f_dvd_of_fCofactor_dvd hx hr₀ hz')⟩

lemma eq_two_smul_of_μ_eq_one (hμ : (μ <| .ofAdd <| .some x y h) = 1) :
    ∃ P : W.Point, .some x y h = 2 • P := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · exact eq_two_smul_of_μ_eq_one_of_eq h hμ hx
  · exact eq_two_smul_of_μ_eq_one_of_ne h hμ hx

end kernel

/-- The kernel of `μ` is exactly `2 • W(K)`. -/
lemma ker_μ_eq : (μ (W := W)).ker = (nsmulAddMonoidHom 2).range.toSubgroup := by
  ext P'
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  rw [MonoidHom.mem_ker, μ_apply, Multiplicative.mem_toSubgroup, toAdd_ofAdd,
    AddMonoidHom.mem_range]
  simp only [nsmulAddMonoidHom_apply]
  constructor
  · match P with
    | 0 => exact fun _ ↦ ⟨0, by simp⟩
    | .some x y h => exact fun hμ ↦ (eq_two_smul_of_μ_eq_one h hμ).imp fun Q hQ ↦ hQ.symm
  · rintro ⟨Q, rfl⟩
    exact μ₀_two_nsmul Q

/-- A criterion for the validity of the weak Mordell-Weil Theorem. -/
lemma finite_index_range_nsmulAddMonoidHom_two_iff :
    (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex ↔ Finite (μ (W := W)).range := by
  rw [← AddSubgroup.finiteIndex_toSubgroup_iff, ← ker_μ_eq,
    Equiv.finite_iff (QuotientGroup.quotientKerEquivRange (μ (W := W))).symm.toEquiv]
  exact Subgroup.finiteIndex_iff_finite_quotient

end WeierstrassCurve.Affine

/-!
## Step 6: `im μ ⊆ A(S,2)`

The right level of generality is: `R` a Dedekind domain, `K = Frac R`, and `E/K` given by a
Weierstrass equation with `a₁ = a₃ = 0`. Everything Step 6 needs — a height-one spectrum,
the `v`-adic valuations, and unique factorization of fractional ideals — is exactly the Dedekind
package.
Number fields are *not* needed until Step 7.

`Mathlib.RingTheory.DedekindDomain.SelmerGroup` already defines, for a Dedekind domain `R` with
fraction field `K`, the group `IsDedekindDomain.selmerGroup : Subgroup (Units.modPow K n)`,
namely the classes whose valuation is `≡ 0 mod n` at every `v ∉ S`. Note that its ambient group
is literally our `Units.modPow K n` (that file has it only as a local notation). So the target
`A(S,2)` should be assembled out of `selmerGroup`s, not defined from scratch.

The obstruction is that `A = AdjoinRoot f` is an étale algebra, not a field, so it has no
`HeightOneSpectrum`. The way around this is the decomposition of `A` into a product of fields,
provided by `EllipticCurves.Mathlib.Basic`: as `f` is separable, `AdjoinRoot.equivPiFactors` gives
`A ≃ₐ[K] ((p : W.f.Factors) → AdjoinRoot p)`, a finite product of finite separable field
extensions of `K` indexed by the monic irreducible factors `p` of `f`, and correspondingly
`AdjoinRoot.modPowEquivPiFactors` gives
`W.M = Units.modPow A 2 ≃* ((p : W.f.Factors) → Units.modPow (AdjoinRoot p) 2)`.
Each factor carries `Field`, `Algebra K` and `FiniteDimensional K` instances, and
`Polynomial.Factors.separable` supplies separability.

With that in hand:

* for each factor, `ringOfIntegersFactor R p := integralClosure R (AdjoinRoot p)` is again a
  Dedekind domain (`IsIntegralClosure.isDedekindDomain`, applicable thanks to
  `AdjoinRoot.isSeparable_of_separable`) with fraction field `AdjoinRoot p`, so
  `IsDedekindDomain.selmerGroup` applies to it;
* `A(S,2)` (`WeierstrassCurve.Affine.selmerGroupA`) is the preimage under the above isomorphism of
  the product of the `selmerGroupFactor R p`, the `2`-Selmer groups relative to the primes above
  `S`;
* the containment `im μ ⊆ A(S,2)` is checked factor by factor: for `P = (x, y)` and `w` a prime
  of `ringOfIntegersFactor R p` not above `S`, the valuation `w (x - θ)` is even, where `θ` is
  the root of `p`. If `x` has a pole at `w`, the leading term of the cubic dominates and
  `w (x - θ) = w x = w (y / x) ^ 2`. If `x` is `w`-integral, one uses the factorization
  `y ^ 2 = (x - θ) * (x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄)` over the factor `K[X]/(p)`
  itself: the cofactor
  is congruent to `f' θ` modulo `x - θ`, and `f' θ` is a `w`-unit because `w ∤ Δ`. So either
  `x - θ` is a `w`-unit, or the cofactor is, and then `w (x - θ) = w y ^ 2`.

Step 7 (finiteness of `A(S,2)`) then reduces to finiteness of the `2`-Selmer group of each
factor, which needs the primes above `S` to be finite in number, the class group of
`ringOfIntegersFactor R p` to be finite, and its unit group to be finitely generated — i.e.
number fields. Mathlib lists finiteness of `selmerGroup` as a TODO.

Note that the valuation computation stays inside the single field factor `K[X]/(p)`; no splitting
field is needed. That `f' θ` is a unit at every good prime
(`WeierstrassCurve.Affine.valuation_deriv_root_eq_one`) needs exactly that the coefficients of the
cubic are integral and `disc f` is a unit there — which is what `Δ ∈ badPrimes` buys, via the Bézout
identity behind `WeierstrassCurve.Affine.separable_f`.

In this file: `WeierstrassCurve.Affine.badPrimes` (`S`) and its finiteness,
`AdjoinRoot.isSeparable_of_separable` (so that `IsIntegralClosure.isDedekindDomain` applies to each
factor), `IsDedekindDomain.HeightOneSpectrum.primesAbove` (the `S i`),
`IsDedekindDomain.selmerGroupAbove`, `WeierstrassCurve.Affine.selmerGroupA` (`A(S,2)`, as a subgroup
of `W.M`), and finally `WeierstrassCurve.Affine.range_μ_le_selmerGroupA`.
-/

section Cubic

/- The valuation-theoretic arithmetic of Step 6, for a valuation `v` on a commutative ring and
the monic cubic `t ^ 3 + a * t ^ 2 + b * t + c` with `v`-integral coefficients: integrality of
`f'(t)` and of the cofactors that appear, and the two ways the valuation of `x - θ` turns out to
be even. Integrality of a polynomial expression in integral elements is read off from
`v.integer` being a subring. These are specific to Weierstrass equations, so they live here
rather than in the general-support file; the lemmas of the `RingOfIntegers` and `Core` sections
below instantiate them in the field factors `K[X]/(p)`. -/

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
  {t s a b c : L}

private lemma Valuation.map_cubic_deriv_le_one (ha : v a ≤ 1) (hb : v b ≤ 1) (ht : v t ≤ 1) :
    v (3 * t ^ 2 + 2 * a * t + b) ≤ 1 :=
  let t' : v.integer := ⟨t, ht⟩
  let a' : v.integer := ⟨a, ha⟩
  let b' : v.integer := ⟨b, hb⟩
  (3 * t' ^ 2 + 2 * a' * t' + b').prop

private lemma Valuation.map_cubic_deriv_eq_one (ha : v a ≤ 1) (hb : v b ≤ 1) (hc : v c ≤ 1)
    (ht : v t ≤ 1) {δ : L} (hδ : v δ = 1)
    (hmul : (3 * t ^ 2 + 2 * a * t + b) * ((2 * a ^ 2 - 6 * b) * t ^ 2
      + (2 * a ^ 3 - 7 * a * b + 9 * c) * t + (a ^ 2 * b - 4 * b ^ 2 + 3 * a * c)) = δ) :
    v (3 * t ^ 2 + 2 * a * t + b) = 1 :=
  let t' : v.integer := ⟨t, ht⟩
  let a' : v.integer := ⟨a, ha⟩
  let b' : v.integer := ⟨b, hb⟩
  let c' : v.integer := ⟨c, hc⟩
  v.eq_one_of_mul_eq_one (v.map_cubic_deriv_le_one ha hb ht)
    ((2 * a' ^ 2 - 6 * b') * t' ^ 2 + (2 * a' ^ 3 - 7 * a' * b' + 9 * c') * t'
      + (a' ^ 2 * b' - 4 * b' ^ 2 + 3 * a' * c')).prop (hmul ▸ hδ)

private lemma Valuation.map_cofactor_eq_one (ha : v a ≤ 1) (ht : v t ≤ 1) (hs : v s ≤ 1)
    (hlt : v (s - t) < 1) (hderiv : v (3 * t ^ 2 + 2 * a * t + b) = 1) :
    v (s ^ 2 + t * s + t ^ 2 + a * (s + t) + b) = 1 := by
  have h2t : v (s + 2 * t + a) ≤ 1 :=
    let t' : v.integer := ⟨t, ht⟩
    let a' : v.integer := ⟨a, ha⟩
    let s' : v.integer := ⟨s, hs⟩
    (s' + 2 * t' + a').prop
  have hlt' : v ((s - t) * (s + 2 * t + a)) < v (3 * t ^ 2 + 2 * a * t + b) := by
    rw [hderiv, map_mul]
    exact (mul_le_of_le_one_right' h2t).trans_lt hlt
  rw [show s ^ 2 + t * s + t ^ 2 + a * (s + t) + b
      = (s - t) * (s + 2 * t + a) + (3 * t ^ 2 + 2 * a * t + b) by ring,
    v.map_add_eq_of_lt_right hlt', hderiv]

private lemma Valuation.map_sub_eq_one_or_eq_map_sq (ha : v a ≤ 1) (ht : v t ≤ 1) {x y : L}
    (hx : v x ≤ 1) (hderiv : v (3 * t ^ 2 + 2 * a * t + b) = 1)
    (hfac : (x - t) * (x ^ 2 + t * x + t ^ 2 + a * (x + t) + b) = y ^ 2) :
    v (x - t) = 1 ∨ v (x - t) = v y ^ 2 := by
  by_cases h1 : v (x - t) = 1
  · exact .inl h1
  refine .inr ?_
  have hlt : v (x - t) < 1 := lt_of_le_of_ne ((v.map_sub x t).trans (max_le hx ht)) h1
  rw [← map_pow, ← hfac, map_mul, v.map_cofactor_eq_one ha ht hx hlt hderiv, mul_one]

variable [Nontrivial L]

private lemma cubic_coeff_le_one (ha : v a ≤ 1) (hb : v b ≤ 1) (hc : v c ≤ 1) :
    ∀ i < (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree,
      v ((X ^ 3 + C a * X ^ 2 + C b * X + C c).coeff i) ≤ 1 := by
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  intro i hi
  rw [hdeg] at hi
  interval_cases i <;> simp [ha, hb, hc]

private lemma Valuation.map_cubic_of_one_lt (ha : v a ≤ 1) (hb : v b ≤ 1) (hc : v c ≤ 1)
    (ht : 1 < v t) :
    v (t ^ 3 + a * t ^ 2 + b * t + c) = v t ^ 3 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  have h := v.map_eval_eq_of_one_lt hp (cubic_coeff_le_one v ha hb hc) ht
  rw [hdeg] at h
  simpa using h

private lemma Valuation.le_one_of_root_cubic (ha : v a ≤ 1) (hb : v b ≤ 1) (hc : v c ≤ 1)
    (heq : t ^ 3 + a * t ^ 2 + b * t + c = 0) :
    v t ≤ 1 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  refine v.le_one_of_root_monic hp (cubic_coeff_le_one v ha hb hc) (by rw [hdeg]; norm_num) ?_
  simpa using heq

private lemma Valuation.map_sub_add_cofactor_eq_one [NoZeroDivisors L] (ha : v a ≤ 1) (hb : v b ≤ 1)
    (hc : v c ≤ 1) (hs : s ^ 3 + a * s ^ 2 + b * s + c = 0) (ht : t ^ 3 + a * t ^ 2 + b * t + c = 0)
    (hderiv : v (3 * s ^ 2 + 2 * a * s + b) = 1) :
    v (s - t + (t ^ 2 + (s + a) * t + (s ^ 2 + a * s + b))) = 1 := by
  have hs1 : v s ≤ 1 := v.le_one_of_root_cubic ha hb hc hs
  have ht1 : v t ≤ 1 := v.le_one_of_root_cubic ha hb hc ht
  have hprod : (s - t) * (t ^ 2 + (s + a) * t + (s ^ 2 + a * s + b)) = 0 := by
    linear_combination hs - ht
  rcases mul_eq_zero.mp hprod with h0 | h0
  · -- `s = t`: the element is `f'(s)`
    rw [h0, zero_add,
      show t ^ 2 + (s + a) * t + (s ^ 2 + a * s + b) = 3 * s ^ 2 + 2 * a * s + b by
        linear_combination -(t + 2 * s + a) * h0, hderiv]
  · -- the cofactor vanishes: the element is `s - t`, and `f'(s) = (s - t)(2s + t + a)`
    rw [h0, add_zero]
    have h2t : v (2 * s + t + a) ≤ 1 :=
      let t' : v.integer := ⟨t, ht1⟩
      let a' : v.integer := ⟨a, ha⟩
      let s' : v.integer := ⟨s, hs1⟩
      (2 * s' + t' + a').prop
    refine v.eq_one_of_mul_eq_one ((v.map_sub s t).trans (max_le hs1 ht1)) h2t ?_
    rw [show (s - t) * (2 * s + t + a) = 3 * s ^ 2 + 2 * a * s + b by linear_combination -h0,
      hderiv]

end Cubic

section CubicField

variable {L Γ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ)
  {t a b c : L}

private lemma Valuation.map_sub_eq_map_div_sq (ha : v a ≤ 1) (hb : v b ≤ 1) (hc : v c ≤ 1)
    (ht : v t ≤ 1) {x y : L} (hx : 1 < v x) (heq : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x + c) :
    v (x - t) = v (y / x) ^ 2 := by
  have hx0 : v x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hval : v y ^ 2 = v x ^ 3 := by rw [← map_pow, heq, v.map_cubic_of_one_lt ha hb hc hx]
  rw [v.map_sub_eq_of_lt_left (ht.trans_lt hx), map_div₀, div_pow, hval, pow_succ,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 hx0)]

end CubicField

namespace WeierstrassCurve

variable {K Γ : Type*} [CommRing K] [LinearOrderedCommGroupWithZero Γ]

/-- A Weierstrass curve over `K` is *integral at* a valuation `v` of `K` if all its
coefficients are `v`-integral. -/
structure IsIntegralAt (W : WeierstrassCurve K) (v : Valuation K Γ) : Prop where
  a₁ : v W.a₁ ≤ 1
  a₂ : v W.a₂ ≤ 1
  a₃ : v W.a₃ ≤ 1
  a₄ : v W.a₄ ≤ 1
  a₆ : v W.a₆ ≤ 1

/-- For a curve in the normal form `a₁ = a₃ = 0`, integrality at `v` is integrality of the
three remaining coefficients. -/
lemma isIntegralAt_of_isCharNeTwoNF {W : WeierstrassCurve K} [W.IsCharNeTwoNF] {v : Valuation K Γ}
    (ha₂ : v W.a₂ ≤ 1) (ha₄ : v W.a₄ ≤ 1) (ha₆ : v W.a₆ ≤ 1) : W.IsIntegralAt v :=
  ⟨by simp [a₁_of_isCharNeTwoNF], ha₂, by simp [a₃_of_isCharNeTwoNF], ha₄, ha₆⟩

/-- A curve with coefficients in a Dedekind domain `R` is integral at every `v`-adic valuation
of its fraction field. -/
lemma isIntegralAt_valuation {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K) [IsIntegral R W]
    (v : IsDedekindDomain.HeightOneSpectrum R) : W.IsIntegralAt (v.valuation K) := by
  obtain ⟨W₀, rfl⟩ := IsIntegral.integral (R := R) (W := W)
  exact ⟨v.valuation_le_one _, v.valuation_le_one _, v.valuation_le_one _, v.valuation_le_one _,
    v.valuation_le_one _⟩

end WeierstrassCurve

namespace WeierstrassCurve.Affine

open IsDedekindDomain Polynomial UniqueFactorizationMonoid

-- Step 6 needs neither `DecidableEq K` (except where the `x - T` map `μX` enters at the very
-- end) nor the group structure on points, so we re-declare the variables rather than
-- inheriting the ones used for Steps 2-5.
variable {K : Type*} [Field K] (W : Affine K)

/- Notation local to Step 6: for a monic irreducible factor `p` of `f`, `𝕃 p` is the field
factor `K[X]/(p)` of `W.A`, `ι p : K →+* 𝕃 p` is the canonical embedding, and `θ p` is the
image of the root `T` of `f` in `𝕃 p`. -/
local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])
local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))
local notation:max "θ" p:max => AdjoinRoot.root (p : K[X])

/-- The set of "bad" primes of `R`: those dividing `2` or the discriminant of `W`, and those
occurring in a denominator of `a₂`, `a₄` or `a₆` (the latter three are the supports of the
coefficients in the sense of `IsDedekindDomain.HeightOneSpectrum.Support`). Away from these,
the `x - T` map lands in the `2`-Selmer group. -/
def badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] :
    Set (HeightOneSpectrum R) :=
  {v | v.valuation K 2 ≠ 1} ∪ {v | v.valuation K W.Δ ≠ 1} ∪ HeightOneSpectrum.Support R W.a₂ ∪
    HeightOneSpectrum.Support R W.a₄ ∪ HeightOneSpectrum.Support R W.a₆

/-- There are only finitely many bad primes: `2` and `W.Δ` are nonzero, and the support of any
element of `K` is finite. -/
lemma finite_badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] [W.IsElliptic] [W.IsCharNeTwoNF] : (W.badPrimes R).Finite :=
  ((((HeightOneSpectrum.finite_setOf_valuation_ne_one W.two_ne_zero).union
    (HeightOneSpectrum.finite_setOf_valuation_ne_one W.isUnit_Δ.ne_zero)).union
      (HeightOneSpectrum.Support.finite R W.a₂)).union
        (HeightOneSpectrum.Support.finite R W.a₄)).union
          (HeightOneSpectrum.Support.finite R W.a₆)

section BadPrimes

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}

lemma valuation_a₂_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₂ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inl (.inl (.inr hlt)))

lemma valuation_a₄_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₄ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inl (.inr hlt))

lemma valuation_a₆_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₆ ≤ 1 :=
  not_lt.mp fun hlt ↦ hv (.inr hlt)

lemma isIntegralAt_of_notMem_badPrimes [W.IsCharNeTwoNF] (hv : v ∉ W.badPrimes R) :
    W.IsIntegralAt (v.valuation K) :=
  isIntegralAt_of_isCharNeTwoNF (W.valuation_a₂_le_one_of_notMem_badPrimes R hv)
    (W.valuation_a₄_le_one_of_notMem_badPrimes R hv)
    (W.valuation_a₆_le_one_of_notMem_badPrimes R hv)

lemma valuation_Δ_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.Δ = 1 :=
  not_not.mp fun hne ↦ hv (.inl (.inl (.inl (.inr hne))))

lemma valuation_two_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K 2 = 1 :=
  not_not.mp fun hne ↦ hv (.inl (.inl (.inl (.inl hne))))

/-- Away from the bad primes, `disc f` is a `v`-adic unit: `Δ = 16 · disc f`, and both `Δ`
and `2` are `v`-adic units. -/
lemma valuation_discr_eq_one_of_notMem_badPrimes [W.IsCharNeTwoNF] (hv : v ∉ W.badPrimes R) :
    v.valuation K W.f.discr = 1 := by
  have h16 : v.valuation K 16 = 1 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num, map_pow,
      W.valuation_two_eq_one_of_notMem_badPrimes R hv, one_pow]
  have hΔ := W.valuation_Δ_eq_one_of_notMem_badPrimes R hv
  rwa [W.Δ_eq_discr_f, map_mul, h16, one_mul] at hΔ

end BadPrimes

section DerivativeUnit

/- `f'(x)` is a unit at a rational root `x` of `f` whenever the coefficients are integral and
the valuation of `disc f` is `1` or `exp (-1)`: this is the arithmetic input for the
`2`-torsion `x - T` representative, both at good primes and at primes with
`v(disc f) = exp (-1)`. -/

/-- The discriminant of `f` is a polynomial in the coefficients of `W`, so it is integral
wherever they are. -/
lemma valuation_discr_le_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
    (hW : W.IsIntegralAt v) : v W.f.discr ≤ 1 := by
  have h : W.a₂ ^ 2 * W.a₄ ^ 2 - 4 * W.a₄ ^ 3 - 4 * W.a₂ ^ 3 * W.a₆ - 27 * W.a₆ ^ 2
      + 18 * W.a₂ * W.a₄ * W.a₆ ∈ v.integer :=
    add_mem (sub_mem (sub_mem (sub_mem (mul_mem (pow_mem hW.a₂ 2) (pow_mem hW.a₄ 2))
      (mul_mem (ofNat_mem _ 4) (pow_mem hW.a₄ 3))) (mul_mem (mul_mem (ofNat_mem _ 4)
        (pow_mem hW.a₂ 3)) hW.a₆)) (mul_mem (ofNat_mem _ 27) (pow_mem hW.a₆ 2)))
      (mul_mem (mul_mem (mul_mem (ofNat_mem _ 18) hW.a₂) hW.a₄) hW.a₆)
  rw [W.discr_f]
  exact h

open WithZero in
private lemma eq_one_of_le_one_of_exp_neg_one_le_sq {t : ℤᵐ⁰} (h1 : t ≤ 1)
    (h2 : exp (-1) ≤ t ^ 2) : t = 1 := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at h2
  rw [← exp_log ht0] at h1 h2 ⊢
  rw [← exp_nsmul, two_nsmul] at h2
  rw [← exp_zero] at h1
  rw [exp_eq_one]
  have h1' := exp_le_exp.mp h1
  have h2' := exp_le_exp.mp h2
  lia

open WithZero in
/-- If `x` is a rational root of `f` and the coefficients of the cubic are `v`-integral with
`exp (-1) ≤ v (disc f)`, then `f'(x)` is a `v`-unit: `disc f = (fCofactor x).discr * f'(x)²`
with both factors integral, and the square `v (f'(x))²` cannot equal `exp (-1)`. -/
lemma valuation_deriv_eval_eq_one {v : Valuation K ℤᵐ⁰} {x : K} (hx : W.f.eval x = 0)
    (hW : W.IsIntegralAt v) (hd : exp (-1) ≤ v W.f.discr) :
    v (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1 := by
  have hx1 : v x ≤ 1 := by
    rw [eval_f] at hx
    exact v.le_one_of_root_cubic hW.a₂ hW.a₄ hW.a₆ hx
  have hfx : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∈ v.integer :=
    add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem hx1 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) hW.a₂) hx1)) hW.a₄
  have hcd' : (x + W.a₂) ^ 2 - 4 * (x ^ 2 + W.a₂ * x + W.a₄) ∈ v.integer :=
    sub_mem (pow_mem (add_mem hx1 hW.a₂) 2) (mul_mem (ofNat_mem _ 4)
      (add_mem (add_mem (pow_mem hx1 2) (mul_mem hW.a₂ hx1)) hW.a₄))
  have hcd : v (W.fCofactor x).discr ≤ 1 := by rw [W.discr_fCofactor x]; exact hcd'
  rw [W.discr_f_eq_discr_fCofactor_mul_sq hx, map_mul, map_pow] at hd
  exact eq_one_of_le_one_of_exp_neg_one_le_sq hfx (hd.trans (mul_le_of_le_one_left' hcd))

end DerivativeUnit

section RingOfIntegers

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- The ring of integers of the field factor `K[X]/(p)` over `R`. -/
noncomputable abbrev ringOfIntegersFactor (p : W.f.Factors) : Type _ :=
  integralClosure R (𝕃 p)

/-- The ring of integers of a field factor is a Dedekind domain: it is the integral closure
of `R` in a finite separable extension of the fraction field `K`. -/
instance isDedekindDomain_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsDedekindDomain (W.ringOfIntegersFactor R p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isDedekindDomain R K (𝕃 p) _

/-- A field factor is the fraction field of its ring of integers. -/
instance isFractionRing_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsFractionRing (W.ringOfIntegersFactor R p) (𝕃 p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isFractionRing_of_finite_extension R K (𝕃 p) _

/-- The ring of integers of a field factor is torsion-free over `R`, as `R` embeds into it. -/
instance instIsTorsionFreeRingOfIntegersFactor (p : W.f.Factors) :
    Module.IsTorsionFree R (W.ringOfIntegersFactor R p) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap R (𝕃 p)) := by
    rw [IsScalarTower.algebraMap_eq R K (𝕃 p)]
    exact (ι p).injective.comp (IsFractionRing.injective R K)
  exact fun a b hab ↦ hinj (congrArg Subtype.val hab)

/-- The `w`-adic valuation of an element of `K` is the `v`-adic valuation of the prime `v`
below `w`, raised to the ramification index. -/
lemma valuation_algebraMap_eq [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) (z : K) :
    (w.below R).valuation K z ^ ((w.below R).asIdeal.ramificationIdx' w.asIdeal) =
      w.valuation (𝕃 p) (ι p z) :=
  HeightOneSpectrum.valuation_liesOver _ _ _ z

/-- If `z` is integral at the prime below `w`, then it is integral at `w`. -/
lemma valuation_algebraMap_le_one [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) {z : K}
    (hz : (w.below R).valuation K z ≤ 1) :
    w.valuation (𝕃 p) (ι p z) ≤ 1 := by
  rw [← W.valuation_algebraMap_eq R p w z]
  simpa using pow_le_pow_left' hz _

/-- A prime `w` of the ring of integers of a field factor that does not lie above `S` lies
over a prime of `R` outside `S`. -/
lemma below_notMem_of_notMem_primesAbove [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    {S : Set (HeightOneSpectrum R)} {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S) : w.below R ∉ S :=
  fun hv ↦ hw ((HeightOneSpectrum.mem_primesAbove_iff R _ _ w).mpr hv)

/-- `θ` satisfies the Weierstrass cubic in the field factor `K[X]/(p)`. -/
lemma root_cubic_eq_zero (p : W.f.Factors) :
    θ p ^ 3 + ι p W.a₂ * θ p ^ 2 + ι p W.a₄ * θ p + ι p W.a₆ = 0 := by
  have hz : AdjoinRoot.mk (p : K[X]) W.f = 0 :=
    AdjoinRoot.mk_eq_zero.mpr p.dvd
  simpa [f, AdjoinRoot.algebraMap_eq] using hz

/-- The Bézout identity `WeierstrassCurve.Affine.aeval_f_mul_add_aeval_derivative_f_mul_eq_discr`
evaluated at `θ`, where `f` vanishes: `f′(θ)` times an explicit quadratic in `θ` with integral
coefficients equals `disc f`. (The classical identity with `Δ` on the right is `16` times this
one; this version stays useful at even places.) -/
lemma deriv_root_mul_eq_discr_f (p : W.f.Factors) :
    (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄)
        * ((2 * ι p W.a₂ ^ 2 - 6 * ι p W.a₄) * θ p ^ 2
          + (2 * ι p W.a₂ ^ 3 - 7 * ι p W.a₂ * ι p W.a₄ + 9 * ι p W.a₆) * θ p
          + (ι p W.a₂ ^ 2 * ι p W.a₄ - 4 * ι p W.a₄ ^ 2 + 3 * ι p W.a₂ * ι p W.a₆)) =
      ι p W.f.discr := by
  have h := W.aeval_f_mul_add_aeval_derivative_f_mul_eq_discr (θ p)
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero.mpr p.dvd, zero_mul,
    zero_add, derivative_f] at h
  simpa only [map_add, map_mul, map_pow, map_ofNat, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
    AdjoinRoot.algebraMap_eq] using h

/-- The cofactor `f / (X - x)`, computed in the field factor `K[X]/(p)`. -/
lemma mk_fCofactor_eq (p : W.f.Factors) (x : K) :
    AdjoinRoot.mk (p : K[X]) (W.fCofactor x) =
      θ p ^ 2 + (ι p x + ι p W.a₂) * θ p + (ι p x ^ 2 + ι p W.a₂ * ι p x + ι p W.a₄) := by
  simp only [fCofactor, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    ← AdjoinRoot.algebraMap_eq]

variable [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
  {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
  (hW : W.IsIntegralAt ((w.below R).valuation K)) (hd : (w.below R).valuation K W.f.discr = 1)
  -- (this is `w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1`;
  -- `variable` commands cannot use the local notation)
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include hW in
/-- If the coefficients of the cubic are integral at the prime below `w`, then the root `θ` is
`w`-integral: it satisfies the monic cubic `f`, whose coefficients are integral at `w`. -/
lemma valuation_root_le_one : w.valuation (𝕃 p) (θ p) ≤ 1 :=
  Valuation.le_one_of_root_cubic _
    (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_algebraMap_le_one R p w hW.a₄)
    (W.valuation_algebraMap_le_one R p w hW.a₆)
    (W.root_cubic_eq_zero p)

/-- An element of `K` with trivial valuation at the prime below `w` has trivial valuation
at `w`. -/
lemma valuation_algebraMap_eq_one {z : K} (hz : (w.below R).valuation K z = 1) :
    w.valuation (𝕃 p) (ι p z) = 1 := by
  rw [← W.valuation_algebraMap_eq R p w z, hz, one_pow]

include hW in
/-- If the coefficients of the cubic are integral at the prime below `w`, then `f' θ` is
`w`-integral. -/
lemma valuation_deriv_root_le_one :
    w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) ≤ 1 :=
  Valuation.map_cubic_deriv_le_one _ (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_algebraMap_le_one R p w hW.a₄) (W.valuation_root_le_one R p hW)

include hW hd in
/-- If the coefficients of the cubic are integral and `disc f` is a unit at the prime below
`w`, then `f' θ = 3 θ ^ 2 + 2 a₂ θ + a₄` is a `w`-unit.

Evaluating the Bézout identity behind `WeierstrassCurve.Affine.separable_f` at `θ` gives
`f'(θ) * c(θ) = disc f` (`WeierstrassCurve.Affine.deriv_root_mul_eq_discr_f`) for an explicit
quadratic `c` with `w`-integral coefficients. Both factors are integral at `w` and the product is a
unit, so both are units. -/
lemma valuation_deriv_root_eq_one :
    w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1 :=
  Valuation.map_cubic_deriv_eq_one _ (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_algebraMap_le_one R p w hW.a₄) (W.valuation_algebraMap_le_one R p w hW.a₆)
    (W.valuation_root_le_one R p hW) (W.valuation_algebraMap_eq_one R p hd)
    (W.deriv_root_mul_eq_discr_f p)

include hW hderiv in
/-- If the coefficients of the cubic are integral at the prime below `w` and `f' θ` is a
`w`-unit, and if `x` is `w`-integral and `x - θ` is not a `w`-unit, then the cofactor
`x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄` is a `w`-unit: modulo `x - θ` it equals `f' θ`. -/
lemma valuation_cofactor_eq_one {x : K}
    (hx : w.valuation (𝕃 p) (ι p x) ≤ 1)
    (hlt : w.valuation (𝕃 p) (ι p x - θ p) < 1) :
    w.valuation (𝕃 p) (ι p x ^ 2 + θ p * ι p x + θ p ^ 2
      + ι p W.a₂ * (ι p x + θ p) + ι p W.a₄) = 1 :=
  Valuation.map_cofactor_eq_one _ (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_root_le_one R p hW) hx hlt hderiv

include hW in
/-- If `x` is a root of `f`, then at a prime `w` at which (i.e. at the prime of `R` below
which) the coefficients of the cubic are integral and `f'(x)` is a unit, the `p`-component of
the `x - T` representative is a unit.

Both `x` and `θ` are roots of `f`, so `x - θ` times the cofactor is `0` and, `L` being a field,
one of the two factors vanishes. If `x = θ` the component is `f'(x)`; if the cofactor vanishes
the component is `x - θ` and `f'(x) = (x - θ)(2x + θ + a₂)`. Either way `hdx` makes it a unit.

At a good prime, `hdx` is supplied by `WeierstrassCurve.Affine.valuation_deriv_eval_eq_one`; at an
odd prime with `v(disc f) = exp (-1)` the same lemma applies, so the `2`-torsion representative is
unramified there as well. -/
lemma valuation_projFactor_torsion_eq_one {x : K} (hx : W.f.eval x = 0)
    (hdx : (w.below R).valuation K (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) = 1) :
    w.valuation (𝕃 p) (ι p x - θ p + AdjoinRoot.mk (p : K[X]) (W.fCofactor x)) = 1 := by
  rw [W.mk_fCofactor_eq p x]
  refine Valuation.map_sub_add_cofactor_eq_one _ (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_algebraMap_le_one R p w hW.a₄) (W.valuation_algebraMap_le_one R p w hW.a₆)
    (by rw [← W.map_eval_f, hx, map_zero]) (W.root_cubic_eq_zero p) ?_
  simpa only [map_add, map_mul, map_pow, map_ofNat] using
    W.valuation_algebraMap_eq_one R p (w := w) hdx

end RingOfIntegers

section Core

variable [W.IsElliptic] [W.IsCharNeTwoNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (p : W.f.Factors)
  {x y : K} (h : W.Equation x y) (hx : W.f.eval x ≠ 0)
  (u : (AdjoinRoot (p : K[X]))ˣ)
  (hu : (u : AdjoinRoot (p : K[X])) =
    algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]))
  (w : HeightOneSpectrum (W.ringOfIntegersFactor R p))
  (hW : W.IsIntegralAt ((w.below R).valuation K))
  -- (this is `w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1`;
  -- `variable` commands cannot use the local notation)
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include h hx hu hW

/-- Non-integral case: `x` has a pole at the prime of `R` below `w`.

The coefficients `a₂`, `a₄`, `a₆` and the root `θ` are `w`-integral, so `1 < w x` makes the
leading term of the cubic dominate: `w (f x) = w x ^ 3`, hence `w y ^ 2 = w x ^ 3`. Also
`w θ ≤ 1 < w x`
gives `w (x - θ) = w x`. Therefore `w (x - θ) = w (y / x) ^ 2` is an even power. -/
lemma even_valuationOfNeZero_sub_root_of_one_lt
    (hx' : 1 < w.valuation (𝕃 p) (ι p x)) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  have hx0 : ι p x ≠ 0 := (w.valuation (𝕃 p)).ne_zero_iff.mp (zero_lt_one.trans hx').ne'
  have hy0 : ι p y ≠ 0 := (_root_.map_ne_zero _).mpr (W.ne_zero_of_eval_f_ne_zero h hx)
  have heq : ι p y ^ 2 = ι p x ^ 3 + ι p W.a₂ * ι p x ^ 2 + ι p W.a₄ * ι p x + ι p W.a₆ := by
    rw [← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hkey : w.valuation (𝕃 p) u = w.valuation (𝕃 p) (Units.mk0 _ (div_ne_zero hy0 hx0)) ^ 2 := by
    rw [hu, Units.val_mk0]
    exact Valuation.map_sub_eq_map_div_sq _ (W.valuation_algebraMap_le_one R p w hW.a₂)
      (W.valuation_algebraMap_le_one R p w hW.a₄) (W.valuation_algebraMap_le_one R p w hW.a₆)
      (W.valuation_root_le_one R p hW) hx' heq
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

include hderiv in
/-- Integral case: `x` is integral at the prime of `R` below `w`.

Over `L` the Weierstrass equation factors as `y ^ 2 = (x - θ) * c` with cofactor
`c = x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄`. If `x - θ` is a `w`-unit there is nothing to do.
Otherwise `w (x - θ) < 1`, and since `c = (x - θ) * (x + 2 θ + a₂) + f' θ` with `f' θ` a
`w`-unit, the cofactor is a `w`-unit. Hence `w (x - θ) = w y ^ 2` is an even power. -/
lemma even_valuationOfNeZero_sub_root_of_le_one
    (hx' : w.valuation (𝕃 p) (ι p x) ≤ 1) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  have hy0 : ι p y ≠ 0 := (_root_.map_ne_zero _).mpr (W.ne_zero_of_eval_f_ne_zero h hx)
  have heq : ι p y ^ 2 = ι p x ^ 3 + ι p W.a₂ * ι p x ^ 2 + ι p W.a₄ * ι p x + ι p W.a₆ := by
    rw [← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hfac : (ι p x - θ p) * (ι p x ^ 2 + θ p * ι p x + θ p ^ 2 + ι p W.a₂ * (ι p x + θ p)
      + ι p W.a₄) = ι p y ^ 2 := by
    linear_combination -W.root_cubic_eq_zero p - heq
  rcases Valuation.map_sub_eq_one_or_eq_map_sq _ (W.valuation_algebraMap_le_one R p w hW.a₂)
    (W.valuation_root_le_one R p hW) hx' hderiv hfac with h1 | h1
  · simpa using w.dvd_toAdd_valuationOfNeZero (n := 2) (z := 1)
      (by rw [Units.val_one, map_one, one_pow, hu, h1])
  · simpa using w.dvd_toAdd_valuationOfNeZero (n := 2) (z := Units.mk0 _ hy0)
      (by simpa [hu] using h1)

include hderiv in
/-- The arithmetic core of Step 6, generic case, with all the group theory stripped away:
for `(x, y)` on `W` with `f x ≠ 0`, and `w` a prime of the ring of integers of the field factor
`K[X]/(p)` such that the coefficients of the cubic are integral at the prime of `R` below `w`
and `f' θ` is a `w`-unit, the `w`-adic valuation of `x - θ` is even.

The proof splits on whether `x` has a pole at the prime of `R` below `w`. -/
lemma even_valuationOfNeZero_sub_root :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  by_cases hx' : 1 < w.valuation (𝕃 p) (ι p x)
  · exact W.even_valuationOfNeZero_sub_root_of_one_lt R p h hx u hu w hW hx'
  · exact W.even_valuationOfNeZero_sub_root_of_le_one R p h hx u hu w hW hderiv
      (not_lt.mp hx')

end Core

section Selmer

/-- If `x` is a root of `f`, then every irreducible factor of `f` other than `X - x` divides
the cofactor `f / (X - x)`. -/
lemma dvd_fCofactor_of_ne {x : K} (hx : W.f.eval x = 0) (p : W.f.Factors)
    (hp : (p : K[X]) ≠ X - C x) : (p : K[X]) ∣ W.fCofactor x := by
  have hdvd : (p : K[X]) ∣ W.fCofactor x * (X - C x) := by
    rw [← W.f_eq_mul_of_eval_eq_zero hx]
    exact p.dvd
  refine (p.prime.2.2 _ _ hdvd).resolve_right fun h ↦ hp ?_
  exact eq_of_monic_of_associated p.monic (monic_X_sub_C x)
    (p.irreducible.associated_of_dvd (irreducible_X_sub_C x) h)

/-- Consequently the cofactor dies in every field factor except the one coming from `X - x`. -/
lemma mk_fCofactor_eq_zero {x : K} (hx : W.f.eval x = 0) (p : W.f.Factors)
    (hp : (p : K[X]) ≠ X - C x) : AdjoinRoot.mk (p : K[X]) (W.fCofactor x) = 0 :=
  AdjoinRoot.mk_eq_zero.mpr (W.dvd_fCofactor_of_ne hx p hp)

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/-- The image of the generic `x - T` representative in the field factor `K[X]/(p)` is `x - θ`. -/
lemma projFactor_mk_C_sub_X (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p (AdjoinRoot.mk W.f (C x - X)) =
      ι p x - θ p := by
  rw [AdjoinRoot.projFactor_mk, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

/-- The image of the `2`-torsion `x - T` representative in the field factor `K[X]/(p)`. -/
lemma projFactor_mk_C_sub_X_add_fCofactor (x : K) (p : W.f.Factors) :
    AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p
        (AdjoinRoot.mk W.f (C x - X + W.fCofactor x)) =
      ι p x - θ p + AdjoinRoot.mk (p : K[X]) (W.fCofactor x) := by
  rw [AdjoinRoot.projFactor_mk, map_add, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq]

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R))

/-- The `2`-Selmer group of the field factor `AdjoinRoot p` of `W.A`, relative to the primes of
its ring of integers lying above the primes in `S`. -/
noncomputable def selmerGroupFactor (p : W.f.Factors) :
    Subgroup (Units.modPow (𝕃 p) 2) :=
  IsDedekindDomain.selmerGroupAbove R (W.ringOfIntegersFactor R p) (𝕃 p) S 2

/-- `A(S,2)` in the product decomposition: the product of the `2`-Selmer groups of the field
factors of `W.A`. -/
noncomputable def selmerGroupPi :
    Subgroup ((p : W.f.Factors) → Units.modPow (𝕃 p) 2) :=
  Subgroup.pi Set.univ (W.selmerGroupFactor R S)

/-- `A(S,2)`, as a subgroup of `W.M`: the classes whose image in each field factor lies in the
`2`-Selmer group of that factor. Step 6 asserts that `im μ ≤ A(S,2)` for `S` the bad primes. -/
noncomputable def selmerGroupA : Subgroup W.M :=
  (W.selmerGroupPi R S).comap
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2).toMonoidHom

lemma mem_selmerGroupA_iff (m : W.M) :
    m ∈ W.selmerGroupA R S ↔ ∀ p : W.f.Factors,
      AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 m p ∈
        W.selmerGroupFactor R S p := by
  simp [selmerGroupA, selmerGroupPi, Subgroup.mem_pi]

/-!
#### The arithmetic input

Write `θ` for `AdjoinRoot.root p`, the image of the root `T` in the field factor `K[X]/(p)`,
and `𝓞` for the integral closure of `R` in `K[X]/(p)`, a Dedekind domain by
`WeierstrassCurve.Affine.isDedekindDomain_ringOfIntegersFactor` (an instance).

The `p`-component of `μX x` is the square class of the reduction mod `p` of the `x - T`
representative, computed by `WeierstrassCurve.Affine.projFactor_mk_C_sub_X` and
`WeierstrassCurve.Affine.projFactor_mk_C_sub_X_add_fCofactor`: it is `x - θ` in the generic case and
`x - θ + fCofactor x` when `x` is a root of `f`.

What has to be shown is that this class lies in the `2`-Selmer group of `K[X]/(p)`, i.e. that
`w (x - θ)` is even for every prime `w` of `𝓞` not lying above a prime of `S`; away from `S`,
the coefficients of the cubic are integral and `disc f` is a unit, by hypothesis.
The two cases are split off as `WeierstrassCurve.Affine.mem_selmerGroupFactor_of_eval_f_ne_zero` and
`WeierstrassCurve.Affine.mem_selmerGroupFactor_of_eval_f_eq_zero`.
-/

/-- Membership of the class of a unit in the `2`-Selmer group of a field factor: its valuation
is even at every prime of the ring of integers not lying above `S`. -/
lemma mem_selmerGroupFactor_unit_iff (p : W.f.Factors) (u : (𝕃 p)ˣ) :
    (QuotientGroup.mk u : Units.modPow (𝕃 p) 2) ∈ W.selmerGroupFactor R S p ↔
      ∀ w : HeightOneSpectrum (W.ringOfIntegersFactor R p),
        w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S →
          (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) :=
  forall₂_congr fun w _ ↦ HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff w 2 u

/-- Membership of the class of a unit of the étale algebra in `A(S,2)`, componentwise: the
valuation of each `projFactor`-component is even at every prime of the corresponding ring of
integers that does not lie above `S`. -/
lemma mem_selmerGroupA_unit_iff (a : W.Aˣ) :
    (QuotientGroup.mk a : W.M) ∈ W.selmerGroupA R S ↔
      ∀ (p : W.f.Factors) (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)),
        w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S →
          (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero
            (Units.map (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p).toMonoidHom a)) := by
  rw [mem_selmerGroupA_iff]
  refine forall_congr' fun p ↦ ?_
  rw [AdjoinRoot.modPowEquivPiFactors_mk, mem_selmerGroupFactor_unit_iff]

variable (hS : ∀ v ∉ S, W.IsIntegralAt (v.valuation K)) (hSd : ∀ v ∉ S, v.valuation K W.f.discr = 1)

include hS hSd in
/-- Generic case of the arithmetic input: `f x ≠ 0`, so the `p`-component of `μX x` is the class
of `x - θ`. -/
lemma mem_selmerGroupFactor_of_eval_f_ne_zero {x y : K} (h : W.Equation x y)
    (hx : W.f.eval x ≠ 0) (p : W.f.Factors) :
    (((isUnit_mk_sub_X_of_eval_f_ne_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        Units.modPow (𝕃 p) 2) ∈ W.selmerGroupFactor R S p := by
  rw [W.mem_selmerGroupFactor_unit_iff R S p]
  intro w hw
  have hv := W.below_notMem_of_notMem_primesAbove R p hw
  refine W.even_valuationOfNeZero_sub_root R p h hx _ ?_ w (hS _ hv)
    (W.valuation_deriv_root_eq_one R p (hS _ hv) (hSd _ hv))
  exact W.projFactor_mk_C_sub_X x p

include hS hSd in
/-- `2`-torsion case of the arithmetic input: `f x = 0`.

By `WeierstrassCurve.Affine.projFactor_mk_C_sub_X_add_fCofactor` the `p`-component of `μX x` is
`x - θ + fCofactor x`, which by `WeierstrassCurve.Affine.valuation_projFactor_torsion_eq_one` is a
unit at every prime `w` not lying above `S`. Its valuation is therefore `0`, in particular even. -/
lemma mem_selmerGroupFactor_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0)
    (p : W.f.Factors) :
    (((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
      (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit :
        Units.modPow (𝕃 p) 2) ∈ W.selmerGroupFactor R S p := by
  rw [W.mem_selmerGroupFactor_unit_iff R S p]
  intro w hw
  have hv := W.below_notMem_of_notMem_primesAbove R p hw
  set u := ((isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).map
    (AdjoinRoot.projFactor W.f_ne_zero W.squarefree_f p)).unit with hudef
  have hd1 : WithZero.exp (-1 : ℤ) ≤ (w.below R).valuation K W.f.discr := by
    rw [hSd _ hv]
    exact (WithZero.exp_le_exp.mpr (by lia)).trans_eq WithZero.exp_zero
  have hval : w.valuation (𝕃 p) (u : 𝕃 p) = 1 := by
    rw [hudef, IsUnit.unit_spec, W.projFactor_mk_C_sub_X_add_fCofactor x p]
    exact W.valuation_projFactor_torsion_eq_one R p (hS _ hv) hx
      (W.valuation_deriv_eval_eq_one hx (hS _ hv) hd1)
  simpa using w.dvd_toAdd_valuationOfNeZero (n := 2) (z := 1) (by simp [hval])

section

variable [DecidableEq K]

include hS hSd in
/-- The heart of Step 6: for a point `(x, y)` of `W` and a field factor `K[X]/(p)` of `W.A`,
the square class of the image of the `x - T` map lies in the `2`-Selmer group of that factor. -/
lemma μX_component_mem_selmerGroupFactor {x y : K} (h : W.Equation x y) (p : W.f.Factors) :
    AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2 (W.μX x) p ∈
      W.selmerGroupFactor R S p := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · rw [μX_of_eval_f_eq_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_eq_zero R S hS hSd hx p
  · rw [μX_of_eval_f_ne_zero hx, AdjoinRoot.modPowEquivPiFactors_unit]
    exact W.mem_selmerGroupFactor_of_eval_f_ne_zero R S hS hSd h hx p

include hS hSd in
/-- **Step 6**: the image of `μ` is contained in `A(S,2)`, whenever the coefficients of the
cubic are integral and `disc f` is a unit away from `S`. -/
theorem range_μ_le_selmerGroupA : (μ (W := W)).range ≤ W.selmerGroupA R S := by
  rintro _ ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P
  rw [μ_apply]
  match P with
  | 0 => rw [μ₀_zero]; exact one_mem _
  | .some x y h =>
    rw [μ₀_some, mem_selmerGroupA_iff]
    exact fun p ↦ W.μX_component_mem_selmerGroupFactor R S hS hSd h.1 p

end

/-!
### Step 7: `A(S,2)` is finite, hence `E(K)/2E(K)` is finite

The finiteness of the `2`-Selmer group of each field factor is
`IsDedekindDomain.finite_selmerGroup` from `EllipticCurves.Mathlib.SelmerGroup`. It requires the
class group
of the factor's ring of integers to be finite and its unit group to be finitely generated;
these are taken as hypotheses here (for `K` a number field they are the class number theorem
and Dirichlet's unit theorem). The relevant set of primes, those above `S`, is finite by
`IsDedekindDomain.HeightOneSpectrum.primesAbove_finite` whenever `S` is. -/

section Step7

variable [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor R p))]
  [(p : W.f.Factors) → Group.FG (W.ringOfIntegersFactor R p)ˣ]

/-- The `2`-Selmer group of each field factor of `W.A` is finite, for a finite set `S`. -/
theorem finite_selmerGroupFactor (hS : S.Finite) (p : W.f.Factors) :
    Finite (W.selmerGroupFactor R S p) :=
  finite_selmerGroup (W.ringOfIntegersFactor R p) (𝕃 p)
    (HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) S) 2
    (HeightOneSpectrum.primesAbove_finite R (W.ringOfIntegersFactor R p) hS)

/-- **Step 7**: `A(S,2)` is finite, for a finite set `S`. -/
theorem finite_selmerGroupA (hS : S.Finite) : Finite (W.selmerGroupA R S) := by
  have := Polynomial.Factors.finite W.f_ne_zero
  have (p : W.f.Factors) : Finite (W.selmerGroupFactor R S p) :=
    W.finite_selmerGroupFactor R S hS p
  have : Finite (W.selmerGroupPi R S) := Subgroup.instFinitePi
  exact Subgroup.finite_comap_of_injective
    (AdjoinRoot.modPowEquivPiFactors W.f_ne_zero W.squarefree_f 2).injective (W.selmerGroupPi R S)

variable [DecidableEq K]

include R in
/-- **The Weak Mordell-Weil Theorem**: `E(K)/2E(K)` is finite, for an elliptic curve `E` in
the normal form `y² = x³ + a₂x² + a₄x + a₆` over the fraction field `K` of a Dedekind domain
`R` such that for each irreducible factor `p` of the cubic, the ring of integers of
`K[X]/(p)` has finite class group and finitely generated unit group.

This is the input to the descent argument (`AddCommGroup.fg_of_descent'`) in the proof of the
Mordell-Weil theorem, `WeierstrassCurve.Affine.fg_point` in `EllipticCurves.MordellWeil`. -/
theorem finite_index_range_nsmulAddMonoidHom_two :
    (nsmulAddMonoidHom (α := W.Point) 2).range.FiniteIndex := by
  rw [finite_index_range_nsmulAddMonoidHom_two_iff]
  have := W.finite_selmerGroupA R (W.badPrimes R) (W.finite_badPrimes R)
  exact ((W.selmerGroupA R (W.badPrimes R) : Set W.M).toFinite.subset
    (W.range_μ_le_selmerGroupA R (W.badPrimes R)
      (fun _ hv ↦ W.isIntegralAt_of_notMem_badPrimes R hv)
      (fun _ hv ↦ W.valuation_discr_eq_one_of_notMem_badPrimes R hv))).to_subtype

end Step7

end Selmer

end WeierstrassCurve.Affine

end
