module

public import Mathlib

@[expose] public section

/-!
# The canonical height attached to a height function on an abelian group

Let `G` be an additive abelian group and `h : G → ℝ` a "height function" on it. If `h` satisfies
the *approximate parallelogram law*
`∃ C, ∀ x y, |h (x + y) + h (x - y) - 2 * (h x + h y)| ≤ C`,
then *Tate's limit*
`ĥ x = lim_{n → ∞} h (2 ^ n • x) / 4 ^ n`
exists, stays within a bounded distance of `h`, and satisfies the parallelogram law *exactly*.
It is therefore a quadratic function on `G`, and it vanishes exactly on the torsion subgroup.

The motivating example is the Mordell-Weil group `E(K)` of an elliptic curve with `h` the naïve
height; there `ĥ` is the *canonical*, or *Néron-Tate*, height. Nothing in this file mentions
elliptic curves: it is pure real analysis on an abelian group, in the same spirit as
`Mathlib.GroupTheory.Descent`, which abstracts the descent step of the Mordell-Weil theorem in
the same way.

## Main definitions

* `AddCommGroup.IsQuadratic p`: the function `p : G → ℝ` satisfies the parallelogram law
  `p (x + y) + p (x - y) = 2 * p x + 2 * p y` exactly. Such a `p` kills `0`, is even, and scales
  by `n ^ 2` under `n • ·`.
* `AddCommGroup.canonicalHeightSeq h x n = h (2 ^ n • x) / 4 ^ n`: the sequence whose limit
  defines the canonical height.
* `AddCommGroup.canonicalHeight h x`: Tate's limit. This is a `limUnder`, so it takes a junk
  value when the defining sequence does not converge; every result about the limit below
  therefore carries a hypothesis forcing convergence.

## Main results

Throughout, `C : ℝ` is a constant. Two hypotheses appear, and the results are deliberately split
according to which one they need:

* the *doubling bound* `hdbl : ∀ x, |h (2 • x) - 4 * h x| ≤ C` suffices for everything about
  convergence: `AddCommGroup.cauchySeq_canonicalHeightSeq`,
  `AddCommGroup.tendsto_canonicalHeightSeq`, `AddCommGroup.abs_canonicalHeight_sub_le`
  (which gives `|ĥ - h| ≤ C / 3`), `AddCommGroup.canonicalHeight_two_nsmul`,
  `AddCommGroup.canonicalHeight_nonneg` and `AddCommGroup.northcott_canonicalHeight`;
* the *approximate parallelogram law*
  `hpar : ∀ x y, |h (x + y) + h (x - y) - 2 * (h x + h y)| ≤ C` is needed only for the results
  that make `ĥ` quadratic: `AddCommGroup.isQuadratic_canonicalHeight` (the *exact*
  parallelogram law), `AddCommGroup.canonicalHeight_neg`,
  `AddCommGroup.canonicalHeight_nsmul`, `AddCommGroup.canonicalHeight_zsmul`,
  `AddCommGroup.canonicalHeight_eq_zero_iff` and
  `AddCommGroup.eq_canonicalHeight_of_abs_sub_le_of_map_zsmul`.

The bridge between the two is `AddCommGroup.abs_two_nsmul_sub_four_mul_le`: taking
`y := x` in `hpar` yields the doubling bound with constant `C + |h 0|`.

## Implementation notes

The development is phrased for `AddCommGroup` only, with no multiplicative counterpart.
Mathlib's convention is to state results multiplicatively and generate additive versions with
`to_additive`. We deviate deliberately: the hypothesis here is a *quadratic* parallelogram law,
and the height functions that satisfy one live on additive groups. Heights on multiplicative
groups are *linear* — the Weil height on `Kˣ` satisfies `h (x ^ n) = |n| * h x`, which already
fails the law at `y := x` — so a multiplicative twin would be `to_additive`-generated
boilerplate with no naturally occurring instance.

The construction is unbundled: `canonicalHeight h` is defined before any hypothesis on `h` is
available, and the hypotheses are then passed explicitly to the lemmas that need them, as in
`Mathlib.GroupTheory.Descent`. In particular `IsQuadratic` is a plain predicate rather than
a bundled structure with a `FunLike` instance. The bundled counterpart of `IsQuadratic` is
`QuadraticMap ℤ G ℝ` (buildable via `QuadraticMap.ofPolar`); we stay unbundled because the
height itself is unbundled and the polar form is not needed here.

Two normal forms for the law coexist on purpose: `IsQuadratic` uses `2 * p x + 2 * p y`,
matching #25986's `ParMap`, while the approximate-law hypothesis `hpar` uses `2 * (h x + h y)`,
matching `Mathlib/GroupTheory/Descent.lean` and this repository's `approx_parallelogram_law`, so
that the curve-level transport is a direct `exact`.

## Acknowledgements

The design and several proofs are adapted, with thanks, from David Kurniadi Angdinata's draft
mathlib pull request
[#25986](https://github.com/leanprover-community/mathlib4/pull/25986),
*"feat(AlgebraicGeometry/EllipticCurve/NumberField/Height): define heights on Weierstrass
curves"*. Specifically: the statements and induction skeleton of the `IsQuadratic` lemmas
below correspond to that PR's bundled `ParMap.zero`, `ParMap.neg` and `ParMap.smul`; the
`C * 4⁻¹ ^ n`-shaped bound on consecutive differences that lets `cauchySeq_of_le_geometric`
apply directly is taken from its `canonHeightSeq_sub_succ`; the forward direction of
`canonicalHeight_eq_zero_iff` follows its `canonHeight_eq_zero` closely, by the same
`← finite_multiples` and `isOfFinAddOrder_iff_zsmul_eq_zero` route into a Northcott-finite set;
and `eq_canonicalHeight_of_abs_sub_le_of_map_zsmul` follows its
`canonHeight_unique`. That PR builds the same construction on a different foundation
(`NumberField.Place` and `realValuation`) and remains the natural home for this material in
Mathlib.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Chapter VIII §9.
-/

open Filter Topology

namespace AddCommGroup

variable {G : Type*} [AddCommGroup G] {p h : G → ℝ} {C : ℝ}

/-!
### Functions satisfying the parallelogram law

A function `p : G → ℝ` satisfying the parallelogram law exactly is a quadratic function: it
kills `0`, is even, and scales by `n ^ 2` under `n • ·`. These are the properties that make the
canonical height a quadratic form on the Mordell-Weil group.
-/

/-- The function `p : G → ℝ` satisfies the *parallelogram law*
`p (x + y) + p (x - y) = 2 * p x + 2 * p y`.

This is the unbundled counterpart of a "parallelogram map"; a function satisfying it kills `0`,
is even, and scales by `n ^ 2` under `n • ·`. -/
def IsQuadratic (p : G → ℝ) : Prop :=
  ∀ x y, p (x + y) + p (x - y) = 2 * p x + 2 * p y

namespace IsQuadratic

/-- A function satisfying the parallelogram law vanishes at `0`. -/
lemma map_zero (hp : IsQuadratic p) : p 0 = 0 := by
  -- The parallelogram law at `(0, 0)` reads `p 0 + p 0 = 2 * p 0 + 2 * p 0`.
  have key := hp 0 0
  rw [add_zero, sub_zero] at key
  linarith

/-- A function satisfying the parallelogram law is even. -/
lemma map_neg (hp : IsQuadratic p) (x : G) : p (-x) = p x := by
  -- The parallelogram law at `(0, x)` reads `p x + p (-x) = 2 * p 0 + 2 * p x`.
  have key := hp 0 x
  rw [zero_add, zero_sub, hp.map_zero] at key
  linarith

/-- A function satisfying the parallelogram law is quadratic: it scales by `n ^ 2` under
multiplication by a natural number `n`. -/
lemma map_nsmul (hp : IsQuadratic p) (n : ℕ) (x : G) : p (n • x) = (n : ℝ) ^ 2 * p x := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using hp.map_zero
  | one => simp
  | more n ih ih' =>
    -- The parallelogram law at `(n • x + x, x)` is a two-step recurrence, since
    -- `n • x + x + x = (n + 2) • x` and `n • x + x - x = n • x`.
    have key : p ((n + 2) • x) + p (n • x) = 2 * p ((n + 1) • x) + 2 * p x := by
      have := hp (n • x + x) x
      rwa [add_sub_cancel_right, ← succ_nsmul, ← succ_nsmul] at this
    push_cast at ih ih' ⊢
    linear_combination key - ih + 2 * ih'

/-- A function satisfying the parallelogram law is quadratic: it scales by `n ^ 2` under
multiplication by an integer `n`. -/
lemma map_zsmul (hp : IsQuadratic p) (n : ℤ) (x : G) : p (n • x) = (n : ℝ) ^ 2 * p x := by
  induction n using Int.negInduction with
  | nat n => rw [natCast_zsmul, hp.map_nsmul]; norm_cast
  | neg _ n => rw [neg_smul, hp.map_neg, natCast_zsmul, hp.map_nsmul]; push_cast; ring

end IsQuadratic

/-!
### Tate's limit

The canonical height is the limit of `h (2 ^ n • x) / 4 ^ n`. Convergence needs only the
doubling bound: consecutive terms differ by at most `C / 4 ^ (n + 1)`, so the sequence is Cauchy
by comparison with a geometric series, and `ℝ` is complete. Summing the telescope from `n = 0`
bounds the distance from `h` itself by `C / 3`.
-/

/-- The sequence whose limit defines the canonical height of `x` relative to `h`. -/
noncomputable def canonicalHeightSeq (h : G → ℝ) (x : G) (n : ℕ) : ℝ :=
  h (2 ^ n • x) / 4 ^ n

/-- *Tate's limit*: the canonical height of `x` relative to the height function `h`, defined as
`lim_{n → ∞} h (2 ^ n • x) / 4 ^ n`.

This takes a junk value if the defining sequence does not converge; the results below all assume
a hypothesis on `h` that forces convergence, typically the doubling bound
`∀ x, |h (2 • x) - 4 * h x| ≤ C`. See `AddCommGroup.tendsto_canonicalHeightSeq`. -/
noncomputable def canonicalHeight (h : G → ℝ) (x : G) : ℝ :=
  limUnder atTop (canonicalHeightSeq h x)

@[simp]
lemma canonicalHeightSeq_zero (h : G → ℝ) (x : G) : canonicalHeightSeq h x 0 = h x := by
  simp [canonicalHeightSeq]

/-- The canonical height vanishes at `0`. This is unconditional: the defining sequence at `0` is
`h 0 / 4 ^ n`, which tends to `0` for any `h`. -/
@[simp]
lemma canonicalHeight_zero : canonicalHeight h 0 = 0 := by
  have key : canonicalHeightSeq h 0 = fun n : ℕ => h 0 * (4 ^ n)⁻¹ := by
    funext n; simp [canonicalHeightSeq, div_eq_mul_inv]
  have H : Tendsto (canonicalHeightSeq h (0 : G)) atTop (𝓝 0) := by
    rw [key]; simp only [← inv_pow]
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (4 : ℝ)⁻¹) (by norm_num) (by norm_num))
  exact H.limUnder_eq

section Doubling

variable (hdbl : ∀ x : G, |h (2 • x) - 4 * h x| ≤ C)
include hdbl

/-- Consecutive terms of `canonicalHeightSeq` differ by at most `(C / 4) * (4⁻¹) ^ n`. -/
lemma dist_canonicalHeightSeq_succ_le (x : G) (n : ℕ) :
    dist (canonicalHeightSeq h x n) (canonicalHeightSeq h x (n + 1)) ≤
      C / 4 * (4 : ℝ)⁻¹ ^ n := by
  have h4 : (0 : ℝ) < 4 ^ (n + 1) := by positivity
  have hsmul : (2 : ℕ) ^ (n + 1) • x = 2 • (2 ^ n • x) := by rw [smul_smul, mul_comm, pow_succ]
  -- Consecutive terms differ by the doubling error at `2 ^ n • x`, scaled by `4 ^ (n + 1)`.
  have key : canonicalHeightSeq h x n - canonicalHeightSeq h x (n + 1) =
      -(h (2 • (2 ^ n • x)) - 4 * h (2 ^ n • x)) / 4 ^ (n + 1) := by
    simp only [canonicalHeightSeq, hsmul]
    field_simp
    ring
  calc dist (canonicalHeightSeq h x n) (canonicalHeightSeq h x (n + 1))
      = |h (2 • (2 ^ n • x)) - 4 * h (2 ^ n • x)| / 4 ^ (n + 1) := by
        rw [Real.dist_eq, key, abs_div, abs_neg, abs_of_pos h4]
    _ ≤ C / 4 ^ (n + 1) := by gcongr; exact hdbl _
    _ = C / 4 * (4 : ℝ)⁻¹ ^ n := by rw [inv_pow, pow_succ]; ring

/-- The defining sequence of the canonical height is Cauchy. -/
lemma cauchySeq_canonicalHeightSeq (x : G) : CauchySeq (canonicalHeightSeq h x) :=
  cauchySeq_of_le_geometric (4 : ℝ)⁻¹ (C / 4) (by norm_num)
    (dist_canonicalHeightSeq_succ_le hdbl x)

/-- The defining sequence of the canonical height converges to the canonical height.

This is the only result that unfolds `AddCommGroup.canonicalHeight`; everything else goes
through it. -/
lemma tendsto_canonicalHeightSeq (x : G) :
    Tendsto (canonicalHeightSeq h x) atTop (𝓝 (canonicalHeight h x)) :=
  (cauchySeq_canonicalHeightSeq hdbl x).tendsto_limUnder

/-- The canonical height stays within `C / 3` of the height function it is built from. -/
theorem abs_canonicalHeight_sub_le (x : G) : |canonicalHeight h x - h x| ≤ C / 3 := by
  -- Summing the geometric telescope from `n = 0` bounds the distance by `(C / 4) / (1 - 4⁻¹)`.
  have key : dist (canonicalHeightSeq h x 0) (canonicalHeight h x) ≤ C / 4 / (1 - 4⁻¹) :=
    dist_le_of_le_geometric_of_tendsto₀ (4 : ℝ)⁻¹ (C / 4) (by norm_num)
      (dist_canonicalHeightSeq_succ_le hdbl x) (tendsto_canonicalHeightSeq hdbl x)
  rw [canonicalHeightSeq_zero, Real.dist_eq, abs_sub_comm] at key
  refine key.trans_eq ?_
  rw [show (1 : ℝ) - 4⁻¹ = 3 / 4 by norm_num]
  ring

/-- The canonical height doubles quadratically: `ĥ (2 • x) = 4 * ĥ x`. This is Silverman's
characterising property, and needs only the doubling bound: the defining sequence at `2 • x` is
`4` times the tail of the defining sequence at `x`. -/
lemma canonicalHeight_two_nsmul (x : G) :
    canonicalHeight h (2 • x) = 4 * canonicalHeight h x := by
  have key : canonicalHeightSeq h (2 • x) = fun n : ℕ ↦ 4 * canonicalHeightSeq h x (n + 1) := by
    funext n
    have hsmul : (2 : ℕ) ^ n • (2 • x) = 2 ^ (n + 1) • x := by rw [smul_smul, ← pow_succ]
    simp only [canonicalHeightSeq, hsmul, pow_succ]
    field_simp
  -- A sequence and its tail have the same limit.
  have htail : Tendsto (fun n : ℕ ↦ 4 * canonicalHeightSeq h x (n + 1)) atTop
      (𝓝 (4 * canonicalHeight h x)) :=
    ((tendsto_canonicalHeightSeq hdbl x).comp (tendsto_add_atTop_nat 1)).const_mul 4
  exact tendsto_nhds_unique (tendsto_canonicalHeightSeq hdbl (2 • x)) (key ▸ htail)

/-- The canonical height is nonnegative, provided the height function is. -/
lemma canonicalHeight_nonneg (hh : ∀ x : G, 0 ≤ h x) (x : G) : 0 ≤ canonicalHeight h x :=
  ge_of_tendsto' (tendsto_canonicalHeightSeq hdbl x) fun n ↦ div_nonneg (hh _) (by positivity)

/-- The canonical height inherits the Northcott property from the height function it is built
from: there are only finitely many elements of bounded canonical height. -/
lemma northcott_canonicalHeight [Northcott h] : Northcott (canonicalHeight h) where
  finite_le b := by
    -- An element of canonical height at most `b` has `h`-height at most `b + C / 3`.
    refine (Northcott.finite_le (h := h) (b + C / 3)).subset fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    have := neg_le_of_abs_le (abs_canonicalHeight_sub_le hdbl x)
    linarith

end Doubling

/-!
### The exact parallelogram law

Applying the approximate parallelogram law at `2 ^ n • x` and `2 ^ n • y` and dividing by `4 ^ n`
makes the error term `C / 4 ^ n` vanish in the limit, so the canonical height satisfies the
parallelogram law on the nose. Everything quadratic about `ĥ` follows from this.
-/

section Parallelogram

variable (hpar : ∀ x y : G, |h (x + y) + h (x - y) - 2 * (h x + h y)| ≤ C)
include hpar

/-- The approximate parallelogram law implies the doubling bound, with constant `C + |h 0|`.
Take `y := x`, so that `x - y = 0`. -/
lemma abs_two_nsmul_sub_four_mul_le (x : G) :
    |h (2 • x) - 4 * h x| ≤ C + |h 0| := by
  -- The parallelogram law at `(x, x)` reads `|h (2 • x) + h 0 - 2 * (h x + h x)| ≤ C`.
  have key := hpar x x
  rw [sub_self, ← two_nsmul] at key
  -- Discarding the `h 0` term costs at most `|h 0|`.
  obtain ⟨hlb, hub⟩ := abs_le.mp key
  have h0lb := neg_abs_le (h 0)
  have h0ub := le_abs_self (h 0)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The canonical height satisfies the parallelogram law exactly**, even though the height
function it is built from satisfies it only up to a bounded error. -/
theorem isQuadratic_canonicalHeight : IsQuadratic (canonicalHeight h) := by
  intro x y
  -- The doubling bound, with the larger constant `C + |h 0|`, gives convergence at each point.
  have hdbl := abs_two_nsmul_sub_four_mul_le hpar
  have hadd := tendsto_canonicalHeightSeq (C := C + |h 0|) hdbl (x + y)
  have hsub := tendsto_canonicalHeightSeq (C := C + |h 0|) hdbl (x - y)
  have hx := tendsto_canonicalHeightSeq (C := C + |h 0|) hdbl x
  have hy := tendsto_canonicalHeightSeq (C := C + |h 0|) hdbl y
  -- At stage `n`, the parallelogram defect of the sequences is the defect of `h` at
  -- `(2 ^ n • x, 2 ^ n • y)` divided by `4 ^ n`, hence at most `C * (4⁻¹) ^ n`.
  have hdefect : ∀ n : ℕ, |canonicalHeightSeq h (x + y) n + canonicalHeightSeq h (x - y) n -
      (2 * canonicalHeightSeq h x n + 2 * canonicalHeightSeq h y n)| ≤ C * (4 : ℝ)⁻¹ ^ n := by
    intro n
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    have key : canonicalHeightSeq h (x + y) n + canonicalHeightSeq h (x - y) n -
        (2 * canonicalHeightSeq h x n + 2 * canonicalHeightSeq h y n) =
          (h (2 ^ n • x + 2 ^ n • y) + h (2 ^ n • x - 2 ^ n • y) -
            2 * (h (2 ^ n • x) + h (2 ^ n • y))) / 4 ^ n := by
      simp only [canonicalHeightSeq, smul_add, smul_sub]
      ring
    rw [key, abs_div, abs_of_pos h4, inv_pow, ← div_eq_mul_inv]
    gcongr
    exact hpar _ _
  -- The bound is geometric, so the defect is squeezed to `0`.
  have hgeom : Tendsto (fun n : ℕ ↦ C * (4 : ℝ)⁻¹ ^ n) atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (4 : ℝ)⁻¹) (by norm_num) (by norm_num)
    simpa using hpow.const_mul C
  have hzero : Tendsto (fun n ↦ canonicalHeightSeq h (x + y) n + canonicalHeightSeq h (x - y) n -
      (2 * canonicalHeightSeq h x n + 2 * canonicalHeightSeq h y n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n ↦ (Real.norm_eq_abs _).trans_le (hdefect n)) hgeom
  -- That same sequence tends to the difference of the two sides, which is therefore `0`.
  refine sub_eq_zero.mp (tendsto_nhds_unique ?_ hzero)
  exact (hadd.add hsub).sub ((hx.const_mul 2).add (hy.const_mul 2))

/-- The canonical height is even. -/
lemma canonicalHeight_neg (x : G) : canonicalHeight h (-x) = canonicalHeight h x :=
  (isQuadratic_canonicalHeight hpar).map_neg x

/-- The canonical height is quadratic: `ĥ (n • x) = n ^ 2 * ĥ x` for `n : ℕ`. -/
lemma canonicalHeight_nsmul (n : ℕ) (x : G) :
    canonicalHeight h (n • x) = (n : ℝ) ^ 2 * canonicalHeight h x :=
  (isQuadratic_canonicalHeight hpar).map_nsmul n x

/-- The canonical height is quadratic: `ĥ (n • x) = n ^ 2 * ĥ x` for `n : ℤ`. -/
lemma canonicalHeight_zsmul (n : ℤ) (x : G) :
    canonicalHeight h (n • x) = (n : ℝ) ^ 2 * canonicalHeight h x :=
  (isQuadratic_canonicalHeight hpar).map_zsmul n x

/-- **The canonical height vanishes exactly on the torsion subgroup.**

For the forward direction, `ĥ x = 0` forces the whole cyclic subgroup generated by `x` to have
bounded height, hence to be finite by the Northcott property. -/
theorem canonicalHeight_eq_zero_iff {x : G} [Northcott h] :
    canonicalHeight h x = 0 ↔ IsOfFinAddOrder x := by
  constructor
  · -- Every multiple satisfies `ĥ (n • x) = n ^ 2 * ĥ x = 0`, so it lies within `(C + |h 0|) / 3`
    -- of `0` for `h` too. The Northcott property makes the set of multiples finite, and a finite
    -- set of multiples is exactly finite additive order.
    intro hx
    rw [← finite_multiples, AddSubmonoid.coe_multiples]
    refine (Northcott.finite_le (h := h) ((C + |h 0|) / 3)).subset
      (Set.range_subset_iff.mpr fun n ↦ ?_)
    have hzero : canonicalHeight h (n • x) = 0 := by
      rw [canonicalHeight_nsmul hpar, hx, mul_zero]
    have hclose := neg_le_of_abs_le <| abs_canonicalHeight_sub_le (C := C + |h 0|)
      (abs_two_nsmul_sub_four_mul_le hpar) (n • x)
    rw [hzero] at hclose
    simp only [Set.mem_setOf_eq]
    linarith
  · -- Some `n ≠ 0` has `n • x = 0`, and then `0 = ĥ 0 = ĥ (n • x) = n ^ 2 * ĥ x` with `n ^ 2 ≠ 0`.
    intro hx
    obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.mp hx
    have hn2 : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (Int.cast_ne_zero.mpr hn)
    have key : (n : ℝ) ^ 2 * canonicalHeight h x = 0 := by
      rw [← canonicalHeight_zsmul hpar, hnx, canonicalHeight_zero]
    exact (mul_eq_zero.mp key).resolve_left hn2

/-- **The canonical height is the unique quadratic function at bounded distance from `h`.**

If `h'` stays within a bounded distance of `h` and scales by `n ^ 2` under `n • ·` for a single
integer `n` with `1 < |n|`, then `h'` is the canonical height. This is what makes `ĥ`
*canonical*. -/
theorem eq_canonicalHeight_of_abs_sub_le_of_map_zsmul {h' : G → ℝ} {C' : ℝ}
    (hbdd : ∀ x : G, |h' x - h x| ≤ C') {n : ℤ} (hn : 1 < |n|)
    (hn' : ∀ x : G, h' (n • x) = (n : ℝ) ^ 2 * h' x) (x : G) :
    h' x = canonicalHeight h x := by
  -- `1 < |n|` makes `((n : ℝ) ^ 2)⁻¹` a legitimate geometric ratio.
  have hnR : 1 < |(n : ℝ)| := by exact_mod_cast hn
  have hsq : 1 < (n : ℝ) ^ 2 := by rw [← sq_abs]; exact one_lt_pow₀ hnR two_ne_zero
  have hsq₀ : (0 : ℝ) < (n : ℝ) ^ 2 := zero_lt_one.trans hsq
  -- `D` is the crude bound on `|h' - ĥ|`, valid before any sharpening.
  set D := C' + (C + |h 0|) / 3 with hD
  -- Both `h'` and `ĥ` lie within a bounded distance of `h`, and both scale by `(n : ℝ) ^ 2`
  -- under `n • ·`. Applying the crude bound at `n ^ m • y` therefore sharpens it by `(n ^ 2) ^ m`.
  have key : ∀ (m : ℕ) (y : G),
      |h' y - canonicalHeight h y| ≤ D * ((n : ℝ) ^ 2)⁻¹ ^ m := by
    intro m
    induction m with
    | zero =>
      intro y
      obtain ⟨h₁, h₂⟩ := abs_le.mp (hbdd y)
      obtain ⟨h₃, h₄⟩ := abs_le.mp <| abs_canonicalHeight_sub_le (C := C + |h 0|)
        (abs_two_nsmul_sub_four_mul_le hpar) y
      rw [pow_zero, mul_one, abs_le]
      constructor <;> linarith
    | succ m ih =>
      intro y
      rw [pow_succ, ← mul_assoc, ← div_eq_mul_inv, le_div_iff₀' hsq₀]
      calc (n : ℝ) ^ 2 * |h' y - canonicalHeight h y|
          = |h' (n • y) - canonicalHeight h (n • y)| := by
            rw [hn', canonicalHeight_zsmul hpar, ← mul_sub, abs_mul, abs_of_pos hsq₀]
        _ ≤ D * ((n : ℝ) ^ 2)⁻¹ ^ m := ih (n • y)
  -- The right-hand side tends to `0`, so the distance is at most `0`, hence exactly `0`.
  have hgeo : Tendsto (fun m : ℕ ↦ D * ((n : ℝ) ^ 2)⁻¹ ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hsq₀.le)
      (inv_lt_one_of_one_lt₀ hsq)).const_mul D
  have hle : |h' x - canonicalHeight h x| ≤ 0 := ge_of_tendsto' hgeo fun m ↦ key m x
  have hzero : |h' x - canonicalHeight h x| = 0 := le_antisymm hle (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

end Parallelogram

end AddCommGroup

end
