module

public import Mathlib
public import EllipticCurves.Mathlib.CanonicalHeight
public import EllipticCurves.MordellWeil

@[expose] public section

/-!
# The canonical height on an elliptic curve

We specialise the general construction of `EllipticCurves.Mathlib.CanonicalHeight` to the
Mordell-Weil group `W.Point` of an elliptic curve, taking for the height function the naïve
height `WeierstrassCurve.Affine.Point.naiveHeight` of `EllipticCurves.MordellWeil`. The result is
the **canonical**, or **Néron-Tate**, height
`ĥ(P) = lim_{n → ∞} h(2ⁿ P) / 4ⁿ`
where `h = naiveHeight`.

The two inputs are already available: `approx_parallelogram_law` supplies the approximate
parallelogram law for `naiveHeight`, and `finite_naiveHeight_le` (via the `Northcott` instance
for `naiveHeight`) supplies the finiteness needed to identify the vanishing locus of `ĥ` with the
torsion subgroup.

## Main definitions

* `WeierstrassCurve.Affine.Point.canonicalHeight`: the canonical height of a point.

## Main results

* `WeierstrassCurve.Affine.abs_canonicalHeight_sub_naiveHeight_le`: `ĥ` and the naïve
  height differ by a bounded amount.
* `WeierstrassCurve.Affine.isQuadratic_canonicalHeight`: `ĥ` satisfies the parallelogram law
  *exactly*.
* `WeierstrassCurve.Affine.Point.canonicalHeight_nsmul` and `.canonicalHeight_zsmul`:
  `ĥ (n • P) = n ^ 2 * ĥ P`.
* `WeierstrassCurve.Affine.Point.eq_canonicalHeight_of_abs_sub_le_of_map_zsmul`: the uniqueness
  characterisation — `ĥ` is the only function at bounded distance from the naïve height that
  scales by `n ^ 2` under `n • ·`.
* `WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_iff`: `ĥ P = 0` exactly when `P` is
  torsion.
* `WeierstrassCurve.Affine.finite_canonicalHeight_le`: there are finitely many points of bounded
  canonical height.

## Implementation notes

The three lemmas `Point.naiveHeight_zero`, `Point.naiveHeight_neg` and `Point.naiveHeight_nonneg`
below are about the naïve height rather than the canonical one, and would sit just as naturally
next to `Point.naiveHeight` in `EllipticCurves.MordellWeil`. They are collected here to keep this
contribution to new files only.

Note that what is *not* provided is any *effective* bound on `|ĥ - naiveHeight|`: the constants
here are existentially quantified throughout. An effective bound (in terms of the Weierstrass
coefficients) is what would be needed to turn `ĥ` into a search for generators of `W.Point`.
-/

open Filter Height Topology

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

section AAV

variable [AdmissibleAbsValues F]

/-!
### Basic properties of the naïve height

All three are immediate from the corresponding facts about `Point.xRep` and `Height.logHeight`.
-/

/-- The naïve height of the point at infinity is `0`. -/
@[simp]
lemma Point.naiveHeight_zero : (0 : W.Point).naiveHeight = 0 := by
  simp [naiveHeight_eq_logHeight₁]

/-- The naïve height is even, since `-P` and `P` have the same `x`-coordinate. -/
@[simp]
lemma Point.naiveHeight_neg (P : W.Point) : (-P).naiveHeight = P.naiveHeight := by
  simp [naiveHeight_eq_logHeight]

/-- The naïve height is nonnegative. -/
lemma Point.naiveHeight_nonneg (P : W.Point) : 0 ≤ P.naiveHeight :=
  logHeight_nonneg _

/-!
### The canonical height

Defining the canonical height needs the group law on `W.Point`, hence `DecidableEq F`; showing
that it is the honest limit rather than a junk value needs the approximate parallelogram law,
hence also that `W` is elliptic.
-/

variable [DecidableEq F]

/-- The **canonical** (or **Néron-Tate**) **height** of a point on an elliptic curve: Tate's limit
`lim_{n → ∞} naiveHeight (2 ^ n • P) / 4 ^ n`.

For this to be the honest limit rather than a junk value one needs the approximate parallelogram
law, which holds as soon as `W` is elliptic; see
`WeierstrassCurve.Affine.Point.tendsto_canonicalHeightSeq`. -/
noncomputable def Point.canonicalHeight (P : W.Point) : ℝ :=
  AddCommGroup.canonicalHeight Point.naiveHeight P

/-- The canonical height of the point at infinity is `0`. This is unconditional: it needs neither
the approximate parallelogram law nor `Point.naiveHeight_zero`. -/
@[simp]
lemma Point.canonicalHeight_zero : (0 : W.Point).canonicalHeight = 0 :=
  AddCommGroup.canonicalHeight_zero

variable [W.toAffine.IsElliptic]

variable (W) in
/-- The naïve height satisfies a doubling bound: `naiveHeight (2 • P)` differs from
`4 * naiveHeight P` by a bounded amount. This is the approximate parallelogram law
`approx_parallelogram_law` with `Q := P`. -/
lemma abs_naiveHeight_two_nsmul_sub_four_mul_le :
    ∃ C, ∀ P : W.Point, |(2 • P).naiveHeight - 4 * P.naiveHeight| ≤ C := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact ⟨_, AddCommGroup.abs_two_nsmul_sub_four_mul_le hC⟩

/-- The defining sequence of the canonical height converges to it. -/
theorem Point.tendsto_canonicalHeightSeq (P : W.Point) :
    Tendsto (fun n : ℕ ↦ (2 ^ n • P).naiveHeight / 4 ^ n) atTop (𝓝 P.canonicalHeight) := by
  obtain ⟨C, hC⟩ := abs_naiveHeight_two_nsmul_sub_four_mul_le W
  exact AddCommGroup.tendsto_canonicalHeightSeq hC P

variable (W) in
/-- The canonical height and the naïve height differ by a bounded amount.

The bound is not effective: `C` is existentially quantified. -/
theorem abs_canonicalHeight_sub_naiveHeight_le :
    ∃ C, ∀ P : W.Point, |P.canonicalHeight - P.naiveHeight| ≤ C := by
  obtain ⟨C, hC⟩ := abs_naiveHeight_two_nsmul_sub_four_mul_le W
  exact ⟨C / 3, AddCommGroup.abs_canonicalHeight_sub_le hC⟩

/-- The canonical height is even. -/
@[simp]
lemma Point.canonicalHeight_neg (P : W.Point) : (-P).canonicalHeight = P.canonicalHeight := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.canonicalHeight_neg hC P

/-- The canonical height doubles quadratically: `ĥ (2 • P) = 4 * ĥ P`. This is the characterising
property in Silverman, and the natural input to
`WeierstrassCurve.Affine.Point.eq_canonicalHeight_of_abs_sub_le_of_map_zsmul`. -/
lemma Point.canonicalHeight_two_nsmul (P : W.Point) :
    (2 • P).canonicalHeight = 4 * P.canonicalHeight := by
  obtain ⟨C, hC⟩ := abs_naiveHeight_two_nsmul_sub_four_mul_le W
  exact AddCommGroup.canonicalHeight_two_nsmul hC P

/-- The canonical height is nonnegative. -/
lemma Point.canonicalHeight_nonneg (P : W.Point) : 0 ≤ P.canonicalHeight := by
  obtain ⟨C, hC⟩ := abs_naiveHeight_two_nsmul_sub_four_mul_le W
  exact AddCommGroup.canonicalHeight_nonneg hC Point.naiveHeight_nonneg P

variable (W) in
/-- **The canonical height satisfies the parallelogram law exactly**, in contrast to the naïve
height, which satisfies it only up to a bounded error (`approx_parallelogram_law`). Equivalently,
the canonical height is a quadratic function on the Mordell-Weil group.

Applied to points `P` and `Q` this reads
`(P + Q).canonicalHeight + (P - Q).canonicalHeight =
2 * P.canonicalHeight + 2 * Q.canonicalHeight`. -/
theorem isQuadratic_canonicalHeight :
    AddCommGroup.IsQuadratic (Point.canonicalHeight (F := F) (W := W)) := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.isQuadratic_canonicalHeight hC

/-- The canonical height is quadratic: `ĥ (n • P) = n ^ 2 * ĥ P` for `n : ℕ`. -/
lemma Point.canonicalHeight_nsmul (n : ℕ) (P : W.Point) :
    (n • P).canonicalHeight = (n : ℝ) ^ 2 * P.canonicalHeight := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.canonicalHeight_nsmul hC n P

/-- The canonical height is quadratic: `ĥ (n • P) = n ^ 2 * ĥ P` for `n : ℤ`. -/
lemma Point.canonicalHeight_zsmul (n : ℤ) (P : W.Point) :
    (n • P).canonicalHeight = (n : ℝ) ^ 2 * P.canonicalHeight := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.canonicalHeight_zsmul hC n P

/-- **The canonical height is the unique quadratic function at bounded distance from the naïve
height.** -/
theorem Point.eq_canonicalHeight_of_abs_sub_le_of_map_zsmul {h' : W.Point → ℝ} {C : ℝ}
    (hbdd : ∀ P : W.Point, |h' P - P.naiveHeight| ≤ C) {n : ℤ} (hn : 1 < |n|)
    (hn' : ∀ P : W.Point, h' (n • P) = (n : ℝ) ^ 2 * h' P) (P : W.Point) :
    h' P = P.canonicalHeight := by
  obtain ⟨C', hC'⟩ := approx_parallelogram_law W
  exact AddCommGroup.eq_canonicalHeight_of_abs_sub_le_of_map_zsmul hC' hbdd hn hn' P

section Northcott

/-- The canonical height inherits the Northcott property from the naïve height, mirroring the
instance for `Point.naiveHeight` in `EllipticCurves.MordellWeil`. -/
instance [Northcott (logHeight₁ (K := F))] :
    Northcott (Point.canonicalHeight (F := F) (W := W)) := by
  obtain ⟨C, hC⟩ := abs_naiveHeight_two_nsmul_sub_four_mul_le W
  exact AddCommGroup.northcott_canonicalHeight hC

variable [Northcott (logHeight₁ (K := F))]

/-- **The canonical height vanishes exactly on the torsion subgroup** of the Mordell-Weil group. -/
theorem Point.canonicalHeight_eq_zero_iff {P : W.Point} :
    P.canonicalHeight = 0 ↔ IsOfFinAddOrder P := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.canonicalHeight_eq_zero_iff hC

variable (W) in
/-- The set of points of bounded canonical height is finite. This is the canonical-height
counterpart of `finite_naiveHeight_le`. -/
lemma finite_canonicalHeight_le (B : ℝ) : {P : W.Point | P.canonicalHeight ≤ B}.Finite :=
  Northcott.finite_le B

end Northcott

end AAV

end WeierstrassCurve.Affine

end
