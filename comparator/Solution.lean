import EllipticCurves.MordellWeil
import EllipticCurves.RankExample

/-!
# Comparator solutions

Proofs of `challenge_fg_point_of_numberField` and `challenge_nonempty_point_addEquiv_int` from
`Challenge.lean`, discharged by the library theorems
`WeierstrassCurve.Affine.fg_point_of_numberField` and
`InfiniteOrderExample.nonempty_point_addEquiv_int`. Every notion in the statements is a Mathlib
definition (the example curve and its `IsElliptic` instance are restated here verbatim from the
challenge), so Comparator's body-level comparison of the challenge and solution statements is over
Mathlib definitions only.
-/

/-- **The Mordell-Weil Theorem** over a number field: the group `E(K)` of `K`-rational points of an
elliptic curve `E` over a number field `K` is finitely generated. -/
theorem challenge_fg_point_of_numberField {F : Type*} [Field F] [NumberField F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} [W.toAffine.IsElliptic] :
    AddGroup.FG W.Point :=
  WeierstrassCurve.Affine.fg_point_of_numberField

/-- The curve `y² = x³ - x + 1` over `ℚ`. -/
def challengeCurve : WeierstrassCurve.Affine ℚ := ⟨0, 0, 0, -1, 1⟩

/-- `challengeCurve` is an elliptic curve: its discriminant is `-368 ≠ 0`. -/
instance : challengeCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [challengeCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **The Mordell-Weil group of `y² = x³ - x + 1` over `ℚ` is infinite cyclic.**
`challengeCurve` is definitionally `InfiniteOrderExample.E`, so the library theorem applies. -/
theorem challenge_nonempty_point_addEquiv_int : Nonempty (challengeCurve.Point ≃+ ℤ) :=
  InfiniteOrderExample.nonempty_point_addEquiv_int
