import Mathlib

/-!
# Comparator challenge statements

Self-contained restatements of this repository's two headline results, with `sorry` proofs, for
verification with [leanprover/comparator](https://github.com/leanprover/comparator):

* the **Mordell-Weil Theorem** over a number field
  (`WeierstrassCurve.Affine.fg_point_of_numberField` in `EllipticCurves/MordellWeil.lean`);
* the **show-piece example**: the Mordell-Weil group of `y² = x³ - x + 1` over `ℚ` is infinite
  cyclic (`InfiniteOrderExample.nonempty_point_addEquiv_int` in `EllipticCurves/RankExample.lean`).

This file imports **only Mathlib**. Every notion in the statements — the affine Weierstrass curve
`WeierstrassCurve.Affine`, its group of rational points `Point`, `WeierstrassCurve.IsElliptic`,
`NumberField`, finite generation `AddGroup.FG`, and `≃+` — is a Mathlib definition, so the
challenge reproduces nothing from this repository and is a complete, self-contained specification
of the claims. (The example curve and its `IsElliptic` instance are *defined* here, from Mathlib
notions only.) The companion `Solution.lean` discharges the `sorry`s with the library theorems.
-/

/-- **The Mordell-Weil Theorem** over a number field: the group `E(K)` of `K`-rational points of an
elliptic curve `E` over a number field `K` is finitely generated. -/
theorem challenge_fg_point_of_numberField {F : Type*} [Field F] [NumberField F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} [W.toAffine.IsElliptic] :
    AddGroup.FG W.Point :=
  sorry

/-- The curve `y² = x³ - x + 1` over `ℚ`. -/
def challengeCurve : WeierstrassCurve.Affine ℚ := ⟨0, 0, 0, -1, 1⟩

/-- `challengeCurve` is an elliptic curve: its discriminant is `-368 ≠ 0`. -/
instance : challengeCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  norm_num [challengeCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **The Mordell-Weil group of `y² = x³ - x + 1` over `ℚ` is infinite cyclic.** -/
theorem challenge_nonempty_point_addEquiv_int : Nonempty (challengeCurve.Point ≃+ ℤ) :=
  sorry
