import Mathlib

/-!
# Comparator challenge statement (the Mordell-Weil Theorem over number fields)

A self-contained restatement of this repository's **Mordell-Weil Theorem**
(`WeierstrassCurve.Affine.fg_point_of_numberField` in `EllipticCurves/MordellWeil.lean`), with a
`sorry` proof, for verification with
[leanprover/comparator](https://github.com/leanprover/comparator).

This file imports **only Mathlib**. Every notion in the statement — the affine Weierstrass curve
`WeierstrassCurve.Affine`, its group of rational points `Point`, `WeierstrassCurve.IsElliptic`,
`NumberField`, and finite generation `AddGroup.FG` — is a Mathlib definition, so the challenge
reproduces nothing from this repository and is a complete, self-contained specification of the
claim. The companion `Solution.lean` discharges the `sorry` with the library theorem.
-/

/-- **The Mordell-Weil Theorem** over a number field: the group `E(K)` of `K`-rational points of an
elliptic curve `E` over a number field `K` is finitely generated. -/
theorem challenge_fg_point_of_numberField {F : Type*} [Field F] [NumberField F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} [W.toAffine.IsElliptic] :
    AddGroup.FG W.Point :=
  sorry
