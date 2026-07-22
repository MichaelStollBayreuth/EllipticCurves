import EllipticCurves.MordellWeil

/-!
# Comparator solution (the Mordell-Weil Theorem over number fields)

Proof of `challenge_fg_point_of_numberField` from `Challenge.lean`, discharged by the library
theorem `WeierstrassCurve.Affine.fg_point_of_numberField`. Every notion in the statement is a
Mathlib definition, so Comparator's body-level comparison of the challenge and solution statements
is over Mathlib definitions only — the statements are identical and depend on nothing in this
repository beyond the proof itself.
-/

/-- **The Mordell-Weil Theorem** over a number field: the group `E(K)` of `K`-rational points of an
elliptic curve `E` over a number field `K` is finitely generated. -/
theorem challenge_fg_point_of_numberField {F : Type*} [Field F] [NumberField F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F} [W.toAffine.IsElliptic] :
    AddGroup.FG W.Point :=
  WeierstrassCurve.Affine.fg_point_of_numberField
