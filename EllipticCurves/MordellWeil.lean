/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib
public import EllipticCurves.VariableChange
public import EllipticCurves.WeakMordellWeil

@[expose] public section

/-!
# The Mordell-Weil Theorem

The goal of this file is the **Mordell-Weil Theorem**: the group `E(K)` of `K`-rational
points of an elliptic curve `E` over a number field `K` is finitely generated. It comes in
three versions:

* `WeierstrassCurve.Affine.fg_point`: for `E` given by an equation `y² = x³ + a₂x² + a₄x + a₆` (that
  is, with `a₁ = a₃ = 0`) over the fraction field `K` of a Dedekind domain, where `K` has admissible
  absolute values satisfying the Northcott property and the needed class-group and unit-group
  finiteness statements are taken as hypotheses;
* `WeierstrassCurve.Affine.fg_point_of_variableChange`: for an arbitrary `E` over such a `K` with
  `2` invertible, by completing the square and transferring along the isomorphism of point groups
  from `EllipticCurves.VariableChange`;
* `WeierstrassCurve.Affine.fg_point_of_numberField`: for an arbitrary `E` over a number field, where
  all hypotheses are theorems.

The proof is by descent (`AddCommGroup.fg_of_descent'`, in Mathlib): the Weak Mordell-Weil
Theorem of `EllipticCurves.WeakMordellWeil` provides the finiteness of `E(K)/2E(K)`, and the
naïve height `WeierstrassCurve.Affine.Point.naiveHeight` provides the required height
function, via the *approximate parallelogram law*
`WeierstrassCurve.Affine.approx_parallelogram_law` and the Northcott property.
-/

/-
We work with affine points; this seems to be quite a bit less painful
than using projective points.
-/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F}

section Northcott

open Height

variable [AdmissibleAbsValues F] [Northcott (logHeight₁ (K := F))] [DecidableEq F]
  [W.toAffine.IsElliptic]

/-- **The Mordell-Weil Theorem**, general version: `E(K)` is finitely generated, for an
elliptic curve `E` given by an equation `y² = f(x)` with a monic cubic `f` (`a₁ = a₃ = 0`)
over a field `K` such that
* `K` has admissible absolute values satisfying the Northcott property (so heights work);
* `K` is the fraction field of a Dedekind domain `R`; and
* for each irreducible factor `p` of `f`, the integral closure of `R` in `K[X]/(p)` has
  finite class group and finitely generated unit group.

For `K` a number field all of these hold; see `WeierstrassCurve.Affine.fg_point_of_numberField`.

Note that the per-factor hypotheses cannot be replaced by the corresponding hypotheses on `R`
itself: by a theorem of Claborn, refined by Leedham-Green and by Clark
(*Elliptic Dedekind domains revisited*, Enseign. Math. 55 (2009)), **every** abelian group is
the class group of the integral closure of a PID in a separable *quadratic* field extension,
so `Finite (ClassGroup R)` gives no control over the class groups of the factors. (Whether
adding `Group.FG Rˣ` rescues the implication appears to be unknown; all known proofs of the
per-factor statements require `K` to be a global field.) -/
theorem fg_point (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] [W.IsCharNeTwoNF]
    [(p : W.f.Factors) → Finite (ClassGroup (W.ringOfIntegersFactor R p))]
    [(p : W.f.Factors) → Group.FG (W.ringOfIntegersFactor R p)ˣ] :
    AddGroup.FG W.Point := by
  have H₂ (P : W.Point) : 0 ≤ P.naiveHeight := by
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.fg_of_descent' (W.finite_index_range_nsmulAddMonoidHom_two R) H₂ hC

/-- **The Mordell-Weil Theorem** for an arbitrary Weierstrass curve: `E(K)` is finitely generated,
given an admissible change of variables `C` bringing `E` into the normal form `y² = cubic` (i.e.,
`a₁ = a₃ = 0`), together with the finiteness hypotheses of `WeierstrassCurve.Affine.fg_point` for
the model `C • E`. The result is transferred along the isomorphism of point groups
`WeierstrassCurve.Affine.Point.equivVariableChange`.

Such a `C` exists whenever `2` is invertible in `K`
(`WeierstrassCurve.exists_variableChange_isCharNeTwoNF`, completing the square). -/
theorem fg_point_of_variableChange (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] (C : VariableChange F) [(C • W).IsCharNeTwoNF]
    [(p : (C • W).toAffine.f.Factors) →
      Finite (ClassGroup ((C • W).toAffine.ringOfIntegersFactor R p))]
    [(p : (C • W).toAffine.f.Factors) →
      Group.FG ((C • W).toAffine.ringOfIntegersFactor R p)ˣ] :
    AddGroup.FG W.Point := by
  have := fg_point (W := (C • W).toAffine) R
  exact AddGroup.fg_of_surjective (f := (Point.equivVariableChange W C).toAddMonoidHom)
    (Point.equivVariableChange W C).surjective

end Northcott

section NumberField

open NumberField

variable {F : Type*} [Field F] [NumberField F] [DecidableEq F] {W : Affine F}
  [W.toAffine.IsElliptic]

/-- **The Mordell-Weil Theorem**: the group `E(K)` of `K`-rational points of an elliptic
curve `E` over a number field `K` is finitely generated.

The square on the left-hand side is completed by an admissible change of variables (possible since
`K` has characteristic `0`), and the finiteness hypotheses of `WeierstrassCurve.Affine.fg_point` for
the resulting model are the class number theorem and Dirichlet's unit theorem. -/
theorem fg_point_of_numberField : AddGroup.FG W.Point := by
  have := invertibleOfNonzero (two_ne_zero (α := F))
  obtain ⟨C, hC⟩ := exists_variableChange_isCharNeTwoNF (W := W)
  have (p : (C • W).toAffine.f.Factors) :
      Finite (ClassGroup ((C • W).toAffine.ringOfIntegersFactor (𝓞 F) p)) :=
    NumberField.finite_classGroup_integralClosure F (AdjoinRoot (p : Polynomial F))
  have (p : (C • W).toAffine.f.Factors) :
      Group.FG ((C • W).toAffine.ringOfIntegersFactor (𝓞 F) p)ˣ :=
    NumberField.fg_units_integralClosure F (AdjoinRoot (p : Polynomial F))
  exact fg_point_of_variableChange (𝓞 F) C

end NumberField

end WeierstrassCurve.Affine

end
