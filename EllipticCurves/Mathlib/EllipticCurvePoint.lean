module

public import Mathlib

@[expose] public section

/-!
# Points of Weierstrass curves over finite fields: decidability and finiteness

This file provides `Decidable` instances for the predicates `WeierstrassCurve.Affine.Equation`
and `WeierstrassCurve.Affine.Nonsingular` (over any commutative ring with decidable equality),
and deduces `Finite` and `Fintype` instances for the type `WeierstrassCurve.Affine.Point` of
nonsingular points of a Weierstrass curve over a finite ring, via Mathlib's
`WeierstrassCurve.Affine.nonsingularPointEquiv`.

The decision procedure goes through `equation_iff`/`nonsingular_iff`, so it evaluates the
Weierstrass polynomials directly in the base ring, with no `Polynomial` arithmetic involved.
Consequently, for a concrete curve over `ZMod p` the number of points is computable by `decide`:
`Fintype.card W.Point` enumerates the pairs in `ZMod p × ZMod p` and filters by the (decidable)
nonsingularity condition.

We also provide `WeierstrassCurve.Affine.Point.mapEquiv`, the group *isomorphism* on points
induced by an isomorphism of base fields (the equiv version of
`WeierstrassCurve.Affine.Point.map`); it transports point counts along residue-field
identifications such as `ℤ ⧸ (p) ≃+* ZMod p`.
-/

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

instance [DecidableEq R] (x y : R) : Decidable (W'.Equation x y) :=
  decidable_of_iff _ (W'.equation_iff x y).symm

instance [DecidableEq R] (x y : R) : Decidable (W'.Nonsingular x y) :=
  decidable_of_iff _ (W'.nonsingular_iff x y).symm

instance [Finite R] : Finite W'.Point :=
  .of_equiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

instance [Fintype R] [DecidableEq R] : Fintype W'.Point :=
  .ofEquiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

namespace Point

variable {S F K : Type*} [CommRing S] [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] (σ : F ≃ₐ[S] K)

/-- The group isomorphism on nonsingular points induced by an algebra isomorphism
`σ : F ≃ₐ[S] K`, where `W` is defined over a subring of a ring `S`, and `F` and `K` are field
extensions of `S`; the equiv version of `WeierstrassCurve.Affine.Point.map`. -/
noncomputable def mapEquiv : (W'⁄F).Point ≃+ (W'⁄K).Point where
  toFun := map (σ : F →ₐ[S] K)
  invFun := map (σ.symm : K →ₐ[S] F)
  map_add' := map_add _
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
        rw [map_some, map_some, Point.some.injEq]
        exact ⟨σ.symm_apply_apply x, σ.symm_apply_apply y⟩
  right_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
        rw [map_some, map_some, Point.some.injEq]
        exact ⟨σ.apply_symm_apply x, σ.apply_symm_apply y⟩

@[simp] lemma coe_mapEquiv : ⇑(mapEquiv (W' := W') σ) = ⇑(map (W' := W') (σ : F →ₐ[S] K)) :=
  rfl

end Point

end WeierstrassCurve.Affine

end
