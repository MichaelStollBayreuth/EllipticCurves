module

public import Mathlib

@[expose] public section

/-!
# Example: `(1, 1)` on `y² = x³ - x + 1` has infinite order

The point `P = (1, 1)` on the elliptic curve `E : y² = x³ - x + 1` over `ℚ` has infinite order.
A certificate is that its reductions at two primes have coprime orders: modulo `3` the reduced
point is killed by `7` (indeed `#E(𝔽₃) = 7`) and modulo `5` it is killed by `8` (`#E(𝔽₅) = 8`),
and `gcd(7, 8) = 1`. This is exactly the input to
`WeierstrassCurve.Affine.not_isOfFinAddOrder_of_coprime_red`.

This file records the two finite-field torsion facts, `nsmul_seven_eq_zero_mod_three` and
`nsmul_eight_eq_zero_mod_five`, over `ZMod 3` and `ZMod 5`.

## Implementation notes

The two torsion facts are closed by `decide +kernel`. Mathlib's `WeierstrassCurve.Affine.Point`
addition is `noncomputable` (the `AddCommGroup` goes through `Classical.choice`), so plain `decide`
and `native_decide` fail — but the point operations do reduce in the *kernel*, so `decide +kernel`
evaluates `n • P = 0` directly. The on-curve points come from `nonsingular_of_equation`: for an
elliptic curve every equation solution is nonsingular (`equation_iff_nonsingular`).

Turning these into a formal proof that `P ∈ E(ℚ)` has infinite order via the certificate is left as
future work: it additionally needs the reduction over the abstract residue field
`IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)` to be identified with the computable
`ZMod p` (Mathlib has `PadicInt.residueField` for `ℤ_[p]`), and the `p`-adic integral model with
its good-reduction and ramification data.
-/

open WeierstrassCurve

/-- For an elliptic curve, every solution of the (affine) Weierstrass equation is nonsingular:
the forward direction of `equation_iff_nonsingular`, with the equation written out. -/
lemma WeierstrassCurve.Affine.nonsingular_of_equation {R : Type*} [CommRing R] [Nontrivial R]
    {W : Affine R} [W.IsElliptic] {x y : R}
    (h : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) :
    W.Nonsingular x y :=
  W.equation_iff_nonsingular.mp ((W.equation_iff x y).mpr h)

namespace InfiniteOrderExample

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-! ### Reduction modulo `3`: `7 • (1, 1) = 0` -/

/-- `y² = x³ - x + 1` over `𝔽₃`. -/
def E3 : WeierstrassCurve (ZMod 3) := ⟨0, 0, 0, -1, 1⟩

instance : E3.IsElliptic := by rw [WeierstrassCurve.isElliptic_iff]; decide

/-- The point `(1, 1)` on `E : y² = x³ - x + 1` over `𝔽₃`. -/
def P3 : E3.toAffine.Point := .some 1 1 (E3.toAffine.nonsingular_of_equation (by grind [E3]))

/-- `P = (1, 1)` reduces modulo `3` to a point of order `7` (so `7 • P₃ = 0`); computed as
`P₃ → 2P₃ = (2,1) → 3P₃ = (0,2) → 4P₃ = (0,1)` and `7 • P₃ = 4P₃ + 3P₃ = 0`. -/
theorem nsmul_seven_eq_zero_mod_three : (7 : ℕ) • P3 = 0 := by
  decide +kernel

/-! ### Reduction modulo `5`: `8 • (1, 1) = 0` -/

/-- `y² = x³ - x + 1` over `𝔽₅`. -/
def E5 : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, -1, 1⟩

instance : E5.IsElliptic := by rw [WeierstrassCurve.isElliptic_iff]; decide

/-- The point `(1, 1)` on `E : y² = x³ - x + 1` over `𝔽₅`. -/
def P5 : E5.toAffine.Point := .some 1 1 (E5.toAffine.nonsingular_of_equation (by grind [E5]))

/-- `P = (1, 1)` reduces modulo `5` to a point of order `8` (so `8 • P₅ = 0`); computed as
`P₅ → 2P₅ = (4,1) → 3P₅ = (0,4) → 4P₅ = (3,0)`, where `4P₅` is `2`-torsion, so
`8 • P₅ = 4P₅ + 4P₅ = 0`. -/
theorem nsmul_eight_eq_zero_mod_five : (8 : ℕ) • P5 = 0 := by
  decide +kernel

/-- The two reduced orders are coprime, so the certificate
`WeierstrassCurve.Affine.not_isOfFinAddOrder_of_coprime_red` would conclude infinite order. -/
theorem coprime_seven_eight : Nat.Coprime 7 8 := by decide

end InfiniteOrderExample

end
