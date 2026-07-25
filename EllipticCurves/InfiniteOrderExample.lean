module

public import Mathlib
public import EllipticCurves.InfiniteOrder

@[expose] public section

/-!
# Example: `(1, 1)` on `y² = x³ - x + 1` has infinite order

The point `P = (1, 1)` on the elliptic curve `E : y² = x³ - x + 1` over `ℚ` has infinite order.
A certificate is that its reductions at two primes have coprime orders: modulo `3` the reduced
point is killed by `7` (indeed `#E(𝔽₃) = 7`) and modulo `5` it is killed by `8` (`#E(𝔽₅) = 8`),
and `gcd(7, 8) = 1`. This is exactly the input to
`WeierstrassCurve.Affine.not_isOfFinAddOrder_of_coprime_red`, instantiated at `R = ℤ`, `K = ℚ`
and the height-one primes `(3)` and `(5)` of `ℤ`.

## Main statements

* `InfiniteOrderExample.nsmul_seven_eq_zero_mod_three`, `.nsmul_eight_eq_zero_mod_five`: the two
  finite-field torsion facts, over `ZMod 3` and `ZMod 5`.
* `InfiniteOrderExample.not_isOfFinAddOrder_P`: the point `P = (1, 1)` of `E(ℚ)` has infinite
  order.

## Implementation notes

The two torsion facts are closed by `decide +kernel`. Mathlib's `WeierstrassCurve.Affine.Point`
addition is `noncomputable` (the `AddCommGroup` goes through `Classical.choice`), so plain `decide`
and `native_decide` fail — but the point operations do reduce in the *kernel*, so `decide +kernel`
evaluates `n • P = 0` directly. The on-curve points come from `nonsingular_of_equation`: for an
elliptic curve every equation solution is nonsingular (`equation_iff_nonsingular`).

The reduction maps at `(3)` and `(5)` take values in the point groups over the residue fields
`ℤ ⧸ (p)`; the torsion facts are transported there from the computable `ZMod p` along the ring
isomorphism `Int.quotientSpanNatEquivZMod` (via `Point.map` and `Point.congr`).
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

open WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

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
`WeierstrassCurve.Affine.not_isOfFinAddOrder_of_coprime_red` applies. -/
theorem coprime_seven_eight : Nat.Coprime 7 8 := by decide

/-! ### The curve over `ℚ`, its integral model, and the primes `(3)` and `(5)` -/

/-- `y² = x³ - x + 1` as an integral model over `ℤ`. -/
def W₀ : WeierstrassCurve ℤ := ⟨0, 0, 0, -1, 1⟩

/-- `y² = x³ - x + 1` over `ℚ`. -/
def E : Affine ℚ := ⟨0, 0, 0, -1, 1⟩

lemma map_W₀ : W₀.map (algebraMap ℤ ℚ) = E := by
  ext <;> simp [W₀, E]

lemma Δ_W₀ : W₀.Δ = -368 := by
  norm_num [W₀, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : E.IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero, ← map_W₀, map_Δ, Δ_W₀]
  norm_num

/-- The point `P = (1, 1)` on `E : y² = x³ - x + 1` over `ℚ`. -/
def P : E.Point := .some 1 1 (E.nonsingular_of_equation (by norm_num [E]))

/-- The height-one prime `(p)` of `ℤ` attached to a prime number `p`. -/
def intPrime (p : ℕ) [Fact p.Prime] : HeightOneSpectrum ℤ :=
  .ofPrime (p := Ideal.span {(p : ℤ)})
    (Ideal.prime_span_singleton_iff.mpr (Nat.prime_iff_prime_int.mp Fact.out))

@[simp] lemma intPrime_asIdeal (p : ℕ) [Fact p.Prime] :
    (intPrime p).asIdeal = Ideal.span {(p : ℤ)} := rfl

instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℤ ⧸ (intPrime p).asIdeal) :=
  (Int.quotientSpanNatEquivZMod p).toEquiv.decidableEq

variable {p : ℕ} [Fact p.Prime]

/-- `W₀` has good reduction at any prime not dividing its discriminant. -/
lemma isElliptic_redCurve (h : ¬ (p : ℤ) ∣ W₀.Δ) : (redCurve (intPrime p) W₀).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  change (W₀.map (algebraMap ℤ (ℤ ⧸ (intPrime p).asIdeal))).Δ ≠ 0
  rwa [Ne, map_Δ, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
    intPrime_asIdeal, Ideal.mem_span_singleton]

instance : (redCurve (intPrime 3) W₀).IsElliptic := isElliptic_redCurve (by norm_num [Δ_W₀])

instance : (redCurve (intPrime 5) W₀).IsElliptic := isElliptic_redCurve (by norm_num [Δ_W₀])

/-! ### Transport of the torsion facts from `ZMod p` -/

/-- The residue field `ℤ ⧸ (p)` of `intPrime p` compared with `ZMod p`, as a `ℤ`-algebra map. -/
private noncomputable def residueZModAlgHom (p : ℕ) [Fact p.Prime] :
    (ℤ ⧸ (intPrime p).asIdeal) →ₐ[ℤ] ZMod p :=
  (Int.quotientSpanNatEquivZMod p : ℤ ⧸ Ideal.span {(p : ℤ)} →+* ZMod p).toIntAlgHom

variable {W' : Affine (ZMod p)}
  (hW' : ((W₀.toAffine ⁄ (ZMod p)) : WeierstrassCurve _).toAffine = W')

/-- Transport of points of the reduced curve modulo `p` to a concrete curve over `ZMod p`. -/
private noncomputable def resPoint : (redCurve (intPrime p) W₀).Point →+ W'.Point :=
  (Point.congr hW').toAddMonoidHom.comp (Point.map (W' := W₀.toAffine) (residueZModAlgHom p))

private lemma resPoint_injective : Function.Injective (resPoint hW') := fun _ _ h ↦
  Point.map_injective (residueZModAlgHom p) ((Point.congr hW').injective h)

private lemma resPoint_red_P [(redCurve (intPrime p) W₀).IsElliptic]
    (h1 : W'.Nonsingular 1 1) :
    resPoint hW' (red (intPrime p) map_W₀ P) = .some 1 1 h1 := by
  have hone (hx : (1 : ℚ) ∈ ((intPrime p).valuation ℚ).integer) :
      (intPrime p).residueHom ⟨1, hx⟩ = 1 := map_one _
  simp only [P]
  rw [red_some_of_le _ map_W₀ (le_of_eq (map_one _)), resPoint, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, Point.map_some, Point.congr_some, Point.some.injEq, hone]
  exact ⟨map_one _, map_one _⟩

include hW' in
/-- The reduction of `P` at `p` is killed by any `n` killing the corresponding point over
`ZMod p`. -/
private lemma nsmul_red_P_eq_zero [(redCurve (intPrime p) W₀).IsElliptic]
    {h1 : W'.Nonsingular 1 1} {n : ℕ} (hn : n • Point.some 1 1 h1 = 0) :
    n • red (intPrime p) map_W₀ P = 0 :=
  resPoint_injective hW' <| by rw [map_nsmul, resPoint_red_P hW' h1, hn, map_zero]

private lemma baseChange_zmod_three :
    ((W₀.toAffine ⁄ (ZMod 3)) : WeierstrassCurve _).toAffine = E3.toAffine := by
  ext <;> decide +kernel

private lemma baseChange_zmod_five :
    ((W₀.toAffine ⁄ (ZMod 5)) : WeierstrassCurve _).toAffine = E5.toAffine := by
  ext <;> decide +kernel

/-! ### The conclusion -/

/-- **The point `(1, 1)` on `y² = x³ - x + 1` over `ℚ` has infinite order.** -/
theorem not_isOfFinAddOrder_P : ¬ IsOfFinAddOrder P :=
  not_isOfFinAddOrder_of_coprime_red map_W₀ map_W₀ (Point.some_ne_zero _)
    (by norm_num) (Ideal.mem_span_singleton_self _)
    (by rw [intPrime_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]; norm_num)
    (by norm_num) (Ideal.mem_span_singleton_self _)
    (by rw [intPrime_asIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]; norm_num)
    coprime_seven_eight
    (nsmul_red_P_eq_zero baseChange_zmod_three nsmul_seven_eq_zero_mod_three)
    (nsmul_red_P_eq_zero baseChange_zmod_five nsmul_eight_eq_zero_mod_five)

end InfiniteOrderExample

end
