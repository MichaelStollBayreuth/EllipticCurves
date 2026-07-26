module

public import Mathlib
public import EllipticCurves.ReductionAtPrime

@[expose] public section

/-!
# An infinite-order certificate via reduction at two primes

Let `E` be an elliptic curve over the fraction field `K` of a Dedekind domain `R` (e.g. a number
field).  Reduction at a prime `v` of good reduction is injective on the torsion of `E(K)`
provided the residue characteristic `p` is not too ramified (`(p : R) ∈ v.asIdeal` but
`(p : R) ∉ v.asIdeal ^ (p - 1)`, which holds for instance when `p` is odd and `v` is
unramified); this is `WeierstrassCurve.Affine.eq_zero_of_isOfFinAddOrder_of_red_eq_zero`.

This yields a certificate for a point of `E(K)` to have **infinite order**: if the reductions of
a nonzero point at two good primes are torsion of coprime orders, the point cannot be torsion.

Counting points instead of bounding the order of a single reduction gives a certificate for the
whole group `E(K)` to be **torsion-free**: the order of any torsion point divides the number of
points of each such reduction (`WeierstrassCurve.Affine.addOrderOf_dvd_natCard_red`), so it
divides the gcd of finitely many reduction counts; if that gcd is `1`, there is no nonzero
torsion.

## Main statements

* `WeierstrassCurve.Affine.not_isOfFinAddOrder_of_coprime_red`: the two-prime infinite-order
  certificate.
* `WeierstrassCurve.Affine.isAddTorsionFree_of_gcd_natCard_red_eq_one`: `E(K)` is torsion-free
  when the point counts of finitely many good reductions have gcd `1`; with the two-prime
  version `WeierstrassCurve.Affine.isAddTorsionFree_of_coprime_natCard_red`.
-/

open Function IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

/-- An element of an additive monoid annihilated by two coprime multiples is zero. -/
private theorem eq_zero_of_nsmul_eq_zero_of_coprime {A : Type*} [AddMonoid A] {P : A} {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : m • P = 0) (hn : n • P = 0) : P = 0 :=
  AddMonoid.addOrderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes hmn
    (addOrderOf_dvd_of_nsmul_eq_zero hm) (addOrderOf_dvd_of_nsmul_eq_zero hn)

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] [DecidableEq K] [CharZero K] {E : Affine K} [E.IsElliptic]

/-- **Two-prime infinite-order certificate.**  A nonzero point of `E(K)` whose reductions at two
good primes `v`, `w` are torsion of coprime orders (`m • red v hE P = 0`, `n • red w hE' P = 0`
with `m`, `n` coprime) has infinite order.  Here `W₀`, `W₀'` are integral models of `E` over `R`
with good reduction at `v`, `w` respectively, and `p`, `q` are the (lightly ramified) residue
characteristics. -/
theorem not_isOfFinAddOrder_of_coprime_red {v w : HeightOneSpectrum R}
    [DecidableEq (R ⧸ v.asIdeal)] [DecidableEq (R ⧸ w.asIdeal)]
    {W₀ W₀' : WeierstrassCurve R} [(redCurve v W₀).IsElliptic] [(redCurve w W₀').IsElliptic]
    (hE : W₀.map (algebraMap R K) = E) (hE' : W₀'.map (algebraMap R K) = E)
    {P : E.Point} (hP : P ≠ 0)
    {p : ℕ} (hp : p.Prime) (hpmem : (p : R) ∈ v.asIdeal)
    (hpram : (p : R) ∉ v.asIdeal ^ (p - 1))
    {q : ℕ} (hq : q.Prime) (hqmem : (q : R) ∈ w.asIdeal)
    (hqram : (q : R) ∉ w.asIdeal ^ (q - 1))
    {m n : ℕ} (hmn : Nat.Coprime m n)
    (hv : m • red v hE P = 0) (hw : n • red w hE' P = 0) :
    ¬ IsOfFinAddOrder P := fun hfin ↦ hP <|
  eq_zero_of_nsmul_eq_zero_of_coprime hmn
    (nsmul_eq_zero_of_red_nsmul_eq_zero v hE hp hpmem hpram hfin hv)
    (nsmul_eq_zero_of_red_nsmul_eq_zero w hE' hq hqmem hqram hfin hw)

/-- **Torsion-freeness via point counts of good reductions.**  The group `E(K)` is torsion-free
if the numbers of points of finitely many good reductions — at primes `v i` with integral models
`W₀ i` and (lightly ramified) residue characteristics `p i`, as in
`not_isOfFinAddOrder_of_coprime_red` — have greatest common divisor `1`. -/
theorem isAddTorsionFree_of_gcd_natCard_red_eq_one {ι : Type*} {s : Finset ι}
    {v : ι → HeightOneSpectrum R} {W₀ : ι → WeierstrassCurve R}
    (hell : ∀ i ∈ s, (redCurve (v i) (W₀ i)).IsElliptic)
    (hE : ∀ i ∈ s, (W₀ i).map (algebraMap R K) = E)
    {p : ι → ℕ} (hp : ∀ i ∈ s, (p i).Prime)
    (hpmem : ∀ i ∈ s, (p i : R) ∈ (v i).asIdeal)
    (hpram : ∀ i ∈ s, (p i : R) ∉ (v i).asIdeal ^ (p i - 1))
    (hgcd : s.gcd (fun i ↦ Nat.card (redCurve (v i) (W₀ i)).Point) = 1) :
    IsAddTorsionFree E.Point := by
  refine isAddTorsionFree_iff_not_isOfFinAddOrder.mpr fun P hP hfin ↦ hP ?_
  refine AddMonoid.addOrderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one ?_)
  rw [← hgcd]
  refine Finset.dvd_gcd fun i hi ↦ ?_
  classical
  have := hell i hi
  exact addOrderOf_dvd_natCard_red (v i) (hE i hi) (hp i hi) (hpmem i hi) (hpram i hi) hfin

/-- **Torsion-freeness via two point counts**: the group `E(K)` is torsion-free if the numbers
of points of two good reductions (hypotheses as in `not_isOfFinAddOrder_of_coprime_red`) are
coprime. -/
theorem isAddTorsionFree_of_coprime_natCard_red {v w : HeightOneSpectrum R}
    [DecidableEq (R ⧸ v.asIdeal)] [DecidableEq (R ⧸ w.asIdeal)]
    {W₀ W₀' : WeierstrassCurve R} [(redCurve v W₀).IsElliptic] [(redCurve w W₀').IsElliptic]
    (hE : W₀.map (algebraMap R K) = E) (hE' : W₀'.map (algebraMap R K) = E)
    {p : ℕ} (hp : p.Prime) (hpmem : (p : R) ∈ v.asIdeal)
    (hpram : (p : R) ∉ v.asIdeal ^ (p - 1))
    {q : ℕ} (hq : q.Prime) (hqmem : (q : R) ∈ w.asIdeal)
    (hqram : (q : R) ∉ w.asIdeal ^ (q - 1))
    (hmn : Nat.Coprime (Nat.card (redCurve v W₀).Point) (Nat.card (redCurve w W₀').Point)) :
    IsAddTorsionFree E.Point :=
  isAddTorsionFree_iff_not_isOfFinAddOrder.mpr fun _ hP hfin ↦ hP <|
    AddMonoid.addOrderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes hmn
      (addOrderOf_dvd_natCard_red v hE hp hpmem hpram hfin)
      (addOrderOf_dvd_natCard_red w hE' hq hqmem hqram hfin)

end WeierstrassCurve.Affine

end
