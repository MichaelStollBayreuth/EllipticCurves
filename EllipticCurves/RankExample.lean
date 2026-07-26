module

public import Mathlib
public import EllipticCurves.InfiniteOrderExample
public import EllipticCurves.MordellWeil
public import EllipticCurves.SelmerGroup

@[expose] public section

/-!
# Example: the Mordell-Weil group of `y² = x³ - x + 1` over `ℚ` is infinite cyclic

For the elliptic curve `E : y² = x³ - x + 1` over `ℚ`, the cubic `f = x³ - x + 1` is
irreducible with squarefree discriminant `-23`, so `W.discBadPrimes (𝓞 ℚ) = ∅` and the general
bound `WeierstrassCurve.Affine.two_mul_card_selmerGroup₂_le` applies: the cubic field
`ℚ[x]/(f)` (of discriminant `-23`) has trivial class group (via the Minkowski bound) and unit
rank `1` (via Dirichlet, since the discriminant is negative), so the 2-Selmer group of `E`
has order at most `(2 ^ (1 + 1))/2 = 2`.  Since `E(ℚ)` is torsion-free
(`InfiniteOrderExample`), the rank bound `2 ^ rank ≤ #Sel₂` gives `rank E(ℚ) ≤ 1`; being
finitely generated (Mordell-Weil), torsion-free, and nontrivial (it contains `P = (1, 1)`),
the Mordell-Weil group is free of rank exactly one: `E(ℚ) ≅ ℤ`.

## Main statements

* `InfiniteOrderExample.irreducible_f`: `x³ - x + 1` is irreducible over `ℚ` (via reduction
  modulo `2`).
* `InfiniteOrderExample.discBadPrimes_empty`: no finite place imposes an unramifiedness
  restriction beyond the norm condition.
* `InfiniteOrderExample.subsingleton_classGroup`: the cubic field of discriminant `-23` has
  trivial class group (its field discriminant divides `-23`, so the Minkowski bound applies).
* `InfiniteOrderExample.finrank_additive_units`: its unit group has rank `1` (its field
  discriminant is negative, so the signature is `(1, 1)`).
* `InfiniteOrderExample.card_selmerGroup₂_le_two`: the 2-Selmer group of `E` has order at
  most `2`.
* `InfiniteOrderExample.finrank_point_le_one`: the rank of `E(ℚ)` is at most `1`.
* `InfiniteOrderExample.nonempty_point_addEquiv_int`: **`E(ℚ) ≅ ℤ`** — combining the rank
  bound with the Mordell-Weil theorem, torsion-freeness, and the point `(1, 1)`.
-/

open WeierstrassCurve WeierstrassCurve.Affine Polynomial IsDedekindDomain NumberField

namespace InfiniteOrderExample

instance : E.IsCharNeTwoNF := ⟨rfl, rfl⟩

/-! ### The cubic and its discriminant -/

/-- The cubic attached to `E` is `x³ - x + 1`, as a polynomial over `ℤ` base-changed
to `ℚ`. -/
lemma f_eq_map : E.f = (X ^ 3 - X + 1 : ℤ[X]).map (algebraMap ℤ ℚ) := by
  simp only [f, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one, show E.a₂ = 0 from rfl, show E.a₄ = -1 from rfl,
    show E.a₆ = 1 from rfl, map_zero, map_one, Polynomial.C_neg]
  ring

/-- `x³ - x + 1` is irreducible over `ℚ`: it is monic and has no root modulo `2`. -/
lemma irreducible_f : Irreducible E.f := by
  have hmon : (X ^ 3 - X + 1 : ℤ[X]).Monic := by monicity!
  have hmod : ((X ^ 3 - X + 1 : ℤ[X]).map (Int.castRingHom (ZMod 2))) = X ^ 3 + X + 1 := by
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one]
    rw [sub_eq_add_neg, CharTwo.neg_eq]
  have hirr2 : Irreducible ((X ^ 3 - X + 1 : ℤ[X]).map (Int.castRingHom (ZMod 2))) := by
    rw [hmod]
    have hdeg : (X ^ 3 + X + 1 : (ZMod 2)[X]).natDegree = 3 := by compute_degree!
    refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun x ↦ ?_
    · rw [hdeg]; decide
    · fin_cases x <;> simp [IsRoot] <;> decide
  have hirrZ : Irreducible (X ^ 3 - X + 1 : ℤ[X]) :=
    hmon.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2)) _ hirr2
  rw [f_eq_map]
  exact (hmon.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hirrZ

/-- The discriminant of the cubic is `-23`. -/
lemma discr_f_E : E.f.discr = -23 := by
  rw [discr_f, show E.a₂ = 0 from rfl, show E.a₄ = -1 from rfl, show E.a₆ = 1 from rfl]
  norm_num

/-! ### No unramifiedness restrictions: `discBadPrimes (𝓞 ℚ) = ∅` -/

instance : IsPrincipalIdealRing (𝓞 ℚ) :=
  .of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ) Rat.ringOfIntegersEquiv.symm.surjective

/-- `-23` is squarefree in the ring of integers of `ℚ`, being squarefree in `ℤ`. -/
lemma squarefree_neg23 : Squarefree (-23 : 𝓞 ℚ) := by
  have hZ : Squarefree (-23 : ℤ) := Int.squarefree_natAbs.mp <| by
    norm_num
    exact (by norm_num : Nat.Prime 23).squarefree
  intro x hx
  have hdvd : Rat.ringOfIntegersEquiv x * Rat.ringOfIntegersEquiv x ∣ (-23 : ℤ) := by
    rw [← map_mul, show (-23 : ℤ) = Rat.ringOfIntegersEquiv (-23 : 𝓞 ℚ) by
      rw [map_neg, map_ofNat]]
    exact map_dvd _ hx
  have h2 : IsUnit (Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv x)) :=
    (hZ _ hdvd).map Rat.ringOfIntegersEquiv.symm.toRingHom.toMonoidHom
  rwa [RingEquiv.symm_apply_apply] at h2

open WithZero in
/-- No finite place of `ℚ` imposes an unramifiedness restriction on the 2-Selmer group of `E`:
the coefficients are integers and `disc f = -23` is squarefree. -/
lemma discBadPrimes_empty : E.discBadPrimes (𝓞 ℚ) = ∅ := by
  refine E.discBadPrimes_eq_empty (𝓞 ℚ) ?_ ?_ ?_ ?_
  · exact fun v ↦ by rw [show E.a₂ = 0 from rfl, map_zero]; exact zero_le_one
  · exact fun v ↦ by rw [show E.a₄ = -1 from rfl, Valuation.map_neg, map_one]
  · exact fun v ↦ by rw [show E.a₆ = 1 from rfl, map_one]
  · intro v
    rw [discr_f_E, show (-23 : ℚ) = algebraMap (𝓞 ℚ) ℚ (-23) by rw [map_neg, map_ofNat]]
    exact v.exp_neg_one_le_valuation_algebraMap
      (v.notMem_pow_two_of_squarefree squarefree_neg23)

/-! ### The arithmetic of the cubic field of discriminant `-23`

The two inputs are standard facts about the cubic field `L = ℚ[x]/(x³ - x + 1)` (LMFDB label
3.1.23.1): its class group is trivial (via the Minkowski bound) and its unit group has
rank `1` (via Dirichlet, since the discriminant is negative). Both are derived from the key
fact `exists_eq_discr_mul_sq`: the field discriminant times a square is `-23`.
-/

private lemma coe_factors_eq (p : E.f.Factors) : (p : ℚ[X]) = E.f :=
  eq_of_monic_of_associated p.monic E.monic_f
    (p.irreducible.associated_of_dvd irreducible_f p.dvd)

private lemma isIntegral_root (p : E.f.Factors) :
    IsIntegral ℤ (AdjoinRoot.root (p : ℚ[X])) := by
  refine ⟨X ^ 3 - X + 1, by monicity!, ?_⟩
  have h1 : AdjoinRoot.mk (p : ℚ[X]) ((X ^ 3 - X + 1 : ℤ[X]).map (algebraMap ℤ ℚ)) = 0 :=
    (congrArg (AdjoinRoot.mk _) ((coe_factors_eq p).trans f_eq_map)).symm.trans
      AdjoinRoot.mk_self
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one, map_add, map_sub, map_pow, map_one, AdjoinRoot.mk_X] at h1
  simpa only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one] using h1

private lemma finrank_adjoinRoot (p : E.f.Factors) :
    Module.finrank ℚ (AdjoinRoot (p : ℚ[X])) = 3 := by
  rw [(AdjoinRoot.powerBasis p.ne_zero).finrank, AdjoinRoot.powerBasis_dim, coe_factors_eq p,
    natDegree_f]

/-- The discriminant of the cubic field `ℚ[x]/(x³ - x + 1)` times a square is `-23` (in fact
the discriminant *is* `-23`, but divisibility and sign are all that is needed). -/
lemma exists_eq_discr_mul_sq (p : E.f.Factors) :
    ∃ q : ℤ, -23 = NumberField.discr (AdjoinRoot (p : ℚ[X])) * q ^ 2 := by
  have := AdjoinRoot.isSeparable_of_separable E.separable_f p
  have hder : (derivative (p : ℚ[X])).natDegree = (p : ℚ[X]).natDegree - 1 := by
    rw [coe_factors_eq p, natDegree_f, E.derivative_f]
    exact natDegree_quadratic (by norm_num)
  have hdisc := AdjoinRoot.discr_powerBasis_eq_discr (K := ℚ) p.monic hder
  rw [congrArg Polynomial.discr (coe_factors_eq p), discr_f_E] at hdisc
  exact NumberField.exists_eq_discr_mul_sq (AdjoinRoot.powerBasis p.ne_zero)
    (isIntegral_root p) (by exact_mod_cast hdisc)

/-- The ring of integers of the cubic field `ℚ[x]/(x³ - x + 1)` of discriminant `-23` has
trivial class group: the field discriminant divides `-23`, so the Minkowski bound
`(3!/3³)·(4/π)·√23 < 2` shows that every ideal class contains an integral ideal of
norm `1`. -/
theorem subsingleton_classGroup (p : E.f.Factors) :
    Subsingleton (ClassGroup (E.ringOfIntegersFactor (𝓞 ℚ) p)) := by
  refine NumberField.subsingleton_classGroup_integralClosure ℚ _ ?_
  refine RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le
    (finrank_adjoinRoot p) ?_
  obtain ⟨q, hq⟩ := exists_eq_discr_mul_sq p
  have h23 : |NumberField.discr (AdjoinRoot (p : ℚ[X]))| ≤ 23 :=
    Int.le_of_dvd (by norm_num) ((abs_dvd _ _).mpr (dvd_neg.mp ⟨q ^ 2, hq⟩))
  lia

/-- The unit group of the ring of integers of `ℚ[x]/(x³ - x + 1)` has rank `1`: the field
discriminant is negative (it times a square is `-23`), so the field has exactly one real and
one complex place, and Dirichlet's unit theorem gives rank `1 + 1 - 1 = 1`. -/
theorem finrank_additive_units (p : E.f.Factors) :
    Module.finrank ℤ (Additive (E.ringOfIntegersFactor (𝓞 ℚ) p)ˣ) = 1 := by
  obtain ⟨q, hq⟩ := exists_eq_discr_mul_sq p
  have hneg : NumberField.discr (AdjoinRoot (p : ℚ[X])) < 0 := by nlinarith [sq_nonneg q]
  exact (NumberField.finrank_additive_units_integralClosure ℚ _).trans
    (RingOfIntegers.finrank_additive_units_of_discr_neg (finrank_adjoinRoot p) hneg)

instance (p : E.f.Factors) : Group.FG (E.ringOfIntegersFactor (𝓞 ℚ) p)ˣ :=
  NumberField.fg_units_integralClosure ℚ (AdjoinRoot (p : ℚ[X]))

/-! ### The Selmer group bound and the rank bound -/

/-- `-1` is not a square in `ℚ`. -/
lemma not_isSquare_neg_one : ¬ IsSquare (-1 : ℚ) := by
  rintro ⟨r, hr⟩
  nlinarith [mul_self_nonneg r]

/-- **The 2-Selmer group of `E : y² = x³ - x + 1` over `ℚ` has order at most `2`.** -/
theorem card_selmerGroup₂_le_two :
    Nat.card (E.selmerGroup₂ (𝓞 ℚ) (fun v : InfinitePlace ℚ ↦ v.Completion)) ≤ 2 := by
  have : Unique E.f.Factors := Polynomial.Factors.unique irreducible_f E.monic_f
  have : ∀ p : E.f.Factors, Subsingleton (ClassGroup (E.ringOfIntegersFactor (𝓞 ℚ) p)) :=
    subsingleton_classGroup
  have h := E.two_mul_card_selmerGroup₂_le discBadPrimes_empty not_isSquare_neg_one
  rw [Fintype.prod_unique, finrank_additive_units] at h
  lia

/-- **The rank of `E(ℚ)` is at most `1`**: combine the Selmer
bound with `2 ^ rank ∣ #(im μ) ≤ #Sel₂` and the torsion-freeness of `E(ℚ)`. -/
theorem finrank_point_le_one : Module.finrank ℤ E.Point ≤ 1 := by
  have : Unique E.f.Factors := Polynomial.Factors.unique irreducible_f E.monic_f
  have : ∀ p : E.f.Factors, Subsingleton (ClassGroup (E.ringOfIntegersFactor (𝓞 ℚ) p)) :=
    subsingleton_classGroup
  have (p : E.f.Factors) : Finite (ClassGroup (E.ringOfIntegersFactor (𝓞 ℚ) p)) :=
    Finite.of_subsingleton
  have hfg : AddGroup.FG E.Point := fg_point_of_numberField
  have hfin : Finite (E.selmerGroup₂ (𝓞 ℚ) (fun v : InfinitePlace ℚ ↦ v.Completion)) :=
    E.finite_selmerGroup₂
  have h := E.pow_rank_le_card_of_range_μ_le (E.range_μ_le_selmerGroup₂ (𝓞 ℚ)
    (fun v : InfinitePlace ℚ ↦ v.Completion))
  rw [AddMonoidHom.ker_nsmulAddMonoidHom two_ne_zero, AddSubgroup.card_bot, mul_one] at h
  have h2 := h.trans card_selmerGroup₂_le_two
  exact (Nat.pow_le_pow_iff_right one_lt_two).mp (h2.trans_eq (pow_one 2).symm)

/-- **The Mordell-Weil group of `y² = x³ - x + 1` over `ℚ` is infinite cyclic**: `E(ℚ)` is
finitely generated (the Mordell-Weil theorem), torsion-free, nontrivial (it contains
`P = (1, 1)`), and of rank at most `1`, hence free of rank exactly `1`. -/
theorem nonempty_point_addEquiv_int : Nonempty (E.Point ≃+ ℤ) := by
  have : AddGroup.FG E.Point := fg_point_of_numberField
  have : Nontrivial E.Point := nontrivial_of_ne P 0 (Point.some_ne_zero _)
  exact AddCommGroup.nonempty_addEquiv_int_of_finrank_le_one finrank_point_le_one

end InfiniteOrderExample

end
