module

public import EllipticCurves.Mathlib.WeierstrassFormalGroup.ThirdPoint
import all EllipticCurves.Mathlib.WeierstrassFormalGroup.ThirdPoint
import all EllipticCurves.Mathlib.WeierstrassFormalGroup.Chord

/-!
# The formal group law of a Weierstrass curve

Over the fraction field of a domain, the addition series realizes the group law of the curve
`(t, w(t))` (the `Domain` and `Assembly` sections); the universal curve over
`ℤ[A₁, …, A₆]⟦…⟧` then yields associativity (`Universal`). Assembling all the axioms gives
`WeierstrassCurve.formalGroupLaw`, the one-dimensional `ChabautyColeman.FormalGroupLaw` of the
curve, together with the inverse property `subst_inverseSeries_addSeries`.
-/

@[expose] public section

open ChabautyColeman PowerSeries IsDedekindDomain

namespace WeierstrassCurve

section wSeries

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O)

section Chord

open MvPowerSeries

section OnLine

variable {σ : Type*}

section Domain

variable [IsDomain O]

private lemma X_inl_ne_X_inr :
    (MvPowerSeries.X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit) O) ≠
      MvPowerSeries.X (Sum.inr ()) := by
  intro h
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl ()) 1)) h
  simp [MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff] at h1

set_option maxRecDepth 4000 in
/-- Vieta: the chord value at the third root satisfies the Weierstrass equation there. -/
private lemma line_at_thirdRoot :
    W.slopeSeries * W.thirdRootSeries + W.interceptSeries =
      W.mvWStepAt W.thirdRootSeries
        (W.slopeSeries * W.thirdRootSeries + W.interceptSeries) := by
  have hC1 : W.slopeSeries * MvPowerSeries.X (Sum.inl ()) + W.interceptSeries =
      W.mvWStepAt (MvPowerSeries.X (Sum.inl ()))
        (W.slopeSeries * MvPowerSeries.X (Sum.inl ()) + W.interceptSeries) := by
    rw [W.line_left]
    exact W.wsAt_rename _
  have hC2 : W.slopeSeries * MvPowerSeries.X (Sum.inr ()) + W.interceptSeries =
      W.mvWStepAt (MvPowerSeries.X (Sum.inr ()))
        (W.slopeSeries * MvPowerSeries.X (Sum.inr ()) + W.interceptSeries) := by
    rw [W.line_right]
    exact W.wsAt_rename _
  have hAd : (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
      MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 + MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) *
      MvPowerSeries.invOfUnit (1 + MvPowerSeries.C W.a₂ * W.slopeSeries +
        MvPowerSeries.C W.a₄ * W.slopeSeries ^ 2 +
        MvPowerSeries.C W.a₆ * W.slopeSeries ^ 3) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ 1 (by simp)
  simp only [mvWStepAt, thirdRootSeries] at hC1 ⊢
  set Λ := W.slopeSeries
  set N := W.interceptSeries
  set t₁ := (MvPowerSeries.X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit) O)
  set t₂ := (MvPowerSeries.X (Sum.inr ()) : MvPowerSeries (Unit ⊕ Unit) O)
  set d := MvPowerSeries.invOfUnit (1 + MvPowerSeries.C W.a₂ * Λ +
    MvPowerSeries.C W.a₄ * Λ ^ 2 + MvPowerSeries.C W.a₆ * Λ ^ 3) 1
  -- extract the linear coefficient of the chord cubic by cancelling `t₁ - t₂`
  have hsub : (t₁ - t₂) * (-(1 + MvPowerSeries.C W.a₂ * Λ + MvPowerSeries.C W.a₄ * Λ ^ 2 +
      MvPowerSeries.C W.a₆ * Λ ^ 3) * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) -
      (MvPowerSeries.C W.a₁ * Λ + MvPowerSeries.C W.a₂ * N + MvPowerSeries.C W.a₃ * Λ ^ 2 +
        2 * MvPowerSeries.C W.a₄ * Λ * N + 3 * MvPowerSeries.C W.a₆ * Λ ^ 2 * N) *
        (t₁ + t₂) +
      (Λ - (MvPowerSeries.C W.a₁ * N + 2 * MvPowerSeries.C W.a₃ * Λ * N +
        MvPowerSeries.C W.a₄ * N ^ 2 + 3 * MvPowerSeries.C W.a₆ * Λ * N ^ 2))) = 0 := by
    simp only [mvWStepAt] at hC1 hC2
    linear_combination hC1 - hC2
  have hE1 := (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr X_inl_ne_X_inr)
  clear_value Λ N t₁ t₂ d
  set B := MvPowerSeries.C W.a₁ * Λ + MvPowerSeries.C W.a₂ * N + MvPowerSeries.C W.a₃ * Λ ^ 2 +
    2 * MvPowerSeries.C W.a₄ * Λ * N + 3 * MvPowerSeries.C W.a₆ * Λ ^ 2 * N with hB
  set T := -t₁ - t₂ - B * d with hT
  clear_value B T
  linear_combination hC1 + (T - t₁) * hE1 + ((T - t₁) * (T - t₂) * B) * hAd -
    ((T - t₁) * (T - t₂) * (1 + MvPowerSeries.C W.a₂ * Λ + MvPowerSeries.C W.a₄ * Λ ^ 2 +
      MvPowerSeries.C W.a₆ * Λ ^ 3)) * hT + (T ^ 2 - t₁ ^ 2) * hB

/-- The third intersection point lies on the chord:
`w(t₃(t₁, t₂)) = λ(t₁, t₂)·t₃(t₁, t₂) + ν(t₁, t₂)`. -/
theorem subst_thirdRootSeries_wSeries :
    MvPowerSeries.subst (fun _ : Unit ↦ W.thirdRootSeries) W.wSeries =
      W.slopeSeries * W.thirdRootSeries + W.interceptSeries := by
  have hfix : MvPowerSeries.subst (fun _ : Unit ↦ W.thirdRootSeries) W.wSeries =
      W.mvWStepAt W.thirdRootSeries
        (MvPowerSeries.subst (fun _ : Unit ↦ W.thirdRootSeries) W.wSeries) := by
    conv_lhs => rw [W.wSeries_eq_wStep]
    rw [show W.wStep W.wSeries = W.wStepAt X W.wSeries from rfl]
    rw [wStepAt, ← MvPowerSeries.coe_substAlgHom W.hasSubst_thirdRootSeries]
    simp only [map_add, map_mul, map_pow]
    rw [MvPowerSeries.coe_substAlgHom W.hasSubst_thirdRootSeries]
    simp only [show (PowerSeries.C : O →+* O⟦X⟧) = MvPowerSeries.C from rfl,
      show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl,
      MvPowerSeries.subst_C, MvPowerSeries.subst_X W.hasSubst_thirdRootSeries, mvWStepAt]
  refine W.eq_of_mvWStepAt_fixed (q := W.thirdRootSeries)
    (lowVanish_one W.constantCoeff_thirdRootSeries) ?_ ?_ hfix W.line_at_thirdRoot
  · exact lowVanish_one (MvPowerSeries.constantCoeff_subst_eq_zero W.hasSubst_thirdRootSeries
      (fun _ ↦ W.constantCoeff_thirdRootSeries) W.constantCoeff_wSeries)
  · exact lowVanish_one (by simp)

/-- The on-line identity, along a parameter pair. -/
private lemma pair_online {σ' : Type*} {q₁ q₂ : MvPowerSeries σ' O}
    (h₁ : MvPowerSeries.constantCoeff q₁ = 0) (h₂ : MvPowerSeries.constantCoeff q₂ = 0) :
    MvPowerSeries.subst (fun _ : Unit ↦
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries)
        W.wSeries =
      MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.slopeSeries *
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries +
        MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.interceptSeries := by
  have h := congrArg (MvPowerSeries.substAlgHom (hasSubst_pair h₁ h₂))
    W.subst_thirdRootSeries_wSeries
  simp only [map_add, map_mul] at h
  simp only [MvPowerSeries.coe_substAlgHom (hasSubst_pair h₁ h₂)] at h
  rwa [MvPowerSeries.subst_comp_subst_apply W.hasSubst_thirdRootSeries
    (hasSubst_pair h₁ h₂)] at h

variable {σ' : Type*}

/-- `w` composed with a nonzero parameter is nonzero (over a domain). -/
private lemma subst_wSeries_ne_zero {q : MvPowerSeries σ' O}
    (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries ≠ 0 := by
  have hs := hasSubst_single hq
  have hexp : MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries =
      q ^ 3 * MvPowerSeries.subst (fun _ : Unit ↦ q) W.vSeries := by
    conv_lhs => rw [W.wSeries_eq_X_pow_three_mul]
    rw [← MvPowerSeries.coe_substAlgHom hs, map_mul, map_pow,
      MvPowerSeries.coe_substAlgHom hs,
      show (PowerSeries.X : PowerSeries O) = MvPowerSeries.X () from rfl,
      MvPowerSeries.subst_X hs]
  rw [hexp]
  refine mul_ne_zero (pow_ne_zero 3 hq0) fun h ↦ ?_
  have hc := congrArg MvPowerSeries.constantCoeff h
  rw [map_zero, MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ (0 : Unit →₀ ℕ)
    (fun d hd ↦ ?_)] at hc
  · rw [show MvPowerSeries.coeff (0 : Unit →₀ ℕ) W.vSeries =
      PowerSeries.constantCoeff W.vSeries from rfl, W.constantCoeff_vSeries] at hc
    simp at hc
  · rcases Finsupp.ne_iff.mp hd with ⟨u, hu⟩
    have hu' : d u ≠ 0 := by simpa using hu
    rw [smul_eq_mul, Finsupp.prod, map_prod]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hu') ?_)
    rw [map_pow, hq, zero_pow hu']

/-- The intercept series does not vanish: its coefficient at `t₁²t₂` is `-1`. -/
private lemma interceptSeries_ne_zero : W.interceptSeries ≠ 0 := by
  intro h
  have h1 := congrArg (MvPowerSeries.coeff
    (Finsupp.single (Sum.inl ()) 2 + Finsupp.single (Sum.inr ()) 1)) h
  rw [map_zero, interceptSeries, map_sub, coeff_rename_single,
    if_neg (by rw [eq_single_iff']; simp),
    show (MvPowerSeries.X (Sum.inl ()) : MvPowerSeries (Unit ⊕ Unit) O) =
      MvPowerSeries.monomial (Finsupp.single (Sum.inl ()) 1) 1 from rfl,
    MvPowerSeries.coeff_mul_monomial, if_pos (by
      refine Finsupp.le_def.mpr fun s ↦ ?_
      rcases s with u | u <;> simp),
    W.coeff_slopeSeries] at h1
  have h2 : ((Finsupp.single (Sum.inl ()) 2 + Finsupp.single (Sum.inr ()) 1 -
      Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ)) (Sum.inl ()) = 1 := by
    simp
  have h3 : ((Finsupp.single (Sum.inl ()) 2 + Finsupp.single (Sum.inr ()) 1 -
      Finsupp.single (Sum.inl ()) 1 : Unit ⊕ Unit →₀ ℕ)) (Sum.inr ()) = 1 := by
    simp
  rw [h2, h3, W.coeff_wSeries_three, mul_one] at h1
  simp at h1

private lemma X_pair_intercept_ne_zero {σ' : Type*} {s₁ s₂ : σ'} (h : s₁ ≠ s₂) :
    MvPowerSeries.subst
      (Sum.elim (fun _ ↦ (MvPowerSeries.X s₁ : MvPowerSeries σ' O)) fun _ ↦ MvPowerSeries.X s₂)
      W.interceptSeries ≠ 0 := by
  rw [subst_pair_X_eq_rename]
  intro h0
  refine W.interceptSeries_ne_zero (MvPowerSeries.rename_injective
    (⟨Sum.elim (fun _ ↦ s₁) fun _ ↦ s₂, ?_⟩ : Unit ⊕ Unit ↪ σ') ?_)
  · rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) hv
    · rfl
    · exact absurd hv h
    · exact absurd hv.symm h
    · rfl
  · rw [map_zero]
    exact h0

/-- Over a domain, if `ι ≠ X`, the intercept of the chord through a point and its formal
inverse vanishes. -/
private lemma pair_X_inverse_intercept_eq_zero
    (hne : W.inverseSeries ≠ (MvPowerSeries.X () : MvPowerSeries Unit O)) :
    MvPowerSeries.subst
        (Sum.elim (fun _ ↦ (MvPowerSeries.X () : MvPowerSeries Unit O)) fun _ ↦ W.inverseSeries)
        W.interceptSeries = 0 :=
  (mul_eq_zero.mp W.pair_X_inverse_intercept_mul).resolve_right (sub_ne_zero.mpr hne)

/-- Over a domain with `2 ≠ 0` and `ι ≠ X`: the third root of the chord through a point
and its formal inverse is `0` (the third intersection point is the point at infinity). -/
private lemma pair_X_inverse_thirdRoot_eq_zero
    (hne : W.inverseSeries ≠ (MvPowerSeries.X () : MvPowerSeries Unit O))
    (h2 : (2 : O) ≠ 0) :
    MvPowerSeries.subst
        (Sum.elim (fun _ ↦ (MvPowerSeries.X () : MvPowerSeries Unit O)) fun _ ↦ W.inverseSeries)
        W.thirdRootSeries = 0 := by
  have h₁ : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit O) = 0 :=
    MvPowerSeries.constantCoeff_X ()
  have h₂ : MvPowerSeries.constantCoeff (W.inverseSeries : MvPowerSeries Unit O) = 0 :=
    W.constantCoeff_inverseSeries
  have hNp := W.pair_X_inverse_intercept_eq_zero hne
  have hOL := W.pair_online h₁ h₂
  have hTc := W.pair_thirdRoot_constantCoeff h₁ h₂
  have hfix := W.subst_wSeries_fix hTc
  have hrel := W.pair_T₃_relation h₁ h₂
  have hslope := W.pair_slope_identity h₁ h₂
  have hidw : MvPowerSeries.subst (fun _ : Unit ↦ (MvPowerSeries.X () : MvPowerSeries Unit O))
      W.wSeries = W.wSeries := congrFun MvPowerSeries.subst_self _
  have hw : MvPowerSeries.subst (fun _ : Unit ↦ (W.inverseSeries : MvPowerSeries Unit O))
      W.wSeries = -(W.wSeries * PowerSeries.invOfUnit W.uSeries 1) := by
    rw [show MvPowerSeries.subst (fun _ : Unit ↦ (W.inverseSeries : MvPowerSeries Unit O))
        W.wSeries = PowerSeries.subst W.inverseSeries W.wSeries from rfl,
      W.subst_inverseSeries_wSeries]
  rw [hidw, hw] at hslope
  simp only [mvWStepAt] at hfix
  set d := PowerSeries.invOfUnit W.uSeries 1 with hddef
  set Λp := MvPowerSeries.subst
    (Sum.elim (fun _ ↦ (MvPowerSeries.X () : MvPowerSeries Unit O)) fun _ ↦ W.inverseSeries)
    W.slopeSeries
  set Tp := MvPowerSeries.subst
    (Sum.elim (fun _ ↦ (MvPowerSeries.X () : MvPowerSeries Unit O)) fun _ ↦ W.inverseSeries)
    W.thirdRootSeries
  set wT := MvPowerSeries.subst (fun _ : Unit ↦ Tp) W.wSeries
  rw [hNp, add_zero] at hOL
  -- the cubic in `Tp` with the line substituted in factors through `Tp`
  have hTP : Tp * (Λp - Tp ^ 2 - MvPowerSeries.C W.a₁ * Λp * Tp -
      MvPowerSeries.C W.a₂ * Λp * Tp ^ 2 - MvPowerSeries.C W.a₃ * Λp ^ 2 * Tp -
      MvPowerSeries.C W.a₄ * Λp ^ 2 * Tp ^ 2 - MvPowerSeries.C W.a₆ * Λp ^ 3 * Tp ^ 2) = 0 := by
    linear_combination hfix - (1 - MvPowerSeries.C W.a₁ * Tp - MvPowerSeries.C W.a₂ * Tp ^ 2 -
      MvPowerSeries.C W.a₃ * (Λp * Tp + wT) - MvPowerSeries.C W.a₄ * Tp * (Λp * Tp + wT) -
      MvPowerSeries.C W.a₆ * (Λp ^ 2 * Tp ^ 2 + Λp * Tp * wT + wT ^ 2)) * hOL
  refine (mul_eq_zero.mp hTP).resolve_right fun hbranch ↦ ?_
  -- in the second branch, `Λp = -A·Tp·(X + ι)`, contradicting `w·(d + 1)` having order 3
  rw [hNp] at hrel
  have hcontr : W.wSeries * (d + 1) =
      (1 + MvPowerSeries.C W.a₂ * Λp + MvPowerSeries.C W.a₄ * Λp ^ 2 +
        MvPowerSeries.C W.a₆ * Λp ^ 3) * Tp *
        (MvPowerSeries.X () + W.inverseSeries) * (W.inverseSeries - MvPowerSeries.X ()) := by
    linear_combination hslope - (W.inverseSeries - MvPowerSeries.X ()) * hbranch -
      (W.inverseSeries - MvPowerSeries.X ()) * Tp * hrel
  have hd : W.inverseSeries =
      -(MvPowerSeries.X () * d) := rfl
  have hdvd : (MvPowerSeries.X () : MvPowerSeries Unit O) ^ 4 ∣
      (1 + MvPowerSeries.C W.a₂ * Λp + MvPowerSeries.C W.a₄ * Λp ^ 2 +
        MvPowerSeries.C W.a₆ * Λp ^ 3) * Tp *
        (MvPowerSeries.X () + W.inverseSeries) * (W.inverseSeries - MvPowerSeries.X ()) := by
    have d1 : (MvPowerSeries.X () : MvPowerSeries Unit O) ∣ Tp :=
      PowerSeries.X_dvd_iff.mpr hTc
    have d2 : (MvPowerSeries.X () : MvPowerSeries Unit O) ^ 2 ∣
        (MvPowerSeries.X () + W.inverseSeries) := by
      have h1d : (MvPowerSeries.X () : MvPowerSeries Unit O) ∣ (1 - d) :=
        PowerSeries.X_dvd_iff.mpr (by simp [hddef])
      obtain ⟨c, hc⟩ := h1d
      exact ⟨c, by rw [hd]; linear_combination MvPowerSeries.X () * hc⟩
    have d3 : (MvPowerSeries.X () : MvPowerSeries Unit O) ∣
        (W.inverseSeries - MvPowerSeries.X ()) :=
      PowerSeries.X_dvd_iff.mpr
        (by simp [show (MvPowerSeries.X () : MvPowerSeries Unit O) = PowerSeries.X from rfl])
    rw [show (MvPowerSeries.X () : MvPowerSeries Unit O) ^ 4 =
      MvPowerSeries.X () * MvPowerSeries.X () ^ 2 * MvPowerSeries.X () by ring]
    exact mul_dvd_mul (mul_dvd_mul (Dvd.dvd.mul_left d1 _) d2) d3
  have h3 := congrArg (PowerSeries.coeff 3) hcontr
  rw [PowerSeries.X_pow_dvd_iff.mp hdvd 3 (by lia), W.wSeries_eq_X_pow_three_mul,
    mul_assoc, show (3 : ℕ) = 0 + 3 from rfl, PowerSeries.coeff_X_pow_mul] at h3
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, W.constantCoeff_vSeries,
    map_add, map_one, one_mul, hddef, PowerSeries.constantCoeff_invOfUnit] at h3
  simp only [inv_one, Units.val_one] at h3
  exact h2 (by linear_combination h3)

/-- Over a domain with `2 ≠ 0` and `ι ≠ X`: the addition series vanishes at the pair
`(t, ι(t))` — the formal inverse property. -/
private lemma pair_X_inverse_addSeries_eq_zero
    (hne : W.inverseSeries ≠ (MvPowerSeries.X () : MvPowerSeries Unit O))
    (h2 : (2 : O) ≠ 0) :
    MvPowerSeries.subst
        (Sum.elim (fun _ ↦ (MvPowerSeries.X () : MvPowerSeries Unit O)) fun _ ↦ W.inverseSeries)
        W.addSeries = 0 := by
  rw [W.pair_F_eq (MvPowerSeries.constantCoeff_X ()) W.constantCoeff_inverseSeries,
    W.pair_X_inverse_thirdRoot_eq_zero hne h2, zero_mul, neg_zero]

end Domain

section Assembly

/-! ### Assembly: the addition series realizes the group law over the fraction field -/

variable {σ' : Type*} {KK : Type*} [Field KK] [Algebra (MvPowerSeries σ' O) KK]

/-- The base-changed curve over the fraction field of the series ring. -/
private noncomputable def fracCurve (W : WeierstrassCurve O) (σ' : Type*) (KK : Type*)
    [Field KK] [Algebra (MvPowerSeries σ' O) KK] : WeierstrassCurve KK :=
  W.map ((algebraMap (MvPowerSeries σ' O) KK).comp MvPowerSeries.C)

private lemma rho_weierstrass {q : MvPowerSeries σ' O}
    (hq : MvPowerSeries.constantCoeff q = 0) :
    algebraMap (MvPowerSeries σ' O) KK
        (MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries) =
      algebraMap (MvPowerSeries σ' O) KK q ^ 3 +
        (fracCurve W σ' KK).a₁ * algebraMap (MvPowerSeries σ' O) KK q *
          algebraMap (MvPowerSeries σ' O) KK
            (MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries) +
        (fracCurve W σ' KK).a₂ * algebraMap (MvPowerSeries σ' O) KK q ^ 2 *
          algebraMap (MvPowerSeries σ' O) KK
            (MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries) +
        (fracCurve W σ' KK).a₃ * algebraMap (MvPowerSeries σ' O) KK
            (MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries) ^ 2 +
        (fracCurve W σ' KK).a₄ * algebraMap (MvPowerSeries σ' O) KK q *
          algebraMap (MvPowerSeries σ' O) KK
            (MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries) ^ 2 +
        (fracCurve W σ' KK).a₆ * algebraMap (MvPowerSeries σ' O) KK
            (MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries) ^ 3 := by
  have h := congrArg (algebraMap (MvPowerSeries σ' O) KK) (W.subst_wSeries_fix hq)
  simp only [mvWStepAt, map_add, map_mul, map_pow] at h
  exact h

variable [IsDomain O] [IsFractionRing (MvPowerSeries σ' O) KK]

/-- The point of the base-changed curve with parameter `q`. -/
private noncomputable def thetaPoint
    (hΔ : (fracCurve W σ' KK).Δ ≠ 0) {q : MvPowerSeries σ' O}
    (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0) :
    (fracCurve W σ' KK).toAffine.Point :=
  Affine.Point.some _ _ (chord_point_nonsingular (fracCurve W σ' KK)
    (W.rho_weierstrass hq)
    (fun h ↦ W.subst_wSeries_ne_zero hq hq0 ((IsFractionRing.injective (MvPowerSeries σ' O) KK)
      (by rw [h, map_zero])))
    hΔ)

variable [DecidableEq KK] in
/-- The chord addition of parametrized points: `θ(q₁) + θ(q₂) = θ(F(q₁, q₂))`. -/
private lemma thetaPoint_add (hΔ : (fracCurve W σ' KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ' O}
    (h₁ : MvPowerSeries.constantCoeff q₁ = 0) (h₂ : MvPowerSeries.constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0) (hq₁₂ : q₁ ≠ q₂)
    (hN : MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.interceptSeries ≠ 0)
    (hF : MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.addSeries) = 0)
    (hF0 : MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.addSeries ≠ 0) :
    W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 = W.thetaPoint hΔ hF hF0 := by
  classical
  set ρ := algebraMap (MvPowerSeries σ' O) KK with hρ
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ' O) KK
  set Λp := MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.slopeSeries with hΛp
  set Np := MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.interceptSeries with hNp
  set Tp := MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.thirdRootSeries with hTp
  set w₁ := MvPowerSeries.subst (fun _ : Unit ↦ q₁) W.wSeries with hw₁'
  set w₂ := MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.wSeries with hw₂'
  set wT := MvPowerSeries.subst (fun _ : Unit ↦ Tp) W.wSeries with hwT'
  -- the six chord hypotheses, transported to the fraction field
  have hslope : ρ Λp * (ρ q₂ - ρ q₁) = ρ w₂ - ρ w₁ := by
    rw [← map_sub, ← map_sub, ← map_mul]
    exact congrArg ρ (W.pair_slope_identity h₁ h₂)
  have hNint : ρ Np = ρ w₁ - ρ Λp * ρ q₁ := by
    rw [← map_mul, ← map_sub]
    exact congrArg ρ (W.pair_intercept_identity₁ h₁ h₂)
  have hT₃ : (1 + (fracCurve W σ' KK).a₂ * ρ Λp + (fracCurve W σ' KK).a₄ * ρ Λp ^ 2 +
      (fracCurve W σ' KK).a₆ * ρ Λp ^ 3) * (ρ Tp + ρ q₁ + ρ q₂) =
      -((fracCurve W σ' KK).a₁ * ρ Λp + (fracCurve W σ' KK).a₂ * ρ Np +
        (fracCurve W σ' KK).a₃ * ρ Λp ^ 2 +
        2 * (fracCurve W σ' KK).a₄ * ρ Λp * ρ Np +
        3 * (fracCurve W σ' KK).a₆ * ρ Λp ^ 2 * ρ Np) := by
    have h := congrArg ρ (W.pair_T₃_relation h₁ h₂)
    simp only [map_add, map_mul, map_neg, map_pow, map_one, map_ofNat] at h
    exact h
  have hwT : ρ wT = ρ Λp * ρ Tp + ρ Np := by
    have h := congrArg ρ (W.pair_online h₁ h₂)
    simp only [map_add, map_mul] at h
    exact h
  have hA : (1 + (fracCurve W σ' KK).a₂ * ρ Λp + (fracCurve W σ' KK).a₄ * ρ Λp ^ 2 +
      (fracCurve W σ' KK).a₆ * ρ Λp ^ 3) ≠ 0 := by
    intro h
    have h0 : ρ (1 + MvPowerSeries.C W.a₂ * Λp + MvPowerSeries.C W.a₄ * Λp ^ 2 +
        MvPowerSeries.C W.a₆ * Λp ^ 3) = 0 := by
      simp only [map_add, map_mul, map_pow, map_one]
      exact h
    have h1 : (1 : MvPowerSeries σ' O) + MvPowerSeries.C W.a₂ * Λp +
        MvPowerSeries.C W.a₄ * Λp ^ 2 + MvPowerSeries.C W.a₆ * Λp ^ 3 = 0 :=
      hinj (by rw [h0, map_zero])
    have h2 := congrArg MvPowerSeries.constantCoeff h1
    have hΛ0 : MvPowerSeries.constantCoeff Λp = 0 :=
      MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair h₁ h₂)
        (by rintro (j | j) <;> simpa) W.constantCoeff_slopeSeries
    simp [hΛ0] at h2
  have hTp0 : Tp ≠ 0 := by
    intro h
    apply hN
    have honline := W.pair_online h₁ h₂
    rw [← hTp, h] at honline
    rw [show (fun _ : Unit ↦ (0 : MvPowerSeries σ' O)) = 0 from rfl,
      MvPowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_wSeries] at honline
    rw [← hNp, ← hΛp] at honline
    linear_combination -honline
  have hw₁0 : ρ w₁ ≠ 0 := fun h ↦ W.subst_wSeries_ne_zero h₁ hq₁0 (hinj (by rw [h, map_zero]))
  have hw₂0 : ρ w₂ ≠ 0 := fun h ↦ W.subst_wSeries_ne_zero h₂ hq₂0 (hinj (by rw [h, map_zero]))
  have hTc : MvPowerSeries.constantCoeff Tp = 0 := W.pair_thirdRoot_constantCoeff h₁ h₂
  have hwT0 : ρ wT ≠ 0 := fun h ↦ W.subst_wSeries_ne_zero hTc hTp0 (hinj (by rw [h, map_zero]))
  have hqw : q₁ * w₂ - q₂ * w₁ = Np * (q₁ - q₂) := by
    have i₁ := W.pair_intercept_identity₁ h₁ h₂
    have i₂ := W.pair_intercept_identity₂ h₁ h₂
    rw [← hNp, ← hΛp, ← hw₁'] at i₁
    rw [← hNp, ← hΛp, ← hw₂'] at i₂
    linear_combination q₂ * i₁ - q₁ * i₂
  have hx : ρ q₁ * ρ w₂ - ρ q₂ * ρ w₁ ≠ 0 := by
    rw [← map_mul, ← map_mul, ← map_sub]
    intro h
    have := hinj (by rw [h, map_zero] : ρ (q₁ * w₂ - q₂ * w₁) = ρ 0)
    rw [hqw] at this
    exact (mul_ne_zero hN (sub_ne_zero.mpr hq₁₂)) this
  -- the Weierstrass equations
  have hwq₁ := W.rho_weierstrass (KK := KK) h₁
  have hwq₂ := W.rho_weierstrass (KK := KK) h₂
  -- apply the point-level chord lemma
  obtain ⟨h₃, hadd⟩ := chord_point_add (fracCurve W σ' KK) hwq₁ hwq₂ hslope hNint hT₃ hwT hA
    hw₁0 hw₂0 hwT0 hx
    (chord_point_nonsingular (fracCurve W σ' KK) hwq₁ hw₁0 hΔ)
    (chord_point_nonsingular (fracCurve W σ' KK) hwq₂ hw₂0 hΔ)
  refine Eq.trans (show W.thetaPoint hΔ h₁ hq₁0 + W.thetaPoint hΔ h₂ hq₂0 =
    Affine.Point.some _ _ h₃ from hadd) ?_
  -- identify the sum with the point of parameter `F(q₁, q₂)`
  set sp := MvPowerSeries.subst (fun _ : Unit ↦ Tp)
    (PowerSeries.invOfUnit W.uSeries 1) with hsp'
  have hu : ρ (MvPowerSeries.subst (fun _ : Unit ↦ Tp) W.uSeries) * ρ sp = 1 := by
    rw [← map_mul, ← map_one ρ]
    exact congrArg ρ (W.pair_u_mul h₁ h₂)
  have hueq : ρ (MvPowerSeries.subst (fun _ : Unit ↦ Tp) W.uSeries) =
      1 - (fracCurve W σ' KK).a₁ * ρ Tp - (fracCurve W σ' KK).a₃ * ρ wT := by
    have h := congrArg ρ (W.pair_u_eq h₁ h₂)
    simp only [map_sub, map_mul, map_one] at h
    exact h
  have hsp0 : ρ sp ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact one_ne_zero hu.symm
  have hFeq : ρ (MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.addSeries) =
      -(ρ Tp * ρ sp) := by
    have h := congrArg ρ (W.pair_F_eq h₁ h₂)
    simp only [map_neg, map_mul] at h
    exact h
  have hwFeq : ρ (MvPowerSeries.subst (fun _ : Unit ↦
      MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.addSeries) W.wSeries) =
      -(ρ wT * ρ sp) := by
    have h := congrArg ρ (W.pair_wF h₁ h₂)
    simp only [map_neg, map_mul] at h
    exact h
  rw [thetaPoint]
  simp only [Affine.Point.some.injEq]
  constructor
  · rw [hFeq, hwFeq]
    field_simp
  · rw [hwFeq, div_eq_div_iff hwT0 (neg_ne_zero.mpr (mul_ne_zero hwT0 hsp0))]
    linear_combination (-(ρ wT)) * hu + (ρ wT * ρ sp) * hueq



/-- The parametrized point of `ι ∘ q` is the negative of the parametrized point of `q`. -/
private lemma thetaPoint_neg (hΔ : (fracCurve W σ' KK).Δ ≠ 0)
    {q : MvPowerSeries σ' O} (hq : MvPowerSeries.constantCoeff q = 0) (hq0 : q ≠ 0)
    (hi : MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun _ : Unit ↦ q) W.inverseSeries) = 0)
    (hi0 : MvPowerSeries.subst (fun _ : Unit ↦ q) W.inverseSeries ≠ 0) :
    W.thetaPoint hΔ hi hi0 = -W.thetaPoint hΔ hq hq0 := by
  classical
  set ρ := algebraMap (MvPowerSeries σ' O) KK with hρ
  have hu : ρ (MvPowerSeries.subst (fun _ : Unit ↦ q) W.uSeries) *
      ρ (MvPowerSeries.subst (fun _ : Unit ↦ q) (PowerSeries.invOfUnit W.uSeries 1)) = 1 := by
    rw [← map_mul, ← map_one ρ]
    exact congrArg ρ (W.single_u_mul hq)
  have hsp0 : ρ (MvPowerSeries.subst (fun _ : Unit ↦ q)
      (PowerSeries.invOfUnit W.uSeries 1)) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hu
    exact one_ne_zero hu.symm
  have hIeq : ρ (MvPowerSeries.subst (fun _ : Unit ↦ q) W.inverseSeries) =
      -(ρ q * ρ (MvPowerSeries.subst (fun _ : Unit ↦ q)
        (PowerSeries.invOfUnit W.uSeries 1))) := by
    have h := congrArg ρ (W.single_iota_eq hq)
    simpa only [map_neg, map_mul] using h
  have hwIeq : ρ (MvPowerSeries.subst (fun _ : Unit ↦
      MvPowerSeries.subst (fun _ : Unit ↦ q) W.inverseSeries) W.wSeries) =
      -(ρ (MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries) *
        ρ (MvPowerSeries.subst (fun _ : Unit ↦ q)
          (PowerSeries.invOfUnit W.uSeries 1))) := by
    have h := congrArg ρ (W.single_wIota hq)
    simpa only [map_neg, map_mul] using h
  have hueq : ρ (MvPowerSeries.subst (fun _ : Unit ↦ q) W.uSeries) =
      1 - (fracCurve W σ' KK).a₁ * ρ q -
        (fracCurve W σ' KK).a₃ * ρ (MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries) := by
    have h := congrArg ρ (W.single_u_eq hq)
    simp only [map_sub, map_mul, map_one] at h
    exact h
  have hw0 : ρ (MvPowerSeries.subst (fun _ : Unit ↦ q) W.wSeries) ≠ 0 := fun h ↦
    W.subst_wSeries_ne_zero hq hq0
      ((IsFractionRing.injective (MvPowerSeries σ' O) KK) (by rw [h, map_zero]))
  simp only [thetaPoint, Affine.Point.neg_some, Affine.Point.some.injEq]
  simp only [← hρ]
  constructor
  · rw [hIeq, hwIeq]
    field_simp
  · rw [hwIeq, Affine.negY]
    field_simp
    linear_combination
      ρ (MvPowerSeries.subst (fun _ : Unit ↦ q) (PowerSeries.invOfUnit W.uSeries 1)) * hueq -
      hu

/-- The parametrized point determines the parameter. -/
private lemma thetaPoint_inj (hΔ : (fracCurve W σ' KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ' O}
    (h₁ : MvPowerSeries.constantCoeff q₁ = 0) (h₂ : MvPowerSeries.constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0)
    (h : W.thetaPoint hΔ h₁ hq₁0 = W.thetaPoint hΔ h₂ hq₂0) : q₁ = q₂ := by
  classical
  set ρ := algebraMap (MvPowerSeries σ' O) KK with hρ
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ' O) KK
  simp only [thetaPoint, Affine.Point.some.injEq] at h
  simp only [← hρ] at h
  have hw₁0 : ρ (MvPowerSeries.subst (fun _ : Unit ↦ q₁) W.wSeries) ≠ 0 := fun hh ↦
    W.subst_wSeries_ne_zero h₁ hq₁0 (hinj (by rw [hh, map_zero]))
  have hw₂0 : ρ (MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.wSeries) ≠ 0 := fun hh ↦
    W.subst_wSeries_ne_zero h₂ hq₂0 (hinj (by rw [hh, map_zero]))
  have hw : ρ (MvPowerSeries.subst (fun _ : Unit ↦ q₁) W.wSeries) =
      ρ (MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.wSeries) := by
    have h2 := h.2
    field_simp at h2
    linear_combination h2
  refine hinj ?_
  have h1 := h.1
  rw [div_eq_div_iff hw₁0 hw₂0, hw] at h1
  exact mul_right_cancel₀ hw₂0 h1

/-- The pair intercept is nonzero as soon as the two parameters are distinct and not
mutually inverse: otherwise the two parametrized points would have equal `x`-coordinates. -/
private lemma pair_intercept_ne_zero_of_ne (hΔ : (fracCurve W σ' KK).Δ ≠ 0)
    {q₁ q₂ : MvPowerSeries σ' O}
    (h₁ : MvPowerSeries.constantCoeff q₁ = 0) (h₂ : MvPowerSeries.constantCoeff q₂ = 0)
    (hq₁0 : q₁ ≠ 0) (hq₂0 : q₂ ≠ 0) (hne₁ : q₁ ≠ q₂)
    (hne₂ : q₁ ≠ MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.inverseSeries) :
    MvPowerSeries.subst (Sum.elim (fun _ ↦ q₁) (fun _ ↦ q₂)) W.interceptSeries ≠ 0 := by
  classical
  intro h0
  set ρ := algebraMap (MvPowerSeries σ' O) KK with hρ
  have hinj : Function.Injective ρ := IsFractionRing.injective (MvPowerSeries σ' O) KK
  -- equal x-coordinates
  have hqw : q₁ * MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.wSeries -
      q₂ * MvPowerSeries.subst (fun _ : Unit ↦ q₁) W.wSeries = 0 := by
    have i₁ := W.pair_intercept_identity₁ h₁ h₂
    have i₂ := W.pair_intercept_identity₂ h₁ h₂
    rw [h0] at i₁ i₂
    linear_combination q₂ * i₁ - q₁ * i₂
  have hw₁0 : ρ (MvPowerSeries.subst (fun _ : Unit ↦ q₁) W.wSeries) ≠ 0 := fun hh ↦
    W.subst_wSeries_ne_zero h₁ hq₁0 (hinj (by rw [hh, map_zero]))
  have hw₂0 : ρ (MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.wSeries) ≠ 0 := fun hh ↦
    W.subst_wSeries_ne_zero h₂ hq₂0 (hinj (by rw [hh, map_zero]))
  have hx : ρ q₁ / ρ (MvPowerSeries.subst (fun _ : Unit ↦ q₁) W.wSeries) =
      ρ q₂ / ρ (MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.wSeries) := by
    rw [div_eq_div_iff hw₁0 hw₂0, ← map_mul, ← map_mul]
    exact congrArg ρ (by linear_combination hqw)
  -- hence the points agree up to sign
  have hcase := (Affine.Point.X_eq_iff
    (h₁ := (chord_point_nonsingular (fracCurve W σ' KK) (W.rho_weierstrass h₁) hw₁0 hΔ))
    (h₂ := (chord_point_nonsingular (fracCurve W σ' KK) (W.rho_weierstrass h₂) hw₂0 hΔ))).mp hx
  -- data for `ι ∘ q₂`
  have hs0 : MvPowerSeries.subst (fun _ : Unit ↦ q₂)
      (PowerSeries.invOfUnit W.uSeries 1) ≠ 0 := by
    intro hh
    have := W.single_u_mul h₂
    rw [hh, mul_zero] at this
    exact one_ne_zero this.symm
  have hi : MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.inverseSeries) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_single h₂) (fun _ ↦ h₂)
      W.constantCoeff_inverseSeries
  have hi0 : MvPowerSeries.subst (fun _ : Unit ↦ q₂) W.inverseSeries ≠ 0 := by
    rw [W.single_iota_eq h₂]
    exact neg_ne_zero.mpr (mul_ne_zero hq₂0 hs0)
  rcases hcase with hc | hc
  · exact hne₁ (W.thetaPoint_inj hΔ h₁ h₂ hq₁0 hq₂0 hc)
  · have hc' : W.thetaPoint hΔ h₁ hq₁0 = -W.thetaPoint hΔ h₂ hq₂0 := hc
    rw [← W.thetaPoint_neg hΔ h₂ hq₂0 hi hi0] at hc'
    exact hne₂ (W.thetaPoint_inj hΔ h₁ hi hq₁0 hi0 hc')

end Assembly

section Universal

/-- The universal Weierstrass curve, over `ℤ[A₁, A₂, A₃, A₄, A₆]`. -/
noncomputable def universal : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

/-- Every Weierstrass curve is a base change of the universal one. -/
theorem exists_map_universal (W : WeierstrassCurve O) :
    ∃ φ : MvPolynomial (Fin 5) ℤ →+* O, universal.map φ = W := by
  refine ⟨(MvPolynomial.aeval ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]).toRingHom, ?_⟩
  ext <;> simp [universal, WeierstrassCurve.map]

private lemma universal_Δ_ne_zero : universal.Δ ≠ 0 := by
  intro h
  have h2 := congrArg (MvPolynomial.aeval (R := ℤ) ![0, 0, 0, -1, 0]).toRingHom h
  rw [map_zero, ← WeierstrassCurve.map_Δ] at h2
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, universal, WeierstrassCurve.map] at h2
  revert h2
  decide

/-- Associativity of the addition series for the universal Weierstrass curve.

This is the remaining core: it is proved by identifying the addition series with the group
law of the (elliptic, since `Δ ≠ 0`) curve over the fraction field of
`ℤ[A₁, …, A₆]⟦t₁, t₂, t₃⟧`. -/
private lemma X_ne_X {σ'' : Type*} {O' : Type*} [CommRing O'] [Nontrivial O'] {s t : σ''}
    (h : s ≠ t) : (MvPowerSeries.X s : MvPowerSeries σ'' O') ≠ MvPowerSeries.X t := by
  classical
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single s 1)) h0
  simp [MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff, h] at h1

private lemma X_ne_zero' {σ'' : Type*} {O' : Type*} [CommRing O'] [Nontrivial O'] (s : σ'') :
    (MvPowerSeries.X s : MvPowerSeries σ'' O') ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single s 1)) h0
  simp [MvPowerSeries.coeff_X] at h1

theorem assoc_addSeries_universal :
    MvPowerSeries.subst (assocLeftFam (fun _ : Unit ↦ universal.addSeries))
      universal.addSeries =
    MvPowerSeries.subst (assocRightFam (fun _ : Unit ↦ universal.addSeries))
      universal.addSeries := by
  classical
  set KK := FractionRing (MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ))
    with hKK
  -- the discriminant of the base-changed universal curve does not vanish
  have hΔ : (fracCurve universal (Unit ⊕ Unit ⊕ Unit) KK).Δ ≠ 0 := by
    rw [fracCurve, WeierstrassCurve.map_Δ]
    intro h
    exact universal_Δ_ne_zero (MvPowerSeries.C_injective
      (IsFractionRing.injective (MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ))
        KK (by rw [RingHom.comp_apply] at h; simp [h])))
  -- the three coordinate parameters
  have hc₁ : MvPowerSeries.constantCoeff (MvPowerSeries.X (Sum.inl ()) :
      MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ)) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have hc₂ : MvPowerSeries.constantCoeff (MvPowerSeries.X (Sum.inr (Sum.inl ())) :
      MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ)) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have hc₃ : MvPowerSeries.constantCoeff (MvPowerSeries.X (Sum.inr (Sum.inr ())) :
      MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ)) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have h10 := X_ne_zero' (O' := MvPolynomial (Fin 5) ℤ) (Sum.inl () : Unit ⊕ Unit ⊕ Unit)
  have h20 := X_ne_zero' (O' := MvPolynomial (Fin 5) ℤ)
    (Sum.inr (Sum.inl ()) : Unit ⊕ Unit ⊕ Unit)
  have h30 := X_ne_zero' (O' := MvPolynomial (Fin 5) ℤ)
    (Sum.inr (Sum.inr ()) : Unit ⊕ Unit ⊕ Unit)
  -- the two inner sums
  set F₁₂ := MvPowerSeries.subst (Sum.elim (fun _ ↦ (MvPowerSeries.X (Sum.inl ()) :
      MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ)))
      (fun _ ↦ MvPowerSeries.X (Sum.inr (Sum.inl ())))) universal.addSeries with hF₁₂'
  set F₂₃ := MvPowerSeries.subst (Sum.elim (fun _ ↦ (MvPowerSeries.X (Sum.inr (Sum.inl ())) :
      MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ)))
      (fun _ ↦ MvPowerSeries.X (Sum.inr (Sum.inr ())))) universal.addSeries with hF₂₃'
  have hF₁₂c : MvPowerSeries.constantCoeff F₁₂ = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair hc₁ hc₂)
      (by rintro (j | j) <;> simp [MvPowerSeries.constantCoeff_X])
      universal.constantCoeff_addSeries
  have hF₂₃c : MvPowerSeries.constantCoeff F₂₃ = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair hc₂ hc₃)
      (by rintro (j | j) <;> simp [MvPowerSeries.constantCoeff_X])
      universal.constantCoeff_addSeries
  -- the evaluation `u₁ ↦ X, u₂ ↦ 0, u₃ ↦ 0`
  have hχ : MvPowerSeries.HasSubst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0) : Unit ⊕ Unit ⊕ Unit →
      MvPowerSeries Unit (MvPolynomial (Fin 5) ℤ)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by
      rintro (j | j)
      · exact PowerSeries.constantCoeff_X
      · simp)
  -- `χ`-evaluations: `F₁₂ ↦ X`, `F₂₃ ↦ 0`, third-variable compositions with `ι ↦ 0`
  have hχF₁₂ : MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0)) F₁₂ = PowerSeries.X := by
    rw [hF₁₂', MvPowerSeries.subst_comp_subst_apply (hasSubst_pair hc₁ hc₂) hχ,
      show (fun s : Unit ⊕ Unit ↦ MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X :
          PowerSeries (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))
          (Sum.elim (fun _ ↦ (MvPowerSeries.X (Sum.inl ()) :
            MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ)))
            (fun _ ↦ MvPowerSeries.X (Sum.inr (Sum.inl ()))) s)) =
        (Sum.elim MvPowerSeries.X (fun _ ↦ 0) :
          Unit ⊕ Unit → MvPowerSeries Unit (MvPolynomial (Fin 5) ℤ)) from funext fun s ↦ by
        rcases s with u | u <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
          rw [MvPowerSeries.subst_X hχ] <;> rfl]
    exact universal.subst_unitR_addSeries
  have hχF₂₃ : MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0)) F₂₃ = 0 := by
    rw [hF₂₃', MvPowerSeries.subst_comp_subst_apply (hasSubst_pair hc₂ hc₃) hχ,
      show (fun s : Unit ⊕ Unit ↦ MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X :
          PowerSeries (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))
          (Sum.elim (fun _ ↦ (MvPowerSeries.X (Sum.inr (Sum.inl ())) :
            MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ)))
            (fun _ ↦ MvPowerSeries.X (Sum.inr (Sum.inr ()))) s)) =
        (0 : Unit ⊕ Unit → MvPowerSeries Unit (MvPolynomial (Fin 5) ℤ)) from funext fun s ↦ by
        rcases s with u | u <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
          rw [MvPowerSeries.subst_X hχ] <;> rfl]
    exact MvPowerSeries.subst_zero_of_constantCoeff_zero universal.constantCoeff_addSeries
  -- generic: `χ` of `ι` composed with anything `χ`-null is `0`
  have hχι : ∀ q : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ),
      MvPowerSeries.constantCoeff q = 0 →
      MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
        (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0)) q = 0 →
      MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
        (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))
        (MvPowerSeries.subst (fun _ : Unit ↦ q) universal.inverseSeries) = 0 := by
    intro q hqc hq0
    rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_single hqc) hχ,
      show (fun _ : Unit ↦ MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X :
          PowerSeries (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0)) q) =
        (0 : Unit → MvPowerSeries Unit (MvPolynomial (Fin 5) ℤ)) from funext fun _ ↦ hq0]
    exact MvPowerSeries.subst_zero_of_constantCoeff_zero universal.constantCoeff_inverseSeries
  have hχu₃ : MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))
      (MvPowerSeries.X (Sum.inr (Sum.inr ())) :
        MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ)) = 0 := by
    rw [MvPowerSeries.subst_X hχ]
    rfl
  have hχu₁ : MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))
      (MvPowerSeries.X (Sum.inl ()) :
        MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ)) = PowerSeries.X := by
    rw [MvPowerSeries.subst_X hχ]
    rfl
  -- the nonvanishing and distinctness facts via `χ`
  have hXPS : (PowerSeries.X : PowerSeries (MvPolynomial (Fin 5) ℤ)) ≠ 0 := by
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp at h1
  have hF₁₂0 : F₁₂ ≠ 0 := by
    intro h
    rw [h, ← MvPowerSeries.coe_substAlgHom hχ, map_zero] at hχF₁₂
    exact hXPS hχF₁₂.symm
  have hFne : universal.addSeries ≠ 0 := by
    intro h
    have h2 := universal.subst_unitR_addSeries
    rw [h, ← MvPowerSeries.coe_substAlgHom hasSubst_unitR, map_zero] at h2
    exact hXPS h2.symm
  have hF₂₃0 : F₂₃ ≠ 0 := by
    rw [hF₂₃', subst_pair_X_eq_rename]
    intro h
    refine hFne (MvPowerSeries.rename_injective (⟨Sum.elim (fun _ ↦ Sum.inr (Sum.inl ()))
      (fun _ ↦ Sum.inr (Sum.inr ())), ?_⟩ : Unit ⊕ Unit ↪ Unit ⊕ Unit ⊕ Unit) ?_)
    · rintro (⟨⟩ | ⟨⟩) (⟨⟩ | ⟨⟩) hv
      · rfl
      · exact absurd hv (by simp)
      · exact absurd hv (by simp)
      · rfl
    · rw [map_zero]
      exact h
  -- distinctness via `χ`
  have hne_a : F₁₂ ≠ MvPowerSeries.X (Sum.inr (Sum.inr ())) := by
    intro h
    have h2 := congrArg (MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))) h
    rw [hχF₁₂, hχu₃] at h2
    exact hXPS h2
  have hne_b : F₁₂ ≠ MvPowerSeries.subst (fun _ : Unit ↦ (MvPowerSeries.X (Sum.inr (Sum.inr ()))
      : MvPowerSeries (Unit ⊕ Unit ⊕ Unit) (MvPolynomial (Fin 5) ℤ)))
      universal.inverseSeries := by
    intro h
    have h2 := congrArg (MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))) h
    rw [hχF₁₂, hχι _ hc₃ hχu₃] at h2
    exact hXPS h2
  have hne_c : MvPowerSeries.X (Sum.inl ()) ≠ F₂₃ := by
    intro h
    have h2 := congrArg (MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))) h
    rw [hχu₁, hχF₂₃] at h2
    exact hXPS h2
  have hne_d : MvPowerSeries.X (Sum.inl ()) ≠ MvPowerSeries.subst (fun _ : Unit ↦ F₂₃)
      universal.inverseSeries := by
    intro h
    have h2 := congrArg (MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))) h
    rw [hχu₁, hχι _ hF₂₃c hχF₂₃] at h2
    exact hXPS h2
  -- the four nonvanishing intercepts
  have hN₁₂ := universal.X_pair_intercept_ne_zero
    (s₁ := (Sum.inl () : Unit ⊕ Unit ⊕ Unit)) (s₂ := Sum.inr (Sum.inl ())) (by simp)
  have hN₂₃ := universal.X_pair_intercept_ne_zero
    (s₁ := (Sum.inr (Sum.inl ()) : Unit ⊕ Unit ⊕ Unit)) (s₂ := Sum.inr (Sum.inr ()))
    (by simp)
  have hNL := universal.pair_intercept_ne_zero_of_ne (KK := KK) hΔ hF₁₂c hc₃ hF₁₂0 h30
    hne_a hne_b
  have hNR := universal.pair_intercept_ne_zero_of_ne (KK := KK) hΔ hc₁ hF₂₃c h10 hF₂₃0
    hne_c hne_d
  -- constants and nonvanishing of the two full sums
  have hLc : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      (Sum.elim (fun _ ↦ F₁₂) (fun _ ↦ MvPowerSeries.X (Sum.inr (Sum.inr ()))))
      universal.addSeries) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair hF₁₂c hc₃)
      (by rintro (j | j) <;> simp [hF₁₂c, MvPowerSeries.constantCoeff_X])
      universal.constantCoeff_addSeries
  have hRc : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      (Sum.elim (fun _ ↦ MvPowerSeries.X (Sum.inl ())) (fun _ ↦ F₂₃))
      universal.addSeries) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair hc₁ hF₂₃c)
      (by rintro (j | j) <;> simp [hF₂₃c, MvPowerSeries.constantCoeff_X])
      universal.constantCoeff_addSeries
  have hL0 : MvPowerSeries.subst
      (Sum.elim (fun _ ↦ F₁₂) (fun _ ↦ MvPowerSeries.X (Sum.inr (Sum.inr ()))))
      universal.addSeries ≠ 0 := by
    intro h
    have h2 := congrArg (MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))) h
    rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pair hF₁₂c hc₃) hχ,
      show (fun s : Unit ⊕ Unit ↦ MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X :
          PowerSeries (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))
          (Sum.elim (fun _ ↦ F₁₂) (fun _ ↦ MvPowerSeries.X (Sum.inr (Sum.inr ()))) s)) =
        (Sum.elim MvPowerSeries.X (fun _ ↦ 0) :
          Unit ⊕ Unit → MvPowerSeries Unit (MvPolynomial (Fin 5) ℤ)) from funext fun s ↦ by
        rcases s with u | u
        · simp only [Sum.elim_inl]
          exact hχF₁₂
        · simp only [Sum.elim_inr]
          exact hχu₃,
      universal.subst_unitR_addSeries, ← MvPowerSeries.coe_substAlgHom hχ, map_zero] at h2
    exact hXPS h2
  have hR0 : MvPowerSeries.subst
      (Sum.elim (fun _ ↦ MvPowerSeries.X (Sum.inl ())) (fun _ ↦ F₂₃))
      universal.addSeries ≠ 0 := by
    intro h
    have h2 := congrArg (MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X : PowerSeries
      (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))) h
    rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_pair hc₁ hF₂₃c) hχ,
      show (fun s : Unit ⊕ Unit ↦ MvPowerSeries.subst (Sum.elim (fun _ ↦ (PowerSeries.X :
          PowerSeries (MvPolynomial (Fin 5) ℤ))) (fun _ ↦ 0))
          (Sum.elim (fun _ ↦ MvPowerSeries.X (Sum.inl ())) (fun _ ↦ F₂₃) s)) =
        (Sum.elim MvPowerSeries.X (fun _ ↦ 0) :
          Unit ⊕ Unit → MvPowerSeries Unit (MvPolynomial (Fin 5) ℤ)) from funext fun s ↦ by
        rcases s with u | u
        · simp only [Sum.elim_inl]
          exact hχu₁
        · simp only [Sum.elim_inr]
          exact hχF₂₃,
      universal.subst_unitR_addSeries, ← MvPowerSeries.coe_substAlgHom hχ, map_zero] at h2
    exact hXPS h2
  -- the θ-chain
  have e₁₂ := universal.thetaPoint_add (KK := KK) hΔ hc₁ hc₂ h10 h20
    (X_ne_X (by simp)) hN₁₂ hF₁₂c hF₁₂0
  have e₂₃ := universal.thetaPoint_add (KK := KK) hΔ hc₂ hc₃ h20 h30
    (X_ne_X (by simp)) hN₂₃ hF₂₃c hF₂₃0
  have eL := universal.thetaPoint_add (KK := KK) hΔ hF₁₂c hc₃ hF₁₂0 h30 hne_a hNL hLc hL0
  have eR := universal.thetaPoint_add (KK := KK) hΔ hc₁ hF₂₃c h10 hF₂₃0 hne_c hNR hRc hR0
  have hpts : universal.thetaPoint hΔ hLc hL0 = universal.thetaPoint hΔ hRc hR0 := by
    rw [← eL, ← e₁₂, ← eR, ← e₂₃, add_assoc]
  have hkey := universal.thetaPoint_inj hΔ hLc hRc hL0 hR0 hpts
  exact hkey

/-- Associativity of the addition series, for any Weierstrass curve, by reduction to the
universal one. -/
theorem assoc_addSeries (W : WeierstrassCurve O) :
    MvPowerSeries.subst (assocLeftFam (fun _ : Unit ↦ W.addSeries)) W.addSeries =
      MvPowerSeries.subst (assocRightFam (fun _ : Unit ↦ W.addSeries)) W.addSeries := by
  obtain ⟨φ, rfl⟩ := exists_map_universal W
  have h := congrArg (MvPowerSeries.map φ) assoc_addSeries_universal
  rw [MvPowerSeries.map_subst universal.hasSubst_assocLeftFam_addSeries,
    MvPowerSeries.map_subst universal.hasSubst_assocRightFam_addSeries,
    universal.map_assocLeftFam_addSeries φ, universal.map_assocRightFam_addSeries φ,
    universal.map_addSeries φ] at h
  exact h

private lemma universal_inverseSeries_ne_X :
    universal.inverseSeries ≠
      (MvPowerSeries.X () : MvPowerSeries Unit (MvPolynomial (Fin 5) ℤ)) := by
  intro h
  have h1 := congrArg (PowerSeries.coeff 1) h
  rw [show universal.inverseSeries =
      -(PowerSeries.X * PowerSeries.invOfUnit universal.uSeries 1) from rfl, map_neg,
    show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit,
    show (MvPowerSeries.X () : MvPowerSeries Unit (MvPolynomial (Fin 5) ℤ)) = PowerSeries.X
      from rfl, PowerSeries.coeff_one_X, inv_one, Units.val_one] at h1
  have h2 := congrArg (MvPolynomial.eval (0 : Fin 5 → ℤ)) h1
  rw [map_neg, map_one] at h2
  exact absurd h2 (by decide)

/-- The formal inverse property `F(t, ι(t)) = 0`: the addition series vanishes along the
pair `(t, ι(t))`, for any Weierstrass curve — proved for the universal curve via the chord
geometry (the chord through a point and its inverse has intercept `0`, so its third root
is `0` by Vieta) and transported by naturality. -/
theorem subst_inverseSeries_addSeries (W : WeierstrassCurve O) :
    MvPowerSeries.subst
        (Sum.elim (fun _ ↦ (MvPowerSeries.X () : MvPowerSeries Unit O)) fun _ ↦ W.inverseSeries)
        W.addSeries = 0 := by
  obtain ⟨φ, rfl⟩ := exists_map_universal W
  have h := congrArg (MvPowerSeries.map φ) (universal.pair_X_inverse_addSeries_eq_zero
    universal_inverseSeries_ne_X (by norm_num))
  rw [map_zero, MvPowerSeries.map_subst (hasSubst_pair (MvPowerSeries.constantCoeff_X ())
    universal.constantCoeff_inverseSeries), universal.map_addSeries φ] at h
  rw [show (fun s ↦ MvPowerSeries.map φ ((Sum.elim (fun _ ↦ (MvPowerSeries.X () :
      MvPowerSeries Unit (MvPolynomial (Fin 5) ℤ))) fun _ ↦ universal.inverseSeries) s)) =
      Sum.elim (fun _ ↦ (MvPowerSeries.X () : MvPowerSeries Unit O))
        fun _ ↦ (universal.map φ).inverseSeries from funext fun s ↦ by
      rcases s with u | u
      · exact MvPowerSeries.map_X φ ()
      · exact universal.map_inverseSeries φ] at h
  exact h

end Universal

end OnLine

end Chord

/-- The formal group law of a Weierstrass curve: the power series `F(t₁, t₂)` giving the
`t`-coordinate of the sum of the points with parameters `t₁`, `t₂` on the curve
`(t, w(t))`, via the chord construction (Silverman, IV.1.1). One-dimensional, so the index
type is `Unit`. Associativity is proved via the group law of the universal curve over the
fraction field of `ℤ[A₁, …, A₆]⟦t₁, t₂, t₃⟧`. -/
noncomputable def formalGroupLaw (W : WeierstrassCurve O) : FormalGroupLaw O Unit where
  F := fun _ ↦ W.addSeries
  zero_constantCoeff := fun _ ↦ W.constantCoeff_addSeries
  add_zero' := fun _ ↦ W.subst_unitR_addSeries
  zero_add' := fun _ ↦ W.subst_unitL_addSeries
  assoc' := fun _ ↦ W.assoc_addSeries
  comm' := fun _ ↦ by
    rw [show (fun s : Unit ⊕ Unit ↦ (MvPowerSeries.X s.swap : MvPowerSeries (Unit ⊕ Unit) O))
        = (MvPowerSeries.X ∘ Sum.swap) from rfl, ← MvPowerSeries.rename_eq_subst]
    exact W.rename_swap_addSeries



end wSeries

end WeierstrassCurve

end
