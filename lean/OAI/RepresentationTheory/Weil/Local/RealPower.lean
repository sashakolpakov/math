import OAI.RepresentationTheory.Weil.Local.OscillatoryTailTools

/-! # Real Power -/

namespace OAI.RepresentationTheory.Weil.Local.RealPower.Construction

noncomputable section

section

/-! Monotone weights arising from power-law Gaussian damping. -/

open _root_.MeasureTheory Set

def realPowerWeight (p ε x : ℝ) : ℝ := Real.exp (-ε * x ^ p) / x

def realPowerWeightDerivative (p ε x : ℝ) : ℝ :=
  -Real.exp (-ε * x ^ p) * (ε * p * x ^ p + 1) / x ^ 2

theorem realPowerWeight_hasDerivAt (p ε x : ℝ) (hx : 0 < x) :
    HasDerivAt (realPowerWeight p ε) (realPowerWeightDerivative p ε x) x := by
  have hd := (((Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).const_mul (-ε)).exp).div
    (hasDerivAt_id x) hx.ne'
  dsimp only [id_eq] at hd
  convert! hd using 1
  unfold realPowerWeightDerivative
  rw [Real.rpow_sub_one hx.ne']
  field_simp
  ring

theorem realPowerWeight_nonneg (p ε x : ℝ) (hx : 0 < x) : 0 ≤ realPowerWeight p ε x := by
  exact (div_pos (Real.exp_pos _) hx).le

theorem realPowerWeightDerivative_nonpos (p ε x : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (hx : 0 < x) :
    realPowerWeightDerivative p ε x ≤ 0 := by
  unfold realPowerWeightDerivative
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le)
      (by positivity)
  · exact sq_nonneg x

theorem realPowerWeight_le_inverse (p ε x : ℝ) (hε : 0 ≤ ε) (hx : 0 < x) :
    realPowerWeight p ε x ≤ x⁻¹ := by
  change Real.exp (-ε * x ^ p) / x ≤ x⁻¹
  rw [← one_div x]
  apply div_le_div_of_nonneg_right _ hx.le
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε)
    (Real.rpow_nonneg hx.le p))

theorem realPowerWeightDerivative_continuousOn (p ε a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (realPowerWeightDerivative p ε) (uIcc a b) := by
  intro x hx
  have hxpos : 0 < x := ha.trans_le ((uIcc_of_le hab ▸ hx).1)
  have hr : ContinuousAt (fun t : ℝ => t ^ p) x :=
    continuousAt_id.rpow_const (Or.inl hxpos.ne')
  apply ContinuousAt.continuousWithinAt
  unfold realPowerWeightDerivative
  exact ((hr.const_mul (-ε)).rexp.neg.mul
    ((continuousAt_const.mul hr).add continuousAt_const)).div
      (continuousAt_id.pow 2) (pow_ne_zero _ hxpos.ne')

theorem real_quadratic_phase_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun t : ℝ => Gaussian.Construction.realCharacter c (t ^ 2 / 2))
      ((2 * Real.pi * c * Complex.I : ℂ) * x * Gaussian.Construction.realCharacter c (x ^ 2 / 2)) x := by
  have he (t : ℝ) : Gaussian.Construction.realCharacter c (t ^ 2 / 2) =
      Complex.exp ((Real.pi * c : ℂ) * Complex.I * (t : ℂ) ^ 2) := by
    rw [Gaussian.Construction.realCharacter_apply]
    congr 1
    push_cast
    ring
  simp_rw [he]
  have hd := ((((hasDerivAt_id x).ofReal_comp).pow 2).const_mul
    ((Real.pi * c : ℂ) * Complex.I)).cexp
  dsimp only [id_eq, Pi.pow_apply] at hd
  convert! hd using 1
  norm_num
  ring

end

section

/-! Uniform tail control for a real quadratic phase with arbitrary positive-power damping. -/

open _root_.MeasureTheory Set

theorem real_power_damped_interval_tail_bound
    (p ε c a b : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) :
    (2 * Real.pi * |c|) *
      ‖∫ x in a..b, (Real.exp (-ε * x ^ p) : ℂ) * Gaussian.Construction.realCharacter c (x ^ 2 / 2)‖ ≤ 2 / a := by
  let K : ℂ := 2 * Real.pi * c * Complex.I
  let v : ℝ → ℂ := fun x => Gaussian.Construction.realCharacter c (x ^ 2 / 2)
  let v' : ℝ → ℂ := fun x => K * x * v x
  have hxpos (x : ℝ) (hx : x ∈ uIcc a b) : 0 < x :=
    ha.trans_le ((uIcc_of_le hab ▸ hx).1)
  have hv : Continuous v := (RealTestSpace.Construction.realCharacter_temperate c).1.continuous.comp (by fun_prop)
  have hv' : Continuous v' := by dsimp [v']; fun_prop
  have hJ := OscillatoryTailTools.Construction.monotone_weight_oscillatory_bound hab (realPowerWeight p ε)
    (realPowerWeightDerivative p ε) v v'
    (fun x hx => realPowerWeight_hasDerivAt p ε x (hxpos x hx))
    (fun x _ => real_quadratic_phase_hasDerivAt c x)
    (realPowerWeightDerivative_continuousOn p ε a b ha hab).intervalIntegrable
    (hv'.intervalIntegrable _ _)
    (fun x hx => realPowerWeight_nonneg p ε x (hxpos x hx))
    (fun x hx => realPowerWeightDerivative_nonpos p ε x hp hε (hxpos x hx))
    (fun x _ => (QuadraticIntertwiner.Construction.realCharacter_unitary c _).le)
  have hInt : (∫ x in a..b, (realPowerWeight p ε x : ℂ) * v' x) =
      K * ∫ x in a..b, (Real.exp (-ε * x ^ p) : ℂ) * Gaussian.Construction.realCharacter c (x ^ 2 / 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hxpos x hx).ne'
    change ((Real.exp (-ε * x ^ p) / x : ℝ) : ℂ) * (K * x * Gaussian.Construction.realCharacter c (x ^ 2 / 2)) = _
    rw [Complex.ofReal_div]
    field_simp
  have hK : ‖K‖ = 2 * Real.pi * |c| := by
    dsimp [K]
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hInt, norm_mul, hK] at hJ
  calc
    _ ≤ 2 * realPowerWeight p ε a := hJ
    _ ≤ 2 * a⁻¹ := mul_le_mul_of_nonneg_left (realPowerWeight_le_inverse p ε a hε ha) (by norm_num)
    _ = 2 / a := (div_eq_mul_inv _ _).symm

end

section

/-! Integrability of the actual real damping after an arbitrary norm-power change. -/

open _root_.MeasureTheory Set

def realPowerDamping (p ε c x : ℝ) : ℂ :=
  (Real.exp (-ε * |x| ^ p) : ℂ) * Gaussian.Construction.realCharacter c (x ^ 2 / 2)

theorem realPowerDamping_norm (p ε c x : ℝ) :
    ‖realPowerDamping p ε c x‖ = Real.exp (-ε * |x| ^ p) := by
  rw [realPowerDamping, norm_mul, QuadraticIntertwiner.Construction.realCharacter_unitary, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

theorem realPowerDamping_continuous (p ε c : ℝ) (hp : 0 < p) :
    Continuous (realPowerDamping p ε c) := by
  have hpow : Continuous (fun x : ℝ => |x| ^ p) := continuous_abs.rpow_const (fun _ => Or.inr hp.le)
  have he : Continuous (fun x : ℝ => Real.exp (-ε * |x| ^ p)) := (hpow.const_mul (-ε)).rexp
  exact (Complex.continuous_ofReal.comp he).mul
    ((RealTestSpace.Construction.realCharacter_temperate c).1.continuous.comp (by fun_prop))

theorem real_power_damping_integrable (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    Integrable (fun x : ℝ => Real.exp (-ε * |x| ^ p)) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-ε * |x| ^ p)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (by norm_num) hp hε
    simp only [Real.rpow_zero, one_mul] at h
    apply h.congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp only
    rw [abs_of_pos (show 0 < x from hx)]
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hpos

theorem realPowerDamping_integrable (p ε c : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    Integrable (realPowerDamping p ε c) := by
  apply (real_power_damping_integrable p ε hp hε).mono'
    (realPowerDamping_continuous p ε c hp).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => (realPowerDamping_norm p ε c x).le

theorem realPowerDamping_even (p ε c x : ℝ) : realPowerDamping p ε c (-x) = realPowerDamping p ε c x := by
  simp [realPowerDamping]

theorem realPowerDamping_two (ε c x : ℝ) : realPowerDamping 2 ε c x = RealDiagonalGaussian.Construction.realQuadraticDamping c ε x := by
  rw [realPowerDamping, Real.rpow_two, sq_abs]
  rfl

end

section

/-! Half-line tail estimates and compact-interval convergence for power damping. -/

open _root_.MeasureTheory Set Filter
open scoped _root_.Topology

theorem realPowerDamping_interval_tail_bound
    (p ε c a b : ℝ) (hp : 0 < p) (hε : 0 ≤ ε) (ha : 0 < a) (hab : a ≤ b) :
    (2 * Real.pi * |c|) * ‖∫ x in a..b, realPowerDamping p ε c x‖ ≤ 2 / a := by
  have heq : (∫ x in a..b, realPowerDamping p ε c x) =
      ∫ x in a..b, (Real.exp (-ε * x ^ p) : ℂ) * Gaussian.Construction.realCharacter c (x ^ 2 / 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxpos : 0 < x := ha.trans_le ((uIcc_of_le hab ▸ hx).1)
    simp only [realPowerDamping, abs_of_pos hxpos]
  rw [heq]
  exact real_power_damped_interval_tail_bound p ε c a b hp hε ha hab

theorem realPowerDamping_halfLine_tail_bound
    (p ε c a : ℝ) (hp : 0 < p) (hε : 0 < ε) (ha : 0 < a) :
    (2 * Real.pi * |c|) * ‖∫ x in Ioi a, realPowerDamping p ε c x‖ ≤ 2 / a := by
  have ht := intervalIntegral_tendsto_integral_Ioi a
    (realPowerDamping_integrable p ε c hp hε).integrableOn
    (tendsto_id : Tendsto (fun b : ℝ => b) atTop atTop)
  apply le_of_tendsto (ht.norm.const_mul (2 * Real.pi * |c|))
  filter_upwards [eventually_ge_atTop a] with b hb
  exact realPowerDamping_interval_tail_bound p ε c a b hp hε.le ha hb

theorem realPowerDamping_norm_le (p ε c x : ℝ) (hε : 0 ≤ ε) :
    ‖realPowerDamping p ε c x‖ ≤ 1 := by
  rw [realPowerDamping_norm, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε)
    (Real.rpow_nonneg (abs_nonneg x) p)

theorem realPowerDamping_tendsto (p c x : ℝ) :
    Tendsto (fun ε => realPowerDamping p ε c x) (𝓝[>] (0 : ℝ))
      (𝓝 (Gaussian.Construction.realCharacter c (x ^ 2 / 2))) := by
  have h : ContinuousAt (fun ε => realPowerDamping p ε c x) 0 := by
    unfold realPowerDamping
    fun_prop
  simpa [realPowerDamping] using h.tendsto.mono_left nhdsWithin_le_nhds

theorem realPowerDamping_interval_tendsto (p c a b : ℝ) (hp : 0 < p) :
    Tendsto (fun ε => ∫ x in a..b, realPowerDamping p ε c x) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in a..b, Gaussian.Construction.realCharacter c (x ^ 2 / 2))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  · exact Eventually.of_forall fun ε =>
      (realPowerDamping_continuous p ε c hp).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with ε hε
    exact Eventually.of_forall fun x _ => realPowerDamping_norm_le p ε c x hε.le
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun x _ => realPowerDamping_tendsto p c x

end

/-! The real Fresnel limit is unchanged by any positive power in the damping. -/

open _root_.MeasureTheory Set Filter
open scoped _root_.Topology

theorem realPowerDamping_integral_eq_twice_halfLine
    (p ε c : ℝ) (hp : 0 < p) (hε : 0 < ε) :
    (∫ x, realPowerDamping p ε c x) = 2 * ∫ x in Ioi 0, realPowerDamping p ε c x := by
  have hi := realPowerDamping_integrable p ε c hp hε
  have heq : (∫ x in Iic 0, realPowerDamping p ε c x) =
      ∫ x in Ioi 0, realPowerDamping p ε c x := by
    have hn := integral_comp_neg_Iic 0 (realPowerDamping p ε c)
    simpa only [realPowerDamping_even, neg_zero] using hn
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hi.integrableOn hi.integrableOn,
    heq, two_mul]

theorem realPowerDamping_halfLine_difference_tendsto
    (p c : ℝ) (hp : 0 < p) (hc : c ≠ 0) :
    Tendsto (fun ε => (∫ x in Ioi 0, realPowerDamping p ε c x) -
      ∫ x in Ioi 0, realPowerDamping 2 ε c x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let K := 2 * Real.pi * |c|
  have hK : 0 < K := mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr hc)
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let R := 16 / (K * δ)
  have hR : 0 < R := div_pos (by norm_num) (mul_pos hK hδ)
  have hRval : 4 / R = K * δ / 4 := by dsimp [R]; field_simp; ring
  have hmid : Tendsto (fun ε => (∫ x in 0..R, realPowerDamping p ε c x) -
      ∫ x in 0..R, realPowerDamping 2 ε c x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [sub_self] using (realPowerDamping_interval_tendsto p c 0 R hp).sub
      (realPowerDamping_interval_tendsto 2 c 0 R (by norm_num))
  have hm : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖(∫ x in 0..R, realPowerDamping p ε c x) -
        ∫ x in 0..R, realPowerDamping 2 ε c x‖ < δ / 2 := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hmid.eventually (Metric.ball_mem_nhds (0 : ℂ) (half_pos hδ))
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0), hm] with ε hε hmε
  have hip := realPowerDamping_integrable p ε c hp hε
  have hi2 := realPowerDamping_integrable 2 ε c (by norm_num) hε
  have hsp := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := R)
    hip.integrableOn hip.integrableOn
  have hs2 := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := R)
    hi2.integrableOn hi2.integrableOn
  have htp := realPowerDamping_halfLine_tail_bound p ε c R hp hε hR
  have ht2 := realPowerDamping_halfLine_tail_bound 2 ε c R (by norm_num) hε hR
  let M := (∫ x in 0..R, realPowerDamping p ε c x) - ∫ x in 0..R, realPowerDamping 2 ε c x
  let A := ∫ x in Ioi R, realPowerDamping p ε c x
  let B := ∫ x in Ioi R, realPowerDamping 2 ε c x
  have hn : ‖M + (A - B)‖ ≤ ‖M‖ + (‖A‖ + ‖B‖) :=
    (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
  have htotal : K * ‖M + (A - B)‖ < K * δ := by
    have hmul := mul_le_mul_of_nonneg_left hn hK.le
    change K * ‖A‖ ≤ 2 / R at htp
    change K * ‖B‖ ≤ 2 / R at ht2
    change ‖M‖ < δ / 2 at hmε
    have hmε' := mul_lt_mul_of_pos_left hmε hK
    have htail : K * (‖A‖ + ‖B‖) ≤ K * δ / 4 := by
      calc
        _ ≤ 2 / R + 2 / R := by rw [mul_add]; exact add_le_add htp ht2
        _ = 4 / R := by ring
        _ = K * δ / 4 := hRval
    nlinarith only [hmul, hmε', htail, hK, hδ]
  rw [dist_zero_right, ← hsp, ← hs2]
  have heq : ((∫ x in 0..R, realPowerDamping p ε c x) + A) -
      ((∫ x in 0..R, realPowerDamping 2 ε c x) + B) = M + (A - B) := by dsimp [M]; ring
  change ‖((∫ x in 0..R, realPowerDamping p ε c x) + A) -
      ((∫ x in 0..R, realPowerDamping 2 ε c x) + B)‖ < δ
  rw [heq]
  exact (mul_lt_mul_iff_right₀ hK).mp htotal

theorem realPowerDamping_integral_difference_tendsto
    (p c : ℝ) (hp : 0 < p) (hc : c ≠ 0) :
    Tendsto (fun ε => (∫ x, realPowerDamping p ε c x) -
      ∫ x, realPowerDamping 2 ε c x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht := (realPowerDamping_halfLine_difference_tendsto p c hp hc).const_mul (2 : ℂ)
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with ε hε
  rw [realPowerDamping_integral_eq_twice_halfLine p ε c hp hε,
    realPowerDamping_integral_eq_twice_halfLine 2 ε c (by norm_num) hε, mul_sub]

theorem realPowerDamping_integral_tendsto
    (p c : ℝ) (hp : 0 < p) (hc : c ≠ 0) :
    Tendsto (fun ε => ∫ x, realPowerDamping p ε c x) (𝓝[>] (0 : ℝ))
      (𝓝 ((Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ))) := by
  have htwo : Tendsto (fun ε => ∫ x, realPowerDamping 2 ε c x) (𝓝[>] (0 : ℝ))
      (𝓝 ((Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ))) := by
    apply (RealDiagonalGaussian.Construction.realDampedGaussian_tendsto c hc).congr
    intro ε
    simp only [Gaussian.Construction.realDampedGaussian, realPowerDamping, Real.rpow_two, Real.norm_eq_abs, one_mul]
  have ht := (realPowerDamping_integral_difference_tendsto p c hp hc).add htwo
  simpa only [sub_add_cancel, zero_add] using ht

end

end OAI.RepresentationTheory.Weil.Local.RealPower.Construction
