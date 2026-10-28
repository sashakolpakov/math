import OAI.RepresentationTheory.Weil.Local.RadialAnnulusBound
import OAI.RepresentationTheory.Weil.Local.RadialMajorant
import OAI.RepresentationTheory.Weil.Local.PlanarPowerDamping

/-! # Planar Integral -/

namespace OAI.RepresentationTheory.Weil.Local.PlanarIntegral.Construction

noncomputable section

section

/-! A uniform bound for the actual compact-annulus Gaussian integral. -/

open _root_.MeasureTheory Set

def planarAnnulusDamping (s ε R T b : ℝ) (z : ℝ × ℝ) : ℂ :=
  ((1 - RadialTailCutoffBound.Construction.radialCutoff T (PlanarRadialCompact.Construction.planarRadiusSquared z)) : ℝ) *
    (RadialTailCutoffBound.Construction.radialCutoff R (PlanarRadialCompact.Construction.planarRadiusSquared z) : ℝ) * PlanarPowerDamping.Construction.planarPowerDamping s ε b z

def planarTailDamping (s ε R b : ℝ) (z : ℝ × ℝ) : ℂ :=
  (RadialTailCutoffBound.Construction.radialCutoff R (PlanarRadialCompact.Construction.planarRadiusSquared z) : ℝ) * PlanarPowerDamping.Construction.planarPowerDamping s ε b z

theorem radialAnnulusWeight_amplitude (s ε R T t : ℝ) (hR : 0 < R) :
    t * RadialAnnulusWeight.Construction.radialAnnulusWeight s ε R T t =
      (1 - RadialTailCutoffBound.Construction.radialCutoff T t) * RadialTailCutoffBound.Construction.radialCutoff R t * Real.exp (-ε * t ^ s) := by
  by_cases ht : t = 0
  · subst t
    rw [RadialTailCutoffBound.Construction.radialCutoff_zero R 0 hR hR.le]
    simp
  · unfold RadialAnnulusWeight.Construction.radialAnnulusWeight RadialTailCutoffBound.Construction.radialTailWeight RealPower.Construction.realPowerWeight
    field_simp

theorem planarAnnulusDamping_weight (s ε R T b : ℝ) (hR : 0 < R) (z : ℝ × ℝ) :
    planarAnnulusDamping s ε R T b z =
      (PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) * RadialAnnulusWeight.Construction.radialAnnulusWeight s ε R T (PlanarRadialCompact.Construction.planarRadiusSquared z) *
        PlanarQuadraticPhase.Construction.planarQuadraticPhase b z := by
  have hh := congrArg (fun r : ℝ => (r : ℂ))
    (radialAnnulusWeight_amplitude s ε R T (PlanarRadialCompact.Construction.planarRadiusSquared z) hR)
  push_cast at hh
  unfold planarAnnulusDamping PlanarPowerDamping.Construction.planarPowerDamping
  rw [hh]
  push_cast
  ring

theorem planar_annulus_integral_bound : ∃ C : ℝ, 0 < C ∧
    ∀ s ε R T b : ℝ, 0 < s → s ≤ 1 → 0 ≤ ε → 0 < R → 0 < T →
      b ^ 2 * ‖∫ z, planarAnnulusDamping s ε R T b z‖ ≤ Real.pi * C / R := by
  obtain ⟨C, hC, hbound⟩ := RadialAnnulusBound.Construction.radialAnnulusWeight_laplacian_bound
  refine ⟨C, hC, fun s ε R T b hs hs1 hε hR hT => ?_⟩
  have htransfer := PlanarRadialTransfer.Construction.planar_radial_quadratic_integral_transfer b
    (fun t => (RadialAnnulusWeight.Construction.radialAnnulusWeight s ε R T t : ℂ))
    (fun t => (RadialAnnulusWeight.Construction.radialAnnulusWeightDerivative s ε R T t : ℂ))
    (fun t => (RadialAnnulusWeight.Construction.radialAnnulusWeightSecondDerivative s ε R T t : ℂ))
    (fun t _ => (RadialAnnulusWeight.Construction.radialAnnulusWeight_hasDerivAt s ε R T hR t).ofReal_comp)
    (fun t _ => (RadialAnnulusWeight.Construction.radialAnnulusWeightDerivative_hasDerivAt s ε R T hR t).ofReal_comp)
    (RadialAnnulusWeight.Construction.radialAnnulusWeight_transfer_integrable s ε R T b hR hT)
  have hi : (∫ z, (PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) *
      RadialAnnulusWeight.Construction.radialAnnulusWeight s ε R T (PlanarRadialCompact.Construction.planarRadiusSquared z) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z) =
      ∫ z, planarAnnulusDamping s ε R T b z := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => (planarAnnulusDamping_weight s ε R T b hR z).symm
  rw [hi] at htransfer
  have hn := congrArg norm htransfer
  rw [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hn
  rw [hn]
  have hm (t : ℝ) : |t * RadialAnnulusWeight.Construction.radialAnnulusWeightSecondDerivative s ε R T t +
      RadialAnnulusWeight.Construction.radialAnnulusWeightDerivative s ε R T t| ≤ RadialMajorant.Construction.radialInverseSquareMajorant R C t := by
    by_cases ht : t < R
    · obtain ⟨_, h1, h2⟩ := RadialAnnulusWeight.Construction.radialAnnulusWeight_lower_zero s ε R T t hR ht
      simp only [h1, h2, mul_zero, zero_add, abs_zero]
      exact RadialMajorant.Construction.radialInverseSquareMajorant_nonneg R C t hC.le
    · have hRt : R ≤ t := le_of_not_gt ht
      rw [RadialMajorant.Construction.radialInverseSquareMajorant, indicator_of_mem (show t ∈ Ici R from hRt)]
      exact hbound s ε R T t hs hs1 hε hR hT (hR.trans_le hRt)
  calc
    _ ≤ ∫ z : ℝ × ℝ, RadialMajorant.Construction.radialInverseSquareMajorant R C (PlanarRadialCompact.Construction.planarRadiusSquared z) := by
      apply norm_integral_le_of_norm_le (RadialMajorant.Construction.planar_radialInverseSquareMajorant_integrable R C hR)
      exact Filter.Eventually.of_forall fun z => by
        rw [norm_mul, PlanarQuadraticPhase.Construction.planarQuadraticPhase_norm, mul_one]
        have hc : (PlanarRadialCompact.Construction.planarRadiusSquared z : ℂ) *
            RadialAnnulusWeight.Construction.radialAnnulusWeightSecondDerivative s ε R T (PlanarRadialCompact.Construction.planarRadiusSquared z) +
            RadialAnnulusWeight.Construction.radialAnnulusWeightDerivative s ε R T (PlanarRadialCompact.Construction.planarRadiusSquared z) =
            ((PlanarRadialCompact.Construction.planarRadiusSquared z * RadialAnnulusWeight.Construction.radialAnnulusWeightSecondDerivative s ε R T (PlanarRadialCompact.Construction.planarRadiusSquared z) +
              RadialAnnulusWeight.Construction.radialAnnulusWeightDerivative s ε R T (PlanarRadialCompact.Construction.planarRadiusSquared z) : ℝ) : ℂ) := by push_cast; rfl
        rw [hc, Complex.norm_real, Real.norm_eq_abs]
        exact hm _
    _ = _ := RadialMajorant.Construction.planar_radialInverseSquareMajorant_integral R C hR

end

section

/-! Removing the outer cutoff gives a uniform bound for the actual damped Gaussian tail. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem planarAnnulusDamping_continuous (s ε R T b : ℝ) (hs : 0 < s) :
    Continuous (planarAnnulusDamping s ε R T b) := by
  have hT := (RadialTailSmooth.Construction.radialCutoff_contDiff T).continuous.comp PlanarRadialCompact.Construction.planarRadiusSquared_continuous
  have hR := (RadialTailSmooth.Construction.radialCutoff_contDiff R).continuous.comp PlanarRadialCompact.Construction.planarRadiusSquared_continuous
  unfold planarAnnulusDamping
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub hT)).mul
    (Complex.continuous_ofReal.comp hR)).mul (PlanarPowerDamping.Construction.planarPowerDamping_continuous s ε b hs)

theorem planarTailDamping_continuous (s ε R b : ℝ) (hs : 0 < s) :
    Continuous (planarTailDamping s ε R b) :=
  (Complex.continuous_ofReal.comp ((RadialTailSmooth.Construction.radialCutoff_contDiff R).continuous.comp
    PlanarRadialCompact.Construction.planarRadiusSquared_continuous)).mul (PlanarPowerDamping.Construction.planarPowerDamping_continuous s ε b hs)

theorem planarAnnulusDamping_norm_le (s ε R T b : ℝ) (z : ℝ × ℝ) :
    ‖planarAnnulusDamping s ε R T b z‖ ≤ Real.exp (-ε * PlanarRadialCompact.Construction.planarRadiusSquared z ^ s) := by
  rw [planarAnnulusDamping, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (sub_nonneg.mpr (RadialTailCutoffBound.Construction.radialCutoff_le_one T _)),
    Real.norm_of_nonneg (RadialTailCutoffBound.Construction.radialCutoff_nonneg R _), PlanarPowerDamping.Construction.planarPowerDamping_norm]
  apply mul_le_of_le_one_left (Real.exp_pos _).le
  exact (mul_le_mul_of_nonneg_right
    (show 1 - RadialTailCutoffBound.Construction.radialCutoff T (PlanarRadialCompact.Construction.planarRadiusSquared z) ≤ (1 : ℝ) by
      linarith [RadialTailCutoffBound.Construction.radialCutoff_nonneg T (PlanarRadialCompact.Construction.planarRadiusSquared z)])
    (RadialTailCutoffBound.Construction.radialCutoff_nonneg R _)).trans
      (by simpa only [one_mul] using RadialTailCutoffBound.Construction.radialCutoff_le_one R (PlanarRadialCompact.Construction.planarRadiusSquared z))

theorem planarTailDamping_norm_le (s ε R b : ℝ) (z : ℝ × ℝ) :
    ‖planarTailDamping s ε R b z‖ ≤ Real.exp (-ε * PlanarRadialCompact.Construction.planarRadiusSquared z ^ s) := by
  rw [planarTailDamping, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (RadialTailCutoffBound.Construction.radialCutoff_nonneg R _), PlanarPowerDamping.Construction.planarPowerDamping_norm]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (RadialTailCutoffBound.Construction.radialCutoff_le_one R _)

theorem planar_power_weight_real_integrable (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    Integrable (fun z : ℝ × ℝ => Real.exp (-ε * PlanarRadialCompact.Construction.planarRadiusSquared z ^ s)) := by
  have hi := (PlanarPowerDamping.Construction.planar_power_weight_integrable s ε hs hε).norm
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hi

theorem planarTailDamping_integrable (s ε R b : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    Integrable (planarTailDamping s ε R b) :=
  (planar_power_weight_real_integrable s ε hs hε).mono'
    (planarTailDamping_continuous s ε R b hs).aestronglyMeasurable
    (Eventually.of_forall (planarTailDamping_norm_le s ε R b))

theorem planarAnnulusDamping_tendsto (s ε R b : ℝ) (z : ℝ × ℝ) :
    Tendsto (fun T => planarAnnulusDamping s ε R T b z) atTop (𝓝 (planarTailDamping s ε R b z)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (max 1 (PlanarRadialCompact.Construction.planarRadiusSquared z))] with T hT
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hT)
  have ht : PlanarRadialCompact.Construction.planarRadiusSquared z ≤ T := (le_max_right _ _).trans hT
  rw [planarAnnulusDamping, RadialTailCutoffBound.Construction.radialCutoff_zero T _ hT0 ht, sub_zero]
  simp only [Complex.ofReal_one, one_mul, planarTailDamping]

theorem planarAnnulusDamping_integral_tendsto (s ε R b : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    Tendsto (fun T => ∫ z, planarAnnulusDamping s ε R T b z) atTop
      (𝓝 (∫ z, planarTailDamping s ε R b z)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun z => Real.exp (-ε * PlanarRadialCompact.Construction.planarRadiusSquared z ^ s))
  · exact Eventually.of_forall fun T => (planarAnnulusDamping_continuous s ε R T b hs).aestronglyMeasurable
  · exact Eventually.of_forall fun T => Eventually.of_forall (planarAnnulusDamping_norm_le s ε R T b)
  · exact planar_power_weight_real_integrable s ε hs hε
  · exact Eventually.of_forall (planarAnnulusDamping_tendsto s ε R b)

theorem planar_tail_integral_bound : ∃ C : ℝ, 0 < C ∧
    ∀ s ε R b : ℝ, 0 < s → s ≤ 1 → 0 < ε → 0 < R →
      b ^ 2 * ‖∫ z, planarTailDamping s ε R b z‖ ≤ Real.pi * C / R := by
  obtain ⟨C, hC, hbound⟩ := planar_annulus_integral_bound
  refine ⟨C, hC, fun s ε R b hs hs1 hε hR => ?_⟩
  have ht := (planarAnnulusDamping_integral_tendsto s ε R b hs hε).norm.const_mul (b ^ 2)
  apply le_of_tendsto ht
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact hbound s ε R T b hs hs1 hε.le hR hT

end

section

/-! Compact-core convergence for the power-damped planar quadratic integral. -/

open _root_.MeasureTheory Filter Set
open scoped _root_.Topology

def planarCoreCutoff (R : ℝ) (z : ℝ × ℝ) : ℝ := 1 - RadialTailCutoffBound.Construction.radialCutoff R (PlanarRadialCompact.Construction.planarRadiusSquared z)

def planarCoreDamping (s ε R b : ℝ) : ℝ × ℝ → ℂ :=
  PlanarPowerDamping.Construction.planarPowerDamping s ε b - planarTailDamping s ε R b

theorem planarCoreCutoff_nonneg (R : ℝ) (z : ℝ × ℝ) : 0 ≤ planarCoreCutoff R z :=
  sub_nonneg.mpr (RadialTailCutoffBound.Construction.radialCutoff_le_one R _)

theorem planarCoreCutoff_continuous (R : ℝ) : Continuous (planarCoreCutoff R) :=
  continuous_const.sub ((RadialTailSmooth.Construction.radialCutoff_contDiff R).continuous.comp PlanarRadialCompact.Construction.planarRadiusSquared_continuous)

theorem planarCoreCutoff_compactSupport (R : ℝ) (hR : 0 < R) : HasCompactSupport (planarCoreCutoff R) := by
  have hc := PlanarRadialCompact.Construction.planarRadial_compactSupport (fun t => ((1 - RadialTailCutoffBound.Construction.radialCutoff R t : ℝ) : ℂ)) (2 * R)
    (fun t ht => by rw [RadialTailCutoffBound.Construction.radialCutoff_one R t hR ht, sub_self]; rfl)
  have heq : (fun z => ‖PlanarRadialCompact.Construction.planarRadial (fun t => ((1 - RadialTailCutoffBound.Construction.radialCutoff R t : ℝ) : ℂ)) z‖) =
      planarCoreCutoff R := by
    funext z
    rw [PlanarRadialCompact.Construction.planarRadial, Complex.norm_real]
    change ‖planarCoreCutoff R z‖ = planarCoreCutoff R z
    exact Real.norm_of_nonneg (planarCoreCutoff_nonneg R z)
  rw [← heq]
  exact hc.norm

theorem planarCoreCutoff_integrable (R : ℝ) (hR : 0 < R) : Integrable (planarCoreCutoff R) :=
  (planarCoreCutoff_continuous R).integrable_of_hasCompactSupport (planarCoreCutoff_compactSupport R hR)

theorem planarCoreDamping_eq (s ε R b : ℝ) (z : ℝ × ℝ) :
    planarCoreDamping s ε R b z = (planarCoreCutoff R z : ℂ) * PlanarPowerDamping.Construction.planarPowerDamping s ε b z := by
  unfold planarCoreDamping planarTailDamping planarCoreCutoff
  simp only [Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_one]
  ring

theorem planarCoreDamping_integrable (s ε R b : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    Integrable (planarCoreDamping s ε R b) :=
  (PlanarPowerDamping.Construction.planarPowerDamping_integrable s ε b hs hε).sub (planarTailDamping_integrable s ε R b hs hε)

theorem planarCoreDamping_integral_tendsto (s R b : ℝ) (hs : 0 < s) (hR : 0 < R) :
    Tendsto (fun ε => ∫ z, planarCoreDamping s ε R b z) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z, (planarCoreCutoff R z : ℂ) * PlanarQuadraticPhase.Construction.planarQuadraticPhase b z)) := by
  apply tendsto_integral_filter_of_dominated_convergence (planarCoreCutoff R)
  · exact Eventually.of_forall fun ε => ((PlanarPowerDamping.Construction.planarPowerDamping_continuous s ε b hs).sub
      (planarTailDamping_continuous s ε R b hs)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with ε hε
    exact Eventually.of_forall fun z => by
      rw [planarCoreDamping_eq, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (planarCoreCutoff_nonneg R z)]
      exact mul_le_of_le_one_right (planarCoreCutoff_nonneg R z) (PlanarPowerDamping.Construction.planarPowerDamping_norm_le s ε b hε.le z)
  · exact planarCoreCutoff_integrable R hR
  · exact Eventually.of_forall fun z => by
      have ht := (PlanarPowerDamping.Construction.planarPowerDamping_tendsto s b z).const_mul (planarCoreCutoff R z : ℂ)
      exact ht.congr fun ε => (planarCoreDamping_eq s ε R b z).symm

theorem planarPowerDamping_integral_split (s ε R b : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    (∫ z, PlanarPowerDamping.Construction.planarPowerDamping s ε b z) =
      (∫ z, planarCoreDamping s ε R b z) + ∫ z, planarTailDamping s ε R b z := by
  change (∫ z, PlanarPowerDamping.Construction.planarPowerDamping s ε b z) =
    (∫ z, PlanarPowerDamping.Construction.planarPowerDamping s ε b z - planarTailDamping s ε R b z) + ∫ z, planarTailDamping s ε R b z
  rw [integral_sub (PlanarPowerDamping.Construction.planarPowerDamping_integrable s ε b hs hε)
    (planarTailDamping_integrable s ε R b hs hε), sub_add_cancel]

end

/-! The planar quadratic integral has the same limit for every norm power in (0, 1]. -/

open _root_.MeasureTheory Filter Set
open scoped _root_.Topology

theorem planarPowerDamping_integral_difference_tendsto
    (s b : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (hb : b ≠ 0) :
    Tendsto (fun ε => (∫ z, PlanarPowerDamping.Construction.planarPowerDamping s ε b z) -
      ∫ z, PlanarPowerDamping.Construction.planarPowerDamping 1 ε b z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC, htail⟩ := planar_tail_integral_bound
  let K := b ^ 2
  have hK : 0 < K := sq_pos_of_ne_zero hb
  let P := Real.pi * C
  have hP : 0 < P := mul_pos Real.pi_pos hC
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  let R := 8 * P / (K * δ)
  have hR : 0 < R := div_pos (mul_pos (by norm_num) hP) (mul_pos hK hδ)
  have hRval : 2 * P / R = K * δ / 4 := by dsimp [R]; field_simp; norm_num
  have hmid : Tendsto (fun ε => (∫ z, planarCoreDamping s ε R b z) -
      ∫ z, planarCoreDamping 1 ε R b z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [sub_self] using (planarCoreDamping_integral_tendsto s R b hs hR).sub
      (planarCoreDamping_integral_tendsto 1 R b (by norm_num) hR)
  have hm : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖(∫ z, planarCoreDamping s ε R b z) - ∫ z, planarCoreDamping 1 ε R b z‖ < δ / 2 := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hmid.eventually (Metric.ball_mem_nhds (0 : ℂ) (half_pos hδ))
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0), hm] with ε hε hmε
  let M := (∫ z, planarCoreDamping s ε R b z) - ∫ z, planarCoreDamping 1 ε R b z
  let A := ∫ z, planarTailDamping s ε R b z
  let B := ∫ z, planarTailDamping 1 ε R b z
  have ha : K * ‖A‖ ≤ P / R := htail s ε R b hs hs1 hε hR
  have hb' : K * ‖B‖ ≤ P / R := htail 1 ε R b (by norm_num) le_rfl hε hR
  have hn : ‖M + (A - B)‖ ≤ ‖M‖ + (‖A‖ + ‖B‖) :=
    (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
  have ht : K * ‖M + (A - B)‖ < K * δ := by
    have hmul := mul_le_mul_of_nonneg_left hn hK.le
    change ‖M‖ < δ / 2 at hmε
    have hm' := mul_lt_mul_of_pos_left hmε hK
    have hsum : K * (‖A‖ + ‖B‖) ≤ K * δ / 4 := by
      calc
        _ ≤ P / R + P / R := by rw [mul_add]; exact add_le_add ha hb'
        _ = 2 * P / R := by ring
        _ = _ := hRval
    nlinarith only [hmul, hm', hsum, hK, hδ]
  rw [dist_zero_right, planarPowerDamping_integral_split s ε R b hs hε,
    planarPowerDamping_integral_split 1 ε R b (by norm_num) hε]
  have heq : ((∫ z, planarCoreDamping s ε R b z) + A) -
      ((∫ z, planarCoreDamping 1 ε R b z) + B) = M + (A - B) := by dsimp [M]; ring
  change ‖((∫ z, planarCoreDamping s ε R b z) + A) -
    ((∫ z, planarCoreDamping 1 ε R b z) + B)‖ < δ
  rw [heq]
  exact (mul_lt_mul_iff_right₀ hK).mp ht

end

end OAI.RepresentationTheory.Weil.Local.PlanarIntegral.Construction
