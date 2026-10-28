import OAI.AlgebraicGeometry.Comparison.Betti.CauchyAnnulusInvariance

/-! # Annular Cauchy Formula -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AnnularCauchyFormula.Dolbeault

noncomputable section

section

/-! The actual annular Cauchy formula for holomorphic functions on the
punctured complex line, with both contour orientations fixed explicitly. -/

open _root_.Complex Set _root_.Metric
open scoped _root_.Topology

theorem punctured_holomorphic_continuousOn_sphere {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) {R : ℝ} (hR : 0 < R) :
    ContinuousOn f (sphere 0 R) := by
  apply hf.continuousOn.mono
  intro w hw
  have hn : ‖w‖ = R := by simpa only [mem_sphere, dist_zero_right] using hw
  exact norm_pos_iff.mp (hn.symm ▸ hR)

theorem punctured_circleIntegral_radius_eq {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (∮ w in C(0, R), f w) = ∮ w in C(0, r), f w := by
  have hm {w : ℂ} (hw : w ∈ closedBall 0 R \ ball 0 r) : w ∈ PuncturedCauchy.Dolbeault.puncturedComplexOpen :=
    (CauchyAnnulusInvariance.Dolbeault.cauchyAnnulus_avoids_poles hr (z := 0) (Or.inl (by simpa only [norm_zero] using hr)) hw).1
  apply circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR (s := ∅) countable_empty
  · exact hf.continuousOn.mono (fun _ hw => hm hw)
  · intro w hw
    apply hf.differentiableAt
    apply PuncturedCauchy.Dolbeault.puncturedComplexOpen.isOpen.mem_nhds
    exact hm ⟨ball_subset_closedBall hw.1.1, fun h => hw.1.2 (ball_subset_closedBall h)⟩

theorem annularCauchyFormula {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))
    {r R : ℝ} (hr : 0 < r) {z : ℂ} (hrz : r < ‖z‖) (hzR : ‖z‖ < R) :
    CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform f R z - CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform f r z = f z := by
  have hz0 : z ∈ PuncturedCauchy.Dolbeault.puncturedComplexOpen := norm_pos_iff.mp (hr.trans hrz)
  have hR : 0 < R := hr.trans (hrz.trans hzR)
  have hd : DifferentiableOn ℂ (dslope f z) (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ) :=
    (Complex.differentiableOn_dslope (PuncturedCauchy.Dolbeault.puncturedComplexOpen.isOpen.mem_nhds hz0)).mpr hf
  have hi := punctured_circleIntegral_radius_eq hd hr (hrz.trans hzR).le
  rw [CauchyAnnulusInvariance.Dolbeault.circleIntegral_dslope_formula hR.le (ne_of_lt hzR)
      (punctured_holomorphic_continuousOn_sphere hf hR),
    CauchyAnnulusInvariance.Dolbeault.circleIntegral_dslope_formula hr.le (ne_of_gt hrz)
      (punctured_holomorphic_continuousOn_sphere hf hr),
    circleIntegral.integral_sub_inv_of_mem_ball (by simpa only [mem_ball, dist_zero_right] using hzR),
    CauchyAnnulusInvariance.Dolbeault.circleIntegral_inv_eq_zero_outside hr.le hrz, zero_mul, sub_zero] at hi
  have hdiff : (∮ w in C(0, R), f w / (w - z)) - (∮ w in C(0, r), f w / (w - z)) =
      (2 * Real.pi * I : ℂ) * f z := by linear_combination hi
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  unfold CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform
  rw [← mul_sub, hdiff, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end

/-! The positive Laurent part is an actual normalized Cauchy integral.
Contour invariance makes its variable-radius definition entire. -/

open _root_.Complex Set _root_.Metric Filter
open scoped _root_.Topology

theorem cauchyCircleTransform_holomorphic {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : CircleIntegrable f 0 R) {z : ℂ} (hz : ‖z‖ < R) :
    DifferentiableAt ℂ (CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform f R) z := by
  let r : NNReal := ⟨R, hR.le⟩
  have hp := hasFPowerSeriesOn_cauchy_integral (R := r) hf hR
  have hz' : z ∈ Metric.eball (0 : ℂ) r := by
    erw [Metric.eball_coe]
    change dist z 0 < R
    simpa only [dist_zero_right] using hz
  change DifferentiableAt ℂ (fun w => (2 * Real.pi * I : ℂ)⁻¹ *
    ∮ v in C(0, R), f v / (v - w)) z
  simp only [div_eq_inv_mul]
  convert (hp.analyticOnNhd z hz').differentiableAt using 1; rfl

def positiveLaurentPart (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform f (‖z‖ + 1) z

theorem positiveLaurentPart_eq_contour {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))
    {R : ℝ} {z : ℂ} (hz : ‖z‖ < R) :
    positiveLaurentPart f z = CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform f R z := by
  have hnorm : ‖z‖ < ‖z‖ + 1 := lt_add_one _
  have hpos : 0 < ‖z‖ + 1 := (norm_nonneg z).trans_lt hnorm
  rcases le_total (‖z‖ + 1) R with h | h
  · exact (CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform_radius_eq hf hpos h (Or.inl hnorm)).symm
  · exact CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform_radius_eq hf ((norm_nonneg z).trans_lt hz) h (Or.inl hz)

theorem positiveLaurentPart_entire {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) :
    Differentiable ℂ (positiveLaurentPart f) := by
  intro z
  let R := ‖z‖ + 1
  have hz : ‖z‖ < R := lt_add_one _
  have hR : 0 < R := (norm_nonneg z).trans_lt hz
  have hlocal : positiveLaurentPart f =ᶠ[𝓝 z] CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform f R := by
    filter_upwards [isOpen_ball.mem_nhds (show z ∈ ball 0 R by
      simpa only [mem_ball, dist_zero_right] using hz)] with w hw
    exact positiveLaurentPart_eq_contour hf (by simpa only [mem_ball, dist_zero_right] using hw)
  exact (cauchyCircleTransform_holomorphic hR
    ((punctured_holomorphic_continuousOn_sphere hf hR).circleIntegrable hR.le) hz).congr_of_eventuallyEq hlocal

end

end OAI.AlgebraicGeometry.Comparison.Betti.AnnularCauchyFormula.Dolbeault
