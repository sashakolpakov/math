import OAI.Analysis.Fourier.BochnerRiesz.DualityNorm
import OAI.Analysis.Fourier.BochnerRiesz.FourierLimit

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- A bounded measurable function is in `Lp` if its pairings against
`L1 ∩ Lp'` obey the dual norm estimate. No a priori global `Lp` hypothesis
is imposed on the function being estimated. -/
theorem eLpNorm_le_of_integrable_pairing {n : ℕ} {p : ℝ} (hp : 1 < p)
    {f : Space n → ℂ} (hf : AEStronglyMeasurable f volume)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) {A : ℝ≥0∞}
    (hbound : ∀ g : Space n → ℂ, Integrable g →
      MemLp g (ENNReal.ofReal (p / (p - 1))) volume →
      ‖∫ x, g x * f x‖ₑ ≤ A * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume) :
    eLpNorm f (ENNReal.ofReal p) volume ≤ A := by
  classical
  let u (j : ℕ) : Space n → ℂ := (Metric.ball 0 (j : ℝ)).indicator f
  have hu (j : ℕ) : AEStronglyMeasurable (u j) volume :=
    hf.indicator measurableSet_ball
  have hum (j : ℕ) : MemLp (u j) (ENNReal.ofReal p) volume := by
    have htop := memLp_top_of_bound (hu j) M (Eventually.of_forall (fun x ↦ by
      by_cases hx : x ∈ Metric.ball (0 : Space n) (j : ℝ)
      · simpa [u, hx] using hM x
      · have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
        simpa [u, hx] using hM0))
    exact htop.mono_exponent_of_measure_support_ne_top
      (s := Metric.ball 0 (j : ℝ)) (fun x hx ↦ by simp [u, hx])
      (measure_ball_lt_top.ne) le_top
  have hub (j : ℕ) : eLpNorm (u j) (ENNReal.ofReal p) volume ≤ A := by
    apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_integral_mul_bound volume hp (hum j)
    intro g hg
    let v : Space n → ℂ := (Metric.ball 0 (j : ℝ)).indicator g
    have hv : MemLp v (ENNReal.ofReal (p / (p - 1))) volume :=
      hg.indicator measurableSet_ball
    have hv1 : Integrable v := by
      apply memLp_one_iff_integrable.mp
      apply hv.mono_exponent_of_measure_support_ne_top
        (s := Metric.ball 0 (j : ℝ)) (fun x hx ↦ by simp [v, hx])
        (measure_ball_lt_top.ne)
      have hq : 1 ≤ p / (p - 1) := by
        apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
        linarith
      exact_mod_cast ENNReal.ofReal_le_ofReal hq
    have he : (fun x ↦ g x * u j x) = fun x ↦ v x * f x := by
      funext x
      by_cases hx : x ∈ Metric.ball (0 : Space n) (j : ℝ) <;> simp [u, v, hx]
    rw [he]
    exact (hbound v hv1 hv).trans
      (mul_le_mul le_rfl (eLpNorm_indicator_le g measurableSet_ball) zero_le zero_le)
  apply OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_le_of_tendsto_pointwise volume hu hf ?_ (by linarith) hub
  intro x
  obtain ⟨J, hJ⟩ := exists_nat_gt ‖x‖
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop J] with j hj
  have hx : x ∈ Metric.ball (0 : Space n) (j : ℝ) := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hJ.trans_le (Nat.cast_le.mpr hj)
  simp [u, hx]

end OAI.Analysis.Fourier.Restriction
