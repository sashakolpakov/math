import OAI.Analysis.Fourier.Restriction.Polar
import OAI.MeasureTheory.Kakeya.Maximal

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


def direction {n : ℕ} (x : Space n) : Space n := ‖x‖⁻¹ • x

theorem measurable_direction {n : ℕ} : Measurable (direction : Space n → Space n) := by
  unfold direction
  fun_prop

theorem direction_pos_smul {n : ℕ} (x : Space n) {t : ℝ} (ht : 0 < t) :
    direction (t • x) = direction x := by
  unfold direction
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,smul_smul,mul_inv_rev,
    mul_assoc,inv_mul_cancel₀ ht.ne',mul_one]

theorem direction_pos_smul_unit {n : ℕ} {ω : Space n} (hω : ‖ω‖ = 1)
    {t : ℝ} (ht : 0 < t) : direction (t • ω) = ω := by
  unfold direction
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht,hω,mul_one,smul_smul,
    inv_mul_cancel₀ ht.ne',one_smul]

theorem radial_direction_inner_le {n : ℕ} (H : Space n → ℝ≥0∞)
    {R : ℝ} (hR : 0 < R) {ω : Space n} (hω : ‖ω‖ = 1) :
    (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t^(n-1)) *
      (closedBall 0 R).indicator (H ∘ direction) (t • ω)) ≤
        ENNReal.ofReal (R*R^(n-1)) * H ω := by
  let B := ENNReal.ofReal (R^(n-1))*H ω
  have hpt : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)),
      ENNReal.ofReal (t^(n-1)) * (closedBall 0 R).indicator (H ∘ direction) (t • ω) ≤
        (Ioc (0:ℝ) R).indicator (fun _ => B) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hnorm : ‖t • ω‖ = t := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht0,hω,mul_one]
    by_cases htR : t ≤ R
    · have hmem : t • ω ∈ closedBall 0 R := by simpa only [mem_closedBall_zero_iff,hnorm] using htR
      rw [indicator_of_mem hmem,indicator_of_mem (show t ∈ Ioc (0:ℝ) R from ⟨ht0,htR⟩),
        Function.comp_apply,direction_pos_smul_unit hω ht0]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht0.le htR _)) le_rfl
    · have hnot : t • ω ∉ closedBall 0 R := by simpa only [mem_closedBall_zero_iff,hnorm] using htR
      simp only [indicator_of_notMem hnot,mul_zero]
      exact bot_le
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), (Ioc (0:ℝ) R).indicator (fun _ => B) t := lintegral_mono_ae hpt
    _ ≤ ∫⁻ t, (Ioc (0:ℝ) R).indicator (fun _ => B) t :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (R*R^(n-1))*H ω := by
      rw [lintegral_indicator measurableSet_Ioc]
      simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,B]
      rw [ENNReal.ofReal_mul hR.le]
      ac_rfl

/-- A radial lift over a bounded ball has its angular integral controlled
by the genuine sphere measure used in the Kakeya estimate. -/
theorem lintegral_radial_direction_ball {n : ℕ} (hn : 1 ≤ n)
    {R : ℝ} (hR : 0 < R) {H : Space n → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ x in closedBall 0 R, H (direction x)) ≤
      ENNReal.ofReal (R*R^(n-1)) * ∫⁻ ω, H ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
  rw [← lintegral_indicator (isClosed_closedBall.measurableSet)]
  have hmeas : Measurable ((closedBall (0:Space n) R).indicator (fun x => H (direction x))) :=
    (hH.comp measurable_direction).indicator isClosed_closedBall.measurableSet
  rw [OAI.Analysis.Fourier.Restriction.lintegral_polar_sphereMeasure hn hmeas]
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (R*R^(n-1))*H ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      apply lintegral_mono_ae
      filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with ω hω
      simpa only [Function.comp_apply] using! radial_direction_inner_le H hR hω
    _ = _ := lintegral_const_mul _ hH

end OAI.Geometry.Nikodym
