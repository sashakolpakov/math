import OAI.Analysis.PDE.Concentration.LocalSupermean

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
open scoped Topology ContDiff

/-- The exact logarithmic harmonic barrier for a planar annulus. -/
noncomputable def annulusLog (a b : ℝ) (z : ℂ) : ℝ :=
  (Real.log ‖z‖ - Real.log a) / (Real.log b - Real.log a)

theorem harmonicAt_annulusLog (a b : ℝ) {z : ℂ} (hz : z ≠ 0) :
    HarmonicAt (annulusLog a b) z := by
  have hlog : HarmonicAt (fun z : ℂ => Real.log ‖z‖) z :=
    analyticAt_id.harmonicAt_log_norm hz
  have h := (hlog.sub (harmonicAt_const (Real.log a))).const_smul
    (c := (Real.log b - Real.log a)⁻¹)
  convert h using 1
  funext w
  simp [annulusLog, div_eq_mul_inv, mul_comm]

theorem annulusLog_inner (a b : ℝ) {z : ℂ} (hz : ‖z‖ = a) : annulusLog a b z = 0 := by
  simp [annulusLog, hz]

theorem annulusLog_outer {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {z : ℂ} (hz : ‖z‖ = b) : annulusLog a b z = 1 := by
  have hd : 0 < Real.log b - Real.log a := sub_pos.mpr (Real.log_lt_log ha hab)
  simp [annulusLog, hz, hd.ne']

theorem annulusLog_mem_Icc {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {z : ℂ} (haz : a ≤ ‖z‖) (hzb : ‖z‖ ≤ b) : annulusLog a b z ∈ Icc 0 1 := by
  have hd : 0 < Real.log b - Real.log a := sub_pos.mpr (Real.log_lt_log ha hab)
  have hla : Real.log a ≤ Real.log ‖z‖ := Real.log_le_log ha haz
  have hlb : Real.log ‖z‖ ≤ Real.log b := Real.log_le_log (ha.trans_le haz) hzb
  constructor
  · exact div_nonneg (sub_nonneg.mpr hla) hd.le
  · exact (div_le_one hd).mpr (sub_le_sub_right hlb _)

theorem annulusLog_weighted_mean (a b : ℝ) (z : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hR : R < ‖z‖) :
    weightedBallAverage (annulusLog a b) z r =
      annulusLog a b z * ∫ y : ℂ, meanWeight y := by
  have hU : IsOpen ({0}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
  have hh : HarmonicOnNhd (annulusLog a b) ({0}ᶜ : Set ℂ) := by
    intro w hw
    exact harmonicAt_annulusLog a b (by simpa using hw)
  have hball : closedBall z R ⊆ ({0}ᶜ : Set ℂ) := by
    intro w hw
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hz
    subst w
    have hn : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_left] using hw
    linarith
  apply weightedBallAverage_eq_of_harmonic hU hh.contDiffOn z hr hrR hball
  intro w hw
  exact (hh w (hball (closedBall_subset_closedBall hrR.le hw))).2.self_of_nhds

/-- The first logarithmic barrier value appearing in the cylinder argument. -/
theorem annulusLog_at_four_a {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : ‖z‖ = 4 * a) :
    annulusLog (2 * a) 1 z = Real.log 2 / Real.log (1 / (2 * a)) := by
  have h2a : (2 * a : ℝ) ≠ 0 := by positivity
  have ha0 := ha.ne'
  have hnum : Real.log (4 * a) - Real.log (2 * a) = Real.log 2 := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) ha0,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0]
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [h4]
    ring
  rw [annulusLog, hz, hnum, Real.log_div one_ne_zero h2a, Real.log_one]

theorem annulusLog_complement {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {z : ℂ} (hz : z ≠ 0) :
    1 - annulusLog a b z = Real.log (b / ‖z‖) / Real.log (b / a) := by
  have hb := ha.trans hab
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hd : Real.log b - Real.log a ≠ 0 := (sub_pos.mpr (Real.log_lt_log ha hab)).ne'
  rw [annulusLog, Real.log_div hb.ne' hn, Real.log_div hb.ne' ha.ne']
  field_simp
  ring

end OAI.Analysis.PDE.Concentration
