import Mathlib

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Metric
open scoped ContDiff Topology

def awayZeroBump (a : ℝ) (ha : 0 < a) : ContDiffBump (0 : ℂ) where
  rIn := a / 4
  rOut := a / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def awayZeroCutoff (a : ℝ) (ha : 0 < a) (z : ℂ) : ℝ := 1 - awayZeroBump a ha z

theorem contDiff_awayZeroCutoff (a : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (awayZeroCutoff a ha) :=
  contDiff_const.sub (awayZeroBump a ha).contDiff

theorem awayZeroCutoff_nonneg (a : ℝ) (ha : 0 < a) (z : ℂ) :
    0 ≤ awayZeroCutoff a ha z := sub_nonneg.mpr (awayZeroBump a ha).le_one

theorem awayZeroCutoff_eq_zero_near (a : ℝ) (ha : 0 < a) :
    awayZeroCutoff a ha =ᶠ[𝓝 (0 : ℂ)] 0 := by
  filter_upwards [(awayZeroBump a ha).eventuallyEq_one] with z hz
  simp only [awayZeroCutoff, hz, Pi.one_apply, sub_self, Pi.zero_apply]

theorem awayZeroCutoff_eq_one_near (a : ℝ) (ha : 0 < a) {z : ℂ} (hz : a ≤ ‖z‖) :
    awayZeroCutoff a ha =ᶠ[𝓝 z] 1 := by
  have hnorm : a / 2 < ‖z‖ := by linarith
  filter_upwards [continuous_norm.continuousAt.eventually (Ioi_mem_nhds hnorm)] with w hw
  have hb : awayZeroBump a ha w = 0 := (awayZeroBump a ha).zero_of_le_dist
    (by simpa only [dist_zero_right, awayZeroBump] using hw.le)
  simp only [awayZeroCutoff, hb, sub_zero, Pi.one_apply]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Remove only the irrelevant singular part `Y=0`, leaving the function
unchanged on a neighborhood of every point with `a≤|Y|`. -/
def awayZeroExtension (a : ℝ) (ha : 0 < a) (Y : E → ℂ) (f : E → F) : E → F :=
  fun x => awayZeroCutoff a ha (Y x) • f x

theorem contDiff_awayZeroExtension (a : ℝ) (ha : 0 < a) {Y : E → ℂ}
    (hY : ContDiff ℝ ∞ Y) {f : E → F}
    (hf : ∀ x, Y x ≠ 0 → ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (awayZeroExtension a ha Y f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : Y x = 0
  · apply (show ContDiffAt ℝ ∞ (fun _ : E => (0 : F)) x from contDiffAt_const).congr_of_eventuallyEq
    have hzero : Tendsto Y (𝓝 x) (𝓝 0) := by
      simpa only [ContinuousAt, hx] using (hY.continuous.continuousAt : ContinuousAt Y x)
    filter_upwards [(awayZeroCutoff_eq_zero_near a ha).comp_tendsto hzero] with y hy
    change awayZeroCutoff a ha (Y y) = 0 at hy
    simp only [awayZeroExtension, hy, zero_smul]
  · exact ((contDiff_awayZeroCutoff a ha).comp hY).contDiffAt.smul (hf x hx)

omit [NormedSpace ℝ E] in
theorem awayZeroExtension_eq_near (a : ℝ) (ha : 0 < a) {Y : E → ℂ}
    (hY : Continuous Y) (f : E → F) {x : E} (hx : a ≤ ‖Y x‖) :
    awayZeroExtension a ha Y f =ᶠ[𝓝 x] f := by
  filter_upwards [(awayZeroCutoff_eq_one_near a ha hx).comp_tendsto hY.continuousAt] with y hy
  change awayZeroCutoff a ha (Y y) = 1 at hy
  simp only [awayZeroExtension, hy, one_smul]

omit [NormedSpace ℝ E] in
theorem awayZeroExtension_periodic (a : ℝ) (ha : 0 < a) {Y : E → ℂ} {f : E → F} (p : E)
    (hY : ∀ x, Y (x + p) = Y x) (hf : ∀ x, f (x + p) = f x) (x : E) :
    awayZeroExtension a ha Y f (x + p) = awayZeroExtension a ha Y f x := by
  simp only [awayZeroExtension, hY, hf]

end OAI.Analysis.PDE.Concentration
