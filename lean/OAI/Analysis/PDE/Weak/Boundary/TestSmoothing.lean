import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import OAI.Analysis.PDE.Weak.Boundary.Weak.Division

/-! Smooth approximation of compactly supported C¹ tests, including their
actual directional derivatives.  These lemmas use normalized convolution,
not an assumed density principle. -/

noncomputable section
open Set Filter _root_.MeasureTheory ContinuousLinearMap
open scoped ContDiff Convolution Topology
namespace OAI.Analysis.PDE.Weak

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def testBump (n : ℕ) : ContDiffBump (0 : X) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := half_pos (by positivity)
  rIn_lt_rOut := half_lt_self (by positivity)

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
theorem testBump_radius_tendsto :
    Tendsto (fun n => (testBump (X := X) n).rOut) atTop (𝓝 0) := by
  simpa only [testBump] using tendsto_one_div_add_atTop_nhds_zero_nat

def smoothTestApprox (μ : Measure X) (φ : X → F) (n : ℕ) : X → F :=
  ((testBump n).normed μ ⋆[lsmul ℝ ℝ, μ] φ)

variable (μ : Measure X) [μ.IsAddHaarMeasure]

omit [CompleteSpace F] in
theorem smoothTestApprox_contDiff {φ : X → F} (hφ : Continuous φ) (n : ℕ) :
    ContDiff ℝ ∞ (smoothTestApprox μ φ n) :=
  (testBump n).hasCompactSupport_normed.contDiff_convolution_left _
    (testBump n).contDiff_normed hφ.locallyIntegrable

theorem smoothTestApprox_tendsto {φ : X → F} (hφ : Continuous φ) (x : X) :
    Tendsto (fun n => smoothTestApprox μ φ n x) atTop (𝓝 (φ x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous testBump_radius_tendsto hφ x

omit [CompleteSpace F] in
theorem smoothTestApprox_derivative {φ : X → F} (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (n : ℕ) (x w : X) :
    fderiv ℝ (smoothTestApprox μ φ n) x w =
      smoothTestApprox μ (fun y => fderiv ℝ φ y w) n x := by
  unfold smoothTestApprox
  rw [(hs.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
    ((testBump n).contDiff_normed (μ := μ) (n := 1)).continuous.locallyIntegrable hφ x).fderiv]
  exact convolution_precompR_apply (lsmul ℝ ℝ)
    ((testBump n).contDiff_normed (μ := μ) (n := 1)).continuous.locallyIntegrable (hs.fderiv ℝ)
    (hφ.continuous_fderiv one_ne_zero) x w

theorem smoothTestApprox_derivative_tendsto {φ : X → F} (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (x w : X) :
    Tendsto (fun n => fderiv ℝ (smoothTestApprox μ φ n) x w) atTop
      (𝓝 (fderiv ℝ φ x w)) := by
  simp_rw [smoothTestApprox_derivative μ hφ hs]
  exact smoothTestApprox_tendsto μ
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const) x

theorem smoothTestApprox_norm_le {φ : X → F} (hφ : Continuous φ)
    {B : ℝ} (hB : ∀ x, ‖φ x‖ ≤ B) (n : ℕ) (x : X) :
    ‖smoothTestApprox μ φ n x‖ ≤ 3 * B := by
  have hd : dist (smoothTestApprox μ φ n x) (φ x) ≤ 2 * B := by
    apply (testBump n).dist_normed_convolution_le hφ.aestronglyMeasurable
    intro y _
    calc
      dist (φ y) (φ x) ≤ ‖φ y‖ + ‖φ x‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * B := by linarith [hB y, hB x]
  calc
    ‖smoothTestApprox μ φ n x‖ ≤ dist (smoothTestApprox μ φ n x) (φ x) + ‖φ x‖ :=
      by simpa only [dist_zero_right] using dist_triangle (smoothTestApprox μ φ n x) (φ x) 0
    _ ≤ 3 * B := by linarith [hB x]

end OAI.Analysis.PDE.Weak
