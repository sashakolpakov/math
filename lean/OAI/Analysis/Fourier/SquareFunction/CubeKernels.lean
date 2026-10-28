import OAI.Analysis.Fourier.SquareFunction.CubeGeometry
import OAI.Analysis.Fourier.SquareFunction.ConvolutionRegularity

open OAI.Analysis.Fourier.Wave

/-! The low and off-diagonal high estimates on the actual cubes used in the
sharp-function argument. All geometry is discharged here. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set Metric
open scoped ENNReal

theorem low_convolution_on_cube {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (Q : BoxIntegral.Box (Fin n)) {s a q C : ℝ}
    (hs : 0 < s) (hside : ∀ i, Q.upper i - Q.lower i = s)
    (ha : 0 < a) (hq : 0 < q) (hC : 0 ≤ C)
    (has : a * (2 * (n : ℝ) * s) ≤ 1)
    {K : Space n → H} (hKd : Differentiable ℝ K)
    (hK : ∀ u, ‖fderiv ℝ K u‖ ≤ C * (a ^ n * a) * (a * ‖u‖ + 1) ^ (-q))
    (hB : BddAbove (range fun x => ‖K x‖))
    {f : Space n → ℂ} (hfm : Measurable f) (hfi : Integrable f)
    {x z : Space n} (hx : x ∈ euclideanBox Q) (hz : z ∈ euclideanBox Q) :
    ‖convolveKernel K f x - convolveKernel K f (cubeCorner Q)‖ₑ ≤
      ENNReal.ofReal (C * 2 ^ q * a * ((n : ℝ) * s)) *
        (polynomialKernelMass n q * ballMaximal volume (fun y => ‖f y‖ₑ) z) := by
  have hxz : a * dist x z ≤ 1 :=
    (mul_le_mul_of_nonneg_left (dist_le_cube_diameter Q hs.le hside hx hz) ha.le).trans has
  have hcz : a * dist (cubeCorner Q) z ≤ 1 := by
    rw [dist_comm]
    apply (mul_le_mul_of_nonneg_left (dist_cubeCorner_le Q hs.le hside hz) ha.le).trans
    have hns : 0 ≤ (n : ℝ) * s := mul_nonneg (Nat.cast_nonneg n) hs.le
    nlinarith
  have h := convolution_variation_le_maximal ha hq hC hKd hK hfm hxz hcz
    (integrable_convolveKernel_integrand hfi hKd.continuous hB x)
    (integrable_convolveKernel_integrand hfi hKd.continuous hB (cubeCorner Q))
  refine h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  exact mul_le_mul_of_nonneg_left (dist_cubeCorner_le Q hs.le hside hx) (by positivity)

theorem tail_convolution_on_cube {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (Q : BoxIntegral.Box (Fin n)) {s a q r C : ℝ}
    (hs : 0 < s) (hside : ∀ i, Q.upper i - Q.lower i = s)
    (ha : 0 < a) (hr : 0 < r) (hqr : r ≤ q) (hC : 0 ≤ C)
    {K : Space n → H}
    (hK : ∀ u, ‖K u‖ ≤ C * a ^ n * (a * ‖u‖ + 1) ^ (-q))
    {f : Space n → ℂ} (hf : Measurable f)
    {x z : Space n} (hx : x ∈ euclideanBox Q) (hz : z ∈ euclideanBox Q) :
    ‖convolveKernel K ((ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * s)))ᶜ.indicator f) x‖ₑ ≤
      ENNReal.ofReal (C * 2 ^ q * (a * (4 * (((n : ℝ) + 1) * s))) ^ (r - q)) *
        (polynomialKernelMass n r * ballMaximal volume (fun y => ‖f y‖ₑ) z) := by
  let P := ball (cubeCorner Q) (8 * (((n : ℝ) + 1) * s))
  have hP : MeasurableSet P := isOpen_ball.measurableSet
  have hxz : dist x z ≤ (4 * (((n : ℝ) + 1) * s)) / 2 :=
    (dist_le_cube_diameter Q hs.le hside hx hz).trans (by nlinarith)
  have h := tail_convolution_le_maximal ha (by positivity : 0 < 4 * (((n : ℝ) + 1) * s))
    hr hqr hC hK (hf.indicator hP.compl) hxz
    (fun y hy => complement_enlarged_ball_vanishes Q hs hside hz f hy)
  apply h.trans
  apply mul_le_mul_right
  apply mul_le_mul_right
  apply ballMaximal_mono
  intro y
  by_cases hy : y ∈ Pᶜ
  · simp only [indicator_of_mem hy]
    exact le_rfl
  · simp only [indicator_of_notMem hy, enorm_zero]
    exact bot_le

end OAI.Analysis.Fourier.SquareFunction
