import OAI.Analysis.Fourier.Radial.Sphere.ODE
import OAI.Analysis.Fourier.Radial.Bessel
import OAI.MeasureTheory.Kakeya.Hausdorff

open OAI.Analysis.Fourier.Wave

/-! Nonzero leading oscillations of the actual sphere Fourier kernel. -/

open _root_.MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem axisSphereCosineKernel_one_pos {n : ℕ} (hn : 1 ≤ n)
    {v : Space n} (hv : ‖v‖ = 1) : 0 < axisSphereCosineKernel v 1 := by
  have hm : 0 < (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real univ := by
    exact ENNReal.toReal_pos (OAI.MeasureTheory.Kakeya.sphereMeasure_univ_pos hn).ne'
      (measure_ne_top _ _)
  have hb : ∀ᵐ ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n,
      (1 / 2 : ℝ) ≤ Real.cos (inner ℝ v ω) := by
    filter_upwards [ae_sphere_inner_bound v] with ω hω
    rw [hv] at hω
    have hsq : (inner ℝ v ω) ^ 2 ≤ 1 := by
      have := sq_le_sq₀ (abs_nonneg (inner ℝ v ω)) zero_le_one |>.mpr hω
      simpa only [sq_abs, one_pow] using this
    linarith [Real.one_sub_sq_div_two_le_cos (x := inner ℝ v ω)]
  have H := integral_mono_ae (integrable_const (μ := OAI.Analysis.Fourier.Restriction.sphereMeasure n)
    (1 / 2 : ℝ)) (integrable_sphere_cosine v) hb
  have hl : (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real univ / 2 ≤ sphereCosineKernel v := by
    simpa only [sphereCosineKernel, integral_const, smul_eq_mul, div_eq_mul_inv, one_mul] using H
  simpa only [axisSphereCosineKernel, one_smul] using (half_pos hm).trans_le hl

theorem sphereCosine_axis_asymptotic {n : ℕ} (hn : 1 ≤ n)
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) (i : Fin n) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ r, 1 ≤ r →
      |r ^ (((n : ℝ) - 1) / 2) * axisSphereCosineKernel (b i) r -
        (A * Real.cos r + B * Real.sin r)| ≤ C / r ∧
      |r ^ (((n : ℝ) - 1) / 2) * sphereCosineLineDeriv 0 (b i) r +
        (((n : ℝ) - 1) / 2) * r ^ (((n : ℝ) - 1) / 2 - 1) *
          axisSphereCosineKernel (b i) r -
        (-A * Real.sin r + B * Real.cos r)| ≤ C / r := by
  apply bessel_normalized_asymptotic
    (fun t _ => hasDerivAt_axisSphereCosineKernel (b i) t)
  · intro t ht
    convert hasDerivAt_sphereCosine_bessel b i (by linarith : 0 < t) using 1
    ring
  · exact Or.inl (axisSphereCosineKernel_one_pos hn (b.norm_eq_one i)).ne'

theorem sphereCosine_radial_asymptotic {n : ℕ} (hn : 1 ≤ n) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ x : Space n, 1 ≤ ‖x‖ →
      |‖x‖ ^ (((n : ℝ) - 1) / 2) * sphereCosineKernel x -
        (A * Real.cos ‖x‖ + B * Real.sin ‖x‖)| ≤ C / ‖x‖ := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let i : Fin n := ⟨0, by omega⟩
  obtain ⟨A, B, C, hC, hAB, h⟩ := sphereCosine_axis_asymptotic hn b i
  refine ⟨A, B, C, hC, hAB, fun x hx => ?_⟩
  rw [sphereCosineKernel_radial (b.norm_eq_one i)]
  exact (h ‖x‖ hx).1

end OAI.Analysis.Fourier.Radial
