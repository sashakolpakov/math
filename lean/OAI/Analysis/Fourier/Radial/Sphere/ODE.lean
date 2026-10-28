import OAI.Analysis.Fourier.Radial.Sphere.Transverse

open OAI.Analysis.Fourier.Wave

/-! The Bessel equation for the exact Fourier transform of surface measure. -/

open _root_.MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem integrable_sphereCosine_second {n : ℕ} (x v : Space n) :
    Integrable (fun ω => -(inner ℝ v ω) ^ 2 * Real.cos (inner ℝ x ω))
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  apply (integrable_const (μ := OAI.Analysis.Fourier.Restriction.sphereMeasure n) (‖v‖ ^ 2)).mono'
    (by fun_prop)
  filter_upwards [ae_sphere_inner_bound v] with ω hω
  simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_pow]
  calc
    _ ≤ ‖v‖ ^ 2 * 1 := mul_le_mul (by gcongr) (Real.abs_cos_le_one _)
      (abs_nonneg _) (sq_nonneg _)
    _ = _ := mul_one _

theorem sum_sphereCosineLineSecond {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) (x : Space n) :
    ∑ j, sphereCosineLineSecond x (b j) 0 = -sphereCosineKernel x := by
  simp only [sphereCosineLineSecond, zero_smul, add_zero]
  rw [← MeasureTheory.integral_finsetSum _ (fun j _ => integrable_sphereCosine_second x (b j))]
  calc
    _ = ∫ ω, -Real.cos (inner ℝ x ω) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n := by
      apply integral_congr_ae
      filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with ω hω
      rw [← Finset.sum_mul, Finset.sum_neg_distrib, b.sum_sq_inner_right, hω]
      ring
    _ = -sphereCosineKernel x := integral_neg _

theorem sphereCosineLineSecond_axis {n : ℕ} (v : Space n) (r : ℝ) :
    sphereCosineLineSecond (r • v) v 0 = sphereCosineLineSecond 0 v r := by
  simp only [sphereCosineLineSecond, zero_smul, add_zero, zero_add]

theorem sphereCosine_bessel_equation {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) (i : Fin n)
    {r : ℝ} (hr : 0 < r) :
    sphereCosineLineSecond 0 (b i) r =
      -((n : ℝ) - 1) / r * sphereCosineLineDeriv 0 (b i) r -
        axisSphereCosineKernel (b i) r := by
  have H := sum_sphereCosineLineSecond b (r • b i)
  have heq (j : Fin n) : sphereCosineLineSecond (r • b i) (b j) 0 =
      sphereCosineLineDeriv 0 (b i) r / r +
        if j = i then sphereCosineLineSecond 0 (b i) r -
          sphereCosineLineDeriv 0 (b i) r / r else 0 := by
    by_cases hji : j = i
    · subst j
      rw [sphereCosineLineSecond_axis, ite_eq_left rfl]
      ring
    · rw [ite_eq_right hji, add_zero]
      exact sphereCosine_transverse_second (b.norm_eq_one i) (b.norm_eq_one j)
        (b.inner_eq_zero (Ne.symm hji)) hr
  simp_rw [heq] at H
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at H
  change _ = -axisSphereCosineKernel (b i) r at H
  linear_combination H

theorem hasDerivAt_sphereCosine_bessel {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (Space n)) (i : Fin n)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (sphereCosineLineDeriv 0 (b i))
      (-((n : ℝ) - 1) / r * sphereCosineLineDeriv 0 (b i) r -
        axisSphereCosineKernel (b i) r) r := by
  rw [← sphereCosine_bessel_equation b i hr]
  exact hasDerivAt_sphereCosineLineDeriv 0 (b i) r

end OAI.Analysis.Fourier.Radial
