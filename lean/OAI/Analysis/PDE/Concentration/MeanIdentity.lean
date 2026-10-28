import OAI.Analysis.PDE.Concentration.MeanKernel

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set InnerProductSpace Laplacian
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- A radial weighted mean identity, obtained by actual integration by parts.
Its positive compact potential turns the sign of the Laplacian into the
monotonicity of local spatial averages. -/
theorem integral_mean_radial_derivative {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    (∫ x, meanWeight x * fderiv ℝ f x x) = ∫ x, meanPotential x * Δ f x := by
  let v := stdOrthonormalBasis ℝ E
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hD (i) : ContDiff ℝ 1 (fun x => fderiv ℝ f x (v i)) :=
    hdf.clm_apply contDiff_const
  have hDD (i) : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ f y (v i)) x (v i)) :=
    ((hD i).fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuous.clm_apply
      continuous_const
  have hL (i) : Integrable (fun x => meanWeight x * ⟪x, v i⟫_ℝ * fderiv ℝ f x (v i)) :=
    ((contDiff_meanWeight.continuous.mul (continuous_id.inner continuous_const)).mul
      (hD i).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_meanWeight.mul_right.mul_right)
  have hR (i) : Integrable (fun x => meanPotential x *
      fderiv ℝ (fun y => fderiv ℝ f y (v i)) x (v i)) :=
    (contDiff_meanPotential.continuous.mul (hDD i)).integrable_of_hasCompactSupport
      hasCompactSupport_meanPotential.mul_right
  have hIBP (i) :
      (∫ x, meanWeight x * ⟪x, v i⟫_ℝ * fderiv ℝ f x (v i)) =
        ∫ x, meanPotential x * fderiv ℝ (fun y => fderiv ℝ f y (v i)) x (v i) := by
    have hpD : Continuous (fun x : E => fderiv ℝ meanPotential x (v i)) :=
      (contDiff_meanPotential.fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ ∞ by simp)).continuous.clm_apply
        continuous_const
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure E))
      ((hpD.mul (hD i).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_meanPotential.fderiv_apply ℝ (v i)).mul_right)
      (hR i)
      ((contDiff_meanPotential.continuous.mul (hD i).continuous).integrable_of_hasCompactSupport
        hasCompactSupport_meanPotential.mul_right)
      (fun x _ => contDiff_meanPotential.differentiable (by simp) x)
      (fun x _ => (hD i).differentiable (by norm_num) x)
    simp_rw [fderiv_meanPotential, neg_mul, integral_neg, neg_neg] at hh
    exact hh.symm
  have he (x : E) : meanWeight x * fderiv ℝ f x x =
      ∑ i, meanWeight x * ⟪x, v i⟫_ℝ * fderiv ℝ f x (v i) := by
    have hsum := congrArg (fderiv ℝ f x) (v.sum_repr' x)
    simp only [map_sum, map_smul, smul_eq_mul] at hsum
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm]
    ring
  have hΔ (x : E) : meanPotential x * Δ f x =
      ∑ i, meanPotential x * fderiv ℝ (fun y => fderiv ℝ f y (v i)) x (v i) := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f v, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [second_directional_eq_hessian hf]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [he, hΔ]
  rw [integral_finsetSum _ (fun i _ => hL i), integral_finsetSum _ (fun i _ => hR i)]
  exact Finset.sum_congr rfl (fun i _ => hIBP i)

omit [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
theorem laplacian_affine_dilate {f : E → ℝ} (hf : ContDiff ℝ 2 f) (a : E) (r : ℝ) (x : E) :
    Δ (fun y => f (a + r • y)) x = r ^ 2 * Δ f (a + r • x) := by
  have hg : ContDiff ℝ 2 (fun y => f (a + y)) := hf.comp (contDiff_const.add contDiff_id)
  have hh := iteratedFDeriv_comp_const_smul r hg
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  rw [show (fun y => f (a + r • y)) = (fun y => (fun z => f (a + z)) (r • y)) from rfl, hh]
  simp only [iteratedFDeriv_comp_add_left, smul_apply, smul_eq_mul,
    Finset.mul_sum]

theorem mean_radial_derivative_nonpos {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hΔ : ∀ x ∈ Metric.closedBall (0 : E) 1, Δ f x ≤ 0) :
    (∫ x, meanWeight x * fderiv ℝ f x x) ≤ 0 := by
  rw [integral_mean_radial_derivative hf]
  apply integral_nonpos
  intro x
  change meanPotential x * Δ f x ≤ 0
  by_cases hx : x ∈ Metric.closedBall (0 : E) 1
  · exact mul_nonpos_of_nonneg_of_nonpos (meanPotential_nonneg x) (hΔ x hx)
  · have hn : 1 < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    rw [meanPotential_zero hn.le, zero_mul]

end OAI.Analysis.PDE.Concentration
