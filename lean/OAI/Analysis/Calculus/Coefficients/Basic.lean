import OAI.Analysis.PDE.Dirichlet.HolderApprox

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff Convolution
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Positive scalar mollification of a Banach-valued field. -/
def smoothField (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) : EuclideanSpace ℝ (Fin m) → F :=
  (φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

omit [CompleteSpace F] in
theorem smoothField_eq_integral (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (x : EuclideanSpace ℝ (Fin m)) :
    smoothField φ f x = ∫ y, φ.normed volume y • f (x-y) := rfl

omit [CompleteSpace F] in
theorem integrable_smoothField (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : Continuous f) (x : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun y ↦ φ.normed volume y • f (x-y)) :=
  φ.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.continuous_normed hf.locallyIntegrable x

omit [CompleteSpace F] in
theorem contDiff_smoothField (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : Continuous f) :
    ContDiff ℝ ∞ (smoothField φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed hf.locallyIntegrable

omit [CompleteSpace F] in
theorem smoothField_uniform_bound (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B)
    (x : EuclideanSpace ℝ (Fin m)) : ‖smoothField φ f x‖ ≤ B := by
  rw [smoothField_eq_integral]
  have h := norm_integral_le_of_norm_le (φ.integrable_normed.mul_const B)
    (Eventually.of_forall fun y ↦ show ‖φ.normed volume y • f (x-y)‖ ≤ φ.normed volume y * B from by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left (hf _) (φ.nonneg_normed y))
  simpa only [integral_mul_const,φ.integral_normed,one_mul] using h

omit [CompleteSpace F] in
theorem smoothField_holder (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : Continuous f) {H α : ℝ}
    (hh : ∀ x y, ‖f x-f y‖ ≤ H*‖x-y‖^α) (x z : EuclideanSpace ℝ (Fin m)) :
    ‖smoothField φ f x-smoothField φ f z‖ ≤ H*‖x-z‖^α := by
  rw [smoothField_eq_integral,smoothField_eq_integral,
    ←integral_sub (integrable_smoothField φ f hf x) (integrable_smoothField φ f hf z)]
  have hbound : ∀ᵐ y, ‖φ.normed volume y • f (x-y)-φ.normed volume y • f (z-y)‖ ≤
      φ.normed volume y*(H*‖x-z‖^α) := by
    filter_upwards with y
    rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed y)]
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed y)
    have he : x-y-(z-y)=x-z := by abel
    simpa only [he] using hh (x-y) (z-y)
  have hb := norm_integral_le_of_norm_le (φ.integrable_normed.mul_const (H*‖x-z‖^α)) hbound
  simpa only [integral_mul_const,φ.integral_normed,one_mul] using hb

theorem smoothField_error (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : Continuous f) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 ≤ α) (hh : ∀ x y, ‖f x-f y‖ ≤ H*‖x-y‖^α)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖smoothField φ f x-f x‖ ≤ H*φ.rOut^α := by
  have h := φ.dist_normed_convolution_le (μ := volume) hf.aestronglyMeasurable
    (x₀ := x) (ε := H*φ.rOut^α) (fun y hy ↦ ?_)
  · simpa only [smoothField,dist_eq_norm] using h
  · rw [dist_eq_norm]
    exact (hh y x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by simpa only [Metric.mem_ball,dist_eq_norm] using hy.le) hα) hH)

theorem smoothField_tendstoUniformly
    (f : EuclideanSpace ℝ (Fin m) → F) (hf : Continuous f) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α) (hh : ∀ x y, ‖f x-f y‖ ≤ H*‖x-y‖^α) :
    TendstoUniformly (fun j ↦ smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f) f atTop := by
  have ht : Tendsto (fun j ↦ H*(OAI.Analysis.PDE.Schauder.standardMollifier m j).rOut^α) atTop (𝓝 0) := by
    simpa using ((OAI.Analysis.PDE.Schauder.standardMollifier_radius_tendsto m).rpow_const_nhds_zero hα).const_mul H
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [ht (Iio_mem_nhds hε)] with j hj
  intro x
  have hlt := (smoothField_error (OAI.Analysis.PDE.Schauder.standardMollifier m j) f hf hH hα.le hh x).trans_lt hj
  simpa only [dist_eq_norm,norm_sub_rev] using hlt

end OAI.Analysis.Calculus.Coefficients
