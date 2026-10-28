import Mathlib

/-! Genuine integration by parts for compactly supported test functions.
These lemmas use Haar integration, rather than postulating a Green identity. -/

noncomputable section

namespace OAI.Analysis.PDE.Green

open _root_.MeasureTheory Measure
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_directional {u : E → ℝ} (hu : ContDiff ℝ 1 u) (d : E) :
    Continuous (fun x ↦ fderiv ℝ u x d) :=
  (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- Integration by parts against one compactly supported `C¹` test. The
other function need not have compact support. -/
theorem integral_directional_by_parts {u v : E → ℝ}
    (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v)
    (hs : HasCompactSupport u) (d : E) :
    (∫ x, u x * fderiv ℝ v x d ∂μ) =
      -(∫ x, fderiv ℝ u x d * v x ∂μ) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((continuous_directional hu d).mul hv.continuous).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ d).mul_right
  · exact (hu.continuous.mul (continuous_directional hv d)).integrable_of_hasCompactSupport
      hs.mul_right
  · exact (hu.continuous.mul hv.continuous).integrable_of_hasCompactSupport hs.mul_right
  · intro x _
    exact hu.differentiable (by norm_num) x
  · intro x _
    exact hv.differentiable (by norm_num) x

/-- The divergence form of the same identity, for any finite collection of
constant directions. -/
theorem integral_divergence_by_parts {I : Type*} [Fintype I]
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (d : I → E) (F : I → E → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i)) :
    (∫ x, u x * (∑ i, fderiv ℝ (F i) x (d i)) ∂μ) =
      -(∫ x, ∑ i, fderiv ℝ u x (d i) * F i x ∂μ) := by
  have hleft (i : I) : Integrable (fun x ↦ u x * fderiv ℝ (F i) x (d i)) μ :=
    (hu.continuous.mul (continuous_directional (hF i) (d i))).integrable_of_hasCompactSupport
      hs.mul_right
  have hright (i : I) : Integrable (fun x ↦ fderiv ℝ u x (d i) * F i x) μ :=
    ((continuous_directional hu (d i)).mul (hF i).continuous).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ (d i)).mul_right
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hleft i), integral_finsetSum _ (fun i _ ↦ hright i)]
  simp_rw [integral_directional_by_parts hu (hF _) hs]
  exact Finset.sum_neg_distrib _

end OAI.Analysis.PDE.Green
