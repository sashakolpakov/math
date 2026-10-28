import OAI.Analysis.PDE.Schauder.Calculus.Schauder.FarConvolution

/-! The exponent-preserving derivative estimate for the far convolution. -/

noncomputable section
open _root_.MeasureTheory
namespace OAI.Analysis.PDE.Schauder

theorem farConvolution_fderiv_bound {m : ℕ} (hm : 1 ≤ m) (v w : EuclideanSpace ℝ (Fin m)) :
    ∃ C > 0, ∀ (r α H : ℝ), 0 < r → α < 1 → 0 ≤ H →
      ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ x, (∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α) →
      ‖fderiv ℝ (scalarConvolution (truncatedNewtonianEntry m v w r) f) x‖ ≤
        H * C * (r / 2) ^ (α - 1) * rieszTailMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α := by
  obtain ⟨C, hC, hbound⟩ := truncatedNewtonianEntry_weighted_fderiv v w
  refine ⟨C, hC, ?_⟩
  intro r α H hr hα hH f hf hfc x hh
  have hi0 := hbound r α volume inferInstance (by simpa using hm) hr hα
  simp only [finrank_euclideanSpace_fin] at hi0
  have hT := rieszTailMass_nonneg (volume : Measure (EuclideanSpace ℝ (Fin m))) α
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [fderiv_farConvolution_compensated hm v w hr f hf hfc x u]
  have hb : ∀ y, ‖fderiv ℝ (truncatedNewtonianEntry m v w r) y u * (f (x - y) - f x)‖ ≤
      (H * ‖u‖) * (‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖ * ‖y‖ ^ α) := by
    intro y
    rw [norm_mul, Real.norm_eq_abs (f (x - y) - f x)]
    calc
      _ ≤ (‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖ * ‖u‖) * (H * ‖y‖ ^ α) :=
        mul_le_mul ((fderiv ℝ (truncatedNewtonianEntry m v w r) y).le_opNorm u)
          (hh y) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫ y, (H * ‖u‖) * (‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖ * ‖y‖ ^ α) :=
      norm_integral_le_of_norm_le (hi0.1.const_mul _) (Filter.Eventually.of_forall hb)
    _ = (H * ‖u‖) * ∫ y, ‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖ * ‖y‖ ^ α :=
      integral_const_mul _ _
    _ ≤ (H * ‖u‖) * (C * (r / 2) ^ (α - 1) * rieszTailMass volume α) :=
      mul_le_mul_of_nonneg_left hi0.2 (by positivity)
    _ = _ := by ring

end OAI.Analysis.PDE.Schauder
