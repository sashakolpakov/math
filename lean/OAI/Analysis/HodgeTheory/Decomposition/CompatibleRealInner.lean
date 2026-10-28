import OAI.Analysis.HodgeTheory.Decomposition.ComplexMetric

/-! # Compatible Real Inner -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CompatibleRealInner.Constructions

noncomputable section

/-! Real and complex Hilbert structures with the same norm have the same
real inner product; their genuine adjoints therefore agree under restriction. -/

theorem compatible_real_inner {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [InnerProductSpace ℝ F] (u v : F) :
    inner ℝ u v = (inner ℂ u v).re := by
  have hr := norm_sub_sq_real u v
  have hc := norm_sub_sq (𝕜 := ℂ) u v
  change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * (inner ℂ u v).re + ‖v‖ ^ 2 at hc
  linarith

theorem compatible_adjoint_restrictScalars {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
    [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [InnerProductSpace ℝ G]
    [IsScalarTower ℝ ℂ G] [CompleteSpace G] (A : F →L[ℂ] G) :
    (A.restrictScalars ℝ).adjoint = A.adjoint.restrictScalars ℝ := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ u (A v) = inner ℝ (A.adjoint u) v
  rw [compatible_real_inner, compatible_real_inner, ContinuousLinearMap.adjoint_inner_left]

end

end OAI.Analysis.HodgeTheory.Decomposition.CompatibleRealInner.Constructions
