import OAI.Analysis.HodgeTheory.Decomposition.EnergyDomain

/-! # Graph Norm -/

namespace OAI.Analysis.HodgeTheory.Decomposition.GraphNorm.Constructions

noncomputable section

/-! Elementary comparisons between the actual graph norm and its three
genuine L² components. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

theorem projectiveGraphEmbedding_component_bounds
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    ‖Form.Constructions.smoothToProjectiveL2 V (n + 1) a‖ ≤ ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ∧
      ‖Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)‖ ≤ ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ∧
      ‖Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a)‖ ≤ ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ := by
  have he := EnergyDomain.Constructions.projectiveGraphEmbedding_norm_sq V n a
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    exact EnergyDomain.Constructions.projectiveGraphEmbedding_value_norm_sq_le V n a
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith only [he, sq_nonneg ‖Form.Constructions.smoothToProjectiveL2 V (n + 1) a‖,
      sq_nonneg ‖Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a)‖]
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith only [he, sq_nonneg ‖Form.Constructions.smoothToProjectiveL2 V (n + 1) a‖,
      sq_nonneg ‖Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)‖]

theorem projectiveGraphEmbedding_norm_le_sum
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ ≤ ‖Form.Constructions.smoothToProjectiveL2 V (n + 1) a‖ +
      ‖Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)‖ +
      ‖Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EnergyDomain.Constructions.projectiveGraphEmbedding_norm_sq]
  nlinarith only [
    mul_nonneg (norm_nonneg (Form.Constructions.smoothToProjectiveL2 V (n + 1) a))
      (norm_nonneg (Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a))),
    mul_nonneg (norm_nonneg (Form.Constructions.smoothToProjectiveL2 V (n + 1) a))
      (norm_nonneg (Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a))),
    mul_nonneg (norm_nonneg (Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)))
      (norm_nonneg (Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a)))]

end

end OAI.Analysis.HodgeTheory.Decomposition.GraphNorm.Constructions
