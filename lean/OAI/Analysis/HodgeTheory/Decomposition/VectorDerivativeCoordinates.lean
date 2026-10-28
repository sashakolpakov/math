import OAI.Analysis.HodgeTheory.Decomposition.VectorDifferenceConvergence
import OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange

/-! # Vector Derivative Coordinates -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorDerivativeCoordinates.Constructions

noncomputable section

/-! An actual vector H² function has H¹ coordinates for its first
derivative, and its spatial differences converge in those coordinates. -/

open _root_.MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vector_h2_coordinate_is_h1 (u : Lp F 2 (volume : Measure E))
    (hu : MemSobolev 2 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F))) :
    MemSobolev 1 2 (u : 𝓢'(E, F)) := by
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff] at hu
  norm_num only [neg_add_cancel_left] at hu
  exact hu

variable [InnerProductSpace ℝ F]

theorem vector_h2_difference_tendsto_h1_derivative (m : E) (u : Lp F 2 (volume : Measure E))
    (hu : MemSobolev 2 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F))) :
    ∃ v : Lp F 2 (volume : Measure E),
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m u ∧
      Tendsto (fun t : ℝ => VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u) (𝓝[≠] 0) (𝓝 v) := by
  obtain ⟨w, hw⟩ := (VectorEmbeddingRange.Constructions.vectorMemSobolev_l2_iff_embedding_range (by norm_num : (0 : ℝ) ≤ 1) u).mp
    (vector_h2_coordinate_is_h1 u hu)
  have hv := VectorDifferenceConvergence.Constructions.vectorL2DifferenceQuotient_tendsto_derivative m w
  rw [hw] at hv
  refine ⟨AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m w, ?_, hv⟩
  let J := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := F) (by norm_num : (0 : ℝ) ≤ 1)
  have hJ := (J.continuous.tendsto (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m w)).comp hv
  have hfun : (fun t : ℝ => J (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u)) =
      (fun t : ℝ => VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (J u)) := by
    funext t
    exact (VectorDifferenceBounds.Constructions.vectorL2DifferenceQuotient_sobolevEmbedding_comm m t (by norm_num : (0 : ℝ) ≤ 1) u).symm
  change Tendsto (fun t : ℝ => J (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u)) (𝓝[≠] 0)
    (𝓝 (J (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m w))) at hJ
  rw [hfun] at hJ
  exact tendsto_nhds_unique hJ (VectorDifferenceConvergence.Constructions.vectorL2DifferenceQuotient_tendsto_derivative m u)

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorDerivativeCoordinates.Constructions
