import OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange

/-! # Vector Sobolev Membership -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.VectorSobolevMembership

noncomputable section

/-! The original vector Sobolev embedding realizes genuine H¹ distributions. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap

open OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vectorSobolevEmbedding_memSobolev (v : Lp F 2 (volume : Measure E)) :
    MemSobolev 1 2 ((ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
  rw [ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff, neg_add_cancel]
  exact memSobolev_zero_iff.mpr ⟨v, rfl⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.VectorSobolevMembership
