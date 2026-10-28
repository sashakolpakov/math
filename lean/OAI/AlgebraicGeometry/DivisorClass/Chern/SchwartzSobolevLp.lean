import OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange

/-! # Schwartz Sobolev Lp -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzSobolevLp

noncomputable section

/-! The actual L² representative of a Schwartz field has every Sobolev order. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem schwartz_toLp_memSobolev (s : ℝ) (q : 𝓢(E, F)) :
    MemSobolev s 2 (q.toLp 2 volume : 𝓢'(E, F)) := by
  rw [Lp.toTemperedDistribution_toLp_eq]
  exact q.memSobolev

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzSobolevLp
