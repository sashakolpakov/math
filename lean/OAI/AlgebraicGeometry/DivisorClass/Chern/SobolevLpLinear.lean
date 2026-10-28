import OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange

/-! # Sobolev Lp Linear -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SobolevLpLinear

noncomputable section

/-! Addition, subtraction and negation of the actual L² representatives preserve Sobolev membership. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap
open OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem lp_memSobolev_sub {s : ℝ} (a b : Lp F 2 (volume : Measure E))
    (ha : MemSobolev s 2 (a : 𝓢'(E, F))) (hb : MemSobolev s 2 (b : 𝓢'(E, F))) :
    MemSobolev s 2 ((a - b : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
  rw [← Lp.toTemperedDistributionCLM_apply, map_sub]
  exact ha.sub hb

theorem lp_memSobolev_neg {s : ℝ} (a : Lp F 2 (volume : Measure E))
    (ha : MemSobolev s 2 (a : 𝓢'(E, F))) :
    MemSobolev s 2 ((-a : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
  rw [← Lp.toTemperedDistributionCLM_apply, map_neg]
  exact ha.neg

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SobolevLpLinear
