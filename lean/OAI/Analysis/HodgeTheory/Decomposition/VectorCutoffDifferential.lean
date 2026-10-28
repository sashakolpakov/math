import OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffOperator
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential

/-! # Vector Cutoff Differential -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffDifferential.Constructions

noncomputable section

/-! Genuine vector-valued Sobolev cutoff multiplication and its weak derivative. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vectorSobolevCutoffCLM_embedding (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E)) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := F) (μ := (volume : Measure E)) (p := 2)))
  change (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) : 𝓢'(E, F)) =
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) : 𝓢'(E, F))
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_distribution, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding_distribution]
  simpa only [Nat.cast_one, VectorCutoffOperator.Constructions.vectorSobolevDistributionCLM, ContinuousLinearMap.comp_apply,
    Lp.toTemperedDistributionCLM_apply] using VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM_distribution 1 g u

theorem vectorSobolevCutoffCLM_derivative (g : 𝓢(E, ℂ)) (m : E) (u : Lp F 2 (volume : Measure E)) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{m} g : 𝓢(E, ℂ))
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) +
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m u) := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := F) (μ := (volume : Measure E)) (p := 2)))
  change (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) : 𝓢'(E, F)) =
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{m} g : 𝓢(E, ℂ))
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) +
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative m u) : Lp F 2 volume) : 𝓢'(E, F))
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution, vectorSobolevCutoffCLM_embedding,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_distribution, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.distribution_cutoff_leibniz]
  have hadd (v w : Lp F 2 (volume : Measure E)) :
      ((v + w : Lp F 2 volume) : 𝓢'(E, F)) = (v : 𝓢'(E, F)) + (w : 𝓢'(E, F)) := by
    simpa only [Lp.toTemperedDistributionCLM_apply] using
      (Lp.toTemperedDistributionCLM F (volume : Measure E) 2).map_add v w
  rw [hadd, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_distribution, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_distribution,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution]

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffDifferential.Constructions
