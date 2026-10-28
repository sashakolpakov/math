import OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffInsertion
import OAI.Analysis.HodgeTheory.Decomposition.VectorStrongCutoff

/-! # Vector Strong Cutoff Gradient -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorStrongCutoffGradient.Constructions

noncomputable section

/-! The actual vector cutoff-gradient commutator and its Hilbert adjoint
preserve every order of genuine strong Sobolev regularity. -/

open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem vectorStrongSobolev_cutoffGradient (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E))
    (hu : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g u) := by
  rw [VectorCutoffInsertion.Constructions.vectorCutoffGradientMultiply_sum]
  apply AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators.CM.Construction.strongSobolev_finset_sum b n Finset.univ
  intro i _
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolevAdjoints.CM.Construction.strongSobolev_compLpL b (VectorCutoffInsertion.Constructions.vectorCutoffGradientInsertion (F := F) i) n
    (VectorStrongCutoff.Constructions.vectorStrongSobolev_schwartz_multiply b n (∂_{b i} g : 𝓢(E, ℂ)) u hu)

theorem vectorStrongSobolev_cutoffGradient_adjoint (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (g : 𝓢(E, ℂ)) (u : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hu : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (((VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g).restrictScalars ℝ).adjoint u) := by
  rw [VectorCutoffInsertion.Constructions.vectorCutoffGradientMultiply_operator_sum, map_sum, sum_apply]
  apply AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators.CM.Construction.strongSobolev_finset_sum b n Finset.univ
  intro i _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  exact VectorStrongCutoff.Constructions.vectorStrongSobolev_schwartz_multiply_adjoint b n (∂_{b i} g : 𝓢(E, ℂ)) _
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolevAdjoints.CM.Construction.strongSobolev_compLpL_adjoint b (VectorCutoffInsertion.Constructions.vectorCutoffGradientInsertion (F := F) i) n hu)

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorStrongCutoffGradient.Constructions
