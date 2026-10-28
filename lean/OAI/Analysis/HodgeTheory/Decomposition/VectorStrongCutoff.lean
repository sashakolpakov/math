import OAI.Analysis.HodgeTheory.Decomposition.VectorStrongSobolev
import OAI.Analysis.HodgeTheory.Decomposition.CompatibleRealInner
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators

/-! # Vector Strong Cutoff -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorStrongCutoff.Constructions

noncomputable section

/-! Multiplication by a scalar Schwartz cutoff and its actual real
Hilbert adjoint preserve all Sobolev orders of vector coefficient fields. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators.CM.Construction

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem vectorStrongSobolev_schwartz_multiply (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E))
    (hu : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g u) := by
  apply (VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b n _).mpr
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_distribution]
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.memSobolev_nat_schwartz_cutoff n g ((VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b n u).mp hu)

omit [Fintype ι] in
theorem vectorSchwartzL2Multiply_real_adjoint (g : 𝓢(E, ℂ)) :
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (F := F) g).restrictScalars ℝ).adjoint =
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (F := F) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators.CM.Construction.schwartzConjugate g)).restrictScalars ℝ := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  change (∫ x, inner ℝ (u x) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g v x)) =
    ∫ x, inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators.CM.Construction.schwartzConjugate g) u x) (v x)
  apply integral_congr_ae
  filter_upwards [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g v, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators.CM.Construction.schwartzConjugate g) u]
    with x hv hu
  rw [hv, hu, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators.CM.Construction.schwartzConjugate_apply, CompatibleRealInner.Constructions.compatible_real_inner, CompatibleRealInner.Constructions.compatible_real_inner,
    inner_smul_right, inner_smul_left, starRingEnd_self_apply]

theorem vectorStrongSobolev_schwartz_multiply_adjoint (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E))
    (hu : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (F := F) g).restrictScalars ℝ).adjoint u) := by
  rw [vectorSchwartzL2Multiply_real_adjoint]
  exact vectorStrongSobolev_schwartz_multiply b n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffOperators.CM.Construction.schwartzConjugate g) u hu

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorStrongCutoff.Constructions
