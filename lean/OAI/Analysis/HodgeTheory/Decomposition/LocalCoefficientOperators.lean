import OAI.Analysis.HodgeTheory.Decomposition.AdjointCoefficients
import OAI.Analysis.HodgeTheory.Decomposition.LocalAdjointForm

/-! # Local Coefficient Operators -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalCoefficientOperators.Constructions

noncomputable section

/-! Smooth first-order and order-zero coefficient operators for the actual
codifferential on each projective chart. -/

open scoped ContDiff BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

def projectiveAdjointPrincipalCoefficient (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1) →L[ℝ]
      SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  -((AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).inverse.comp
    ((AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i).adjoint.comp (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) z)))

def projectiveAdjointZeroCoefficient (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1) →L[ℝ]
      SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  -((AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).inverse.comp
    (∑ i, (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i).adjoint.comp
      (fderiv ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1)) z
        (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i))))

variable (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveAdjointPrincipalCoefficient_smooth (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) :
    ContDiffOn ℝ ∞ (projectiveAdjointPrincipalCoefficient V e n i) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  ((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_inverse_smooth V e he n).clm_comp
    (contDiffOn_const.clm_comp (AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he (n + 1)))).neg

theorem projectiveAdjointZeroCoefficient_smooth :
    ContDiffOn ℝ ∞ (projectiveAdjointZeroCoefficient V e n) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  have hD (i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) :
      ContDiffOn ℝ ∞ (fun z => fderiv ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1)) z
        (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
    intro z hz
    exact ((((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he (n + 1)).contDiffAt
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).fderiv_right (by simp)).clm_apply
      contDiffAt_const).contDiffWithinAt
  have hS : ContDiffOn ℝ ∞ (fun z => ∑ i, (AdjointCoefficients.Constructions.projectiveEuclideanExteriorSymbol V n i).adjoint.comp
      (fderiv ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1)) z
        (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i))) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
    exact ContDiffOn.sum (fun i _ => contDiffOn_const.clm_comp (hD i))
  exact ((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_inverse_smooth V e he n).clm_comp hS).neg

/-- The explicit coefficient operators recover the actual local codifferential. -/
theorem projectiveLocalAdjointCoefficients_operator_formula
    (v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))
    (hv : ContDiffOn ℝ ∞ v (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _))
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients V e n v z =
      (∑ i, projectiveAdjointPrincipalCoefficient V e n i z
        (fderiv ℝ v z (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i))) +
        projectiveAdjointZeroCoefficient V e n z (v z) := by
  rw [AdjointCoefficients.Constructions.projectiveLocalAdjointCoefficients_expansion V e he n v hv z hz]
  simp only [projectiveAdjointPrincipalCoefficient, projectiveAdjointZeroCoefficient, neg_apply,
    ContinuousLinearMap.comp_apply, sum_apply, map_sum, Finset.sum_neg_distrib]
  abel

theorem projectiveAdjointZeroCoefficient_bounded
    {K : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ‖projectiveAdjointZeroCoefficient V e n z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image
    (((projectiveAdjointZeroCoefficient_smooth V e n he).continuousOn.mono hKU).norm)
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalCoefficientOperators.Constructions
