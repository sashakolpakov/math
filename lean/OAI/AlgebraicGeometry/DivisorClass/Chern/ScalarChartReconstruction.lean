import OAI.Analysis.HodgeTheory.Decomposition.ChartReconstructionSmooth

/-! # Scalar Chart Reconstruction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarChartReconstruction

noncomputable section

/-! The actual scalar chart test reconstructs every smooth form from its literal supported coefficients. -/

open scoped SchwartzMap ContDiff _root_.Manifold
open OAI.Analysis.HodgeTheory.Decomposition.ChartReconstructionSmooth.Constructions

theorem projectiveSchwartzTestLocalized_reconstruct_coefficients (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hgs : tsupport g ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : ∀ z, c z = Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z) :
    Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hg hgs c =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g)
        (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hg hgs) a := by
  apply Subtype.ext
  apply Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.supportedCoefficients_faithful V e he n
  · exact Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_zero_off_source V e he n g hg hgs c
  · intro x hx
    change ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g x • a x = 0
    rw [ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar, Set.indicator_of_notMem hx]
    exact zero_smul ℂ (a x)
  · intro z
    rw [Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized_coefficients, hc z]
    exact (Analysis.HodgeTheory.Decomposition.ChartReconstructionSmooth.Constructions.supportedEuclideanCoefficients_chart_smul V e n g a.val z).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarChartReconstruction
