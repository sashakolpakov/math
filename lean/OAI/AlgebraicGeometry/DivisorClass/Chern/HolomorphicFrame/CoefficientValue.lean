import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffCoordinates

/-! # Coefficient Value -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.CoefficientValue

noncomputable section

/-! Exact pointwise coefficients of every original frame localization, for any actual smooth chart cutoff. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicLineFrameCoefficient_inFrame (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace) (n : ℕ)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs a z =
      f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) •
        Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension z) := by
  let C := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
  have hfield := (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_inFrame V e i n f hf hs a hz).trans
    (Holomorphic.CutoffCoordinates.holomorphicLineSmoothMul_covector V e i f hf n a hz)
  exact (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_coefficients V e i n f hf hs a z).symm.trans
    ((congrArg C hfield).trans (C.map_smul (f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) _))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.CoefficientValue
