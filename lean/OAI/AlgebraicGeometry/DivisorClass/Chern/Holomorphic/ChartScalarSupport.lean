import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiSchwartzTests

/-! # Chart Scalar Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartScalarSupport

noncomputable section

/-! The original scalar chart cutoff is supported in its holomorphic frame and is fixed by the constructed frame cutoff. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
  (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))

include hg hs in
theorem varietyChartTestScalar_holomorphic_support :
    tsupport (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) ⊆
      (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace) := by
  intro x hx
  have hbase : tsupport g ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := fun _ hz => (hs hz).1
  have him := ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_tsupport V e g hg hbase hx
  refine ⟨ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage_subset_source V e hbase him, ?_⟩
  obtain ⟨z, hz, rfl⟩ := him
  exact (hs hz).2

theorem holomorphicSchwartzFrameCutoff_one_on_chart_scalar
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (x : V.analyticSpace)
    (hx : x ∈ tsupport (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g)) :
    AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs x = 1 := by
  have him := ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_tsupport V e g hg (fun _ hz => (hs hz).1) hx
  obtain ⟨z, hz, rfl⟩ := him
  exact AntiSchwartzTests.holomorphicSchwartzFrameCutoff_one V u e he i g hg hs z hz

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartScalarSupport
