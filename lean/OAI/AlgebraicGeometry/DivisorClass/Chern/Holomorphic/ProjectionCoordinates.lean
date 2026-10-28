import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorAntiProjection
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.InsertionCoordinates

/-! # Projection Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ProjectionCoordinates

noncomputable section

/-! The original bundle type projection is the fixed antiholomorphic projection in genuine Euclidean chart coordinates. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem openManifoldOnePart_euclidean (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    {U : Opens V.analyticSpace} (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 1)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e U) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (Manifold.OneFormProjection.openManifoldOnePart Complex.I a).extension z =
      OneCovectorAntiProjection.oneCovectorAntiProjection (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.extension z) := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  rw [Manifold.OneFormProjection.openManifoldOnePart_inChart Complex.I a e he hz, OneCovectorAntiProjection.oneCovectorAntiProjection_comp,
    OneCovectorAntiProjection.oneCovectorAntiProjection_formula]

theorem holomorphicLineOnePart_covector (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (U : Opens V.analyticSpace) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((OneFormProjection.holomorphicLineOnePart u U Complex.I a).val i).extension z =
      OneCovectorAntiProjection.oneCovectorAntiProjection (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z) :=
  openManifoldOnePart_euclidean V e he (a.val i) hz

theorem holomorphicLineAntiFrameInsertion_covector (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Set V.analyticSpace))
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((HolomorphicFrame.Insertion.holomorphicLineAntiFrameInsertion u i f hf hs a).val.val i).extension z =
      f (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) • OneCovectorAntiProjection.oneCovectorAntiProjection (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.val z) := by
  have hp := holomorphicLineOnePart_covector V u e he ⊤ (HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i 1 f hf hs a) i
    (show z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
      from ⟨hz.1, trivial, hz.2⟩)
  have hc := HolomorphicFrame.InsertionCoordinates.holomorphicLineSmoothFrameInsertion_covector V u e i 1 f hf hs a hz
  exact hp.trans ((congrArg OneCovectorAntiProjection.oneCovectorAntiProjection hc).trans (OneCovectorAntiProjection.oneCovectorAntiProjection_complex_smul _ _))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ProjectionCoordinates
