import OAI.Analysis.HodgeTheory.Decomposition.ComponentRotationCharts
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveLocal
import OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful

/-! # Component Laplacian -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ComponentLaplacian.Constructions

noncomputable section

/-! The genuine componentwise Hodge Laplacian preserves every smooth
bidegree by commuting with the actual global rotation operator. -/

open scoped _root_.Topology

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  [∀ C : irreducibleComponents X.carrier, MeasurableSpace (X.componentVariety C).analyticSpace]
  [∀ C : irreducibleComponents X.carrier, BorelSpace (X.componentVariety C).analyticSpace]

def componentPositiveLaplacian (n : ℕ) : Module.End ℂ (X.componentForms (n + 1)) :=
  LinearMap.pi fun C => (AdjointAlgebra.Constructions.projectivePositiveLaplacian (X.componentVariety C) n).comp (LinearMap.proj C)

theorem componentPositiveLaplacian_chart (n : ℕ) (a : X.componentForms (n + 1))
    (C : irreducibleComponents X.carrier)
    (e : OpenPartialHomeomorph (X.componentVariety C).analyticSpace (X.componentVariety C).analyticModel)
    (he : e ∈ atlas (X.componentVariety C).analyticModel (X.componentVariety C).analyticSpace)
    {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel (X.componentVariety C)} (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain (X.componentVariety C) e) :
    ComponentRotationCharts.Constructions.componentEuclideanChartEval X (n + 1) C e z (componentPositiveLaplacian X n a) =
      ProjectiveLocal.Constructions.projectiveLocalHodgeOperator (X.componentVariety C) e n (fun y => ComponentRotationCharts.Constructions.componentEuclideanChartEval X (n + 1) C e y a) z :=
  ProjectiveLocal.Constructions.projectivePositiveLaplacian_chart (X.componentVariety C) e he n (a C) hz

theorem componentPositiveLaplacian_rotation (n : ℕ) (a : X.componentForms (n + 1)) :
    ComponentRotation.Constructions.componentRotation X (n + 1) (componentPositiveLaplacian X n a) =
      componentPositiveLaplacian X n (ComponentRotation.Constructions.componentRotation X (n + 1) a) := by
  funext C
  apply DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let V := X.componentVariety C
  let e := chartAt V.analyticModel x
  have he := chart_mem_atlas V.analyticModel x
  have hx := mem_chart_source V.analyticModel x
  let z := MeasureVolume.Constructions.chartCoordinateForward V e x
  have hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := MeasureVolume.Constructions.chartCoordinateForward_mem V e x hx
  have heq : Set.EqOn (fun y => ComponentRotationCharts.Constructions.componentEuclideanChartEval X (n + 1) C e y (ComponentRotation.Constructions.componentRotation X (n + 1) a))
      (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (ComponentRotationCharts.Constructions.componentEuclideanChartEval X (n + 1) C e y a))
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) := by
    intro y hy
    exact ComponentRotationCharts.Constructions.componentRotation_euclideanChart X (n + 1) C e he y hy a
  have hchart : ComponentRotationCharts.Constructions.componentEuclideanChartEval X (n + 1) C e z
      (ComponentRotation.Constructions.componentRotation X (n + 1) (componentPositiveLaplacian X n a)) =
      ComponentRotationCharts.Constructions.componentEuclideanChartEval X (n + 1) C e z
        (componentPositiveLaplacian X n (ComponentRotation.Constructions.componentRotation X (n + 1) a)) := by
    rw [ComponentRotationCharts.Constructions.componentRotation_euclideanChart X (n + 1) C e he z hz,
      componentPositiveLaplacian_chart X n a C e he hz,
      componentPositiveLaplacian_chart X n (ComponentRotation.Constructions.componentRotation X (n + 1) a) C e he hz,
      ProjectiveLocal.Constructions.projectiveLocalHodgeOperator_eqOn V e n heq hz]
    exact ProjectiveLocal.Constructions.projectiveLocalHodgeOperator_rotation V e he n _ (EuclideanForms.Constructions.euclideanChartForm_smooth V e he (n + 1) (a C)) hz
  apply ChartCoefficientFaithful.Constructions.euclideanChartCoefficients_eq_at V e he (n + 1) _ _ x hx
  exact congrArg (SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis (n + 1)) hchart

theorem componentPositiveLaplacian_pure (n : ℕ) (i : Core.Constructions.Bidegree (n + 1)) (a : X.componentForms (n + 1))
    (ha : a ∈ Core.Constructions.pureFormsAt X (n + 1) i) : componentPositiveLaplacian X n a ∈ Core.Constructions.pureFormsAt X (n + 1) i :=
  ComponentRotation.Constructions.componentOperator_preserves_type_of_rotation X (n + 1) (componentPositiveLaplacian X n)
    (componentPositiveLaplacian_rotation X n) i a ha

end

end OAI.Analysis.HodgeTheory.Decomposition.ComponentLaplacian.Constructions
