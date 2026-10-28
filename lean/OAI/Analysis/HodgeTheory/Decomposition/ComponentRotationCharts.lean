import OAI.Analysis.HodgeTheory.Decomposition.ComponentRotation
import OAI.Analysis.HodgeTheory.Decomposition.ComplexRotationDifferentials
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection

/-! # Component Rotation Charts -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ComponentRotationCharts.Constructions

noncomputable section

/-! The globally smooth component rotation has the actual infinitesimal
covector rotation as its formula in every genuine projective chart. -/

variable (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) (C : irreducibleComponents X.carrier)
  (e : OpenPartialHomeomorph (X.componentVariety C).analyticSpace (X.componentVariety C).analyticModel)

def componentEuclideanChartEval (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel (X.componentVariety C)) :
    X.componentForms n →ₗ[ℂ] DifferentialForms.Manifold.Basic.FormValue (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel (X.componentVariety C)) n where
  toFun a := EuclideanForms.Constructions.euclideanChartForm (X.componentVariety C) e n (a C).val z
  map_add' a b := by ext v; rfl
  map_smul' c a := by ext v; rfl

theorem componentEuclideanChartEval_projection_rotation
    (he : e ∈ atlas (X.componentVariety C).analyticModel (X.componentVariety C).analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel (X.componentVariety C)) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain (X.componentVariety C) e)
    (i : Core.Constructions.Bidegree n) (a : X.componentForms n) :
    ComplexRotationDifferentials.Constructions.complexFormRotation n (componentEuclideanChartEval X n C e z (Projectors.Constructions.componentProjection X n i a)) =
      InfinitesimalTypeEigen.Constructions.typeRotationEigenvalue i • componentEuclideanChartEval X n C e z (Projectors.Constructions.componentProjection X n i a) := by
  rcases i with ⟨⟨p, q⟩, hi⟩
  subst n
  have hp := Projectors.Constructions.componentProjection_pure X (p + q) ⟨(p, q), rfl⟩ a
  change Projectors.Constructions.componentProjection X (p + q) ⟨(p, q), rfl⟩ a ∈ X.componentPureForms p q at hp
  rw [X.mem_componentPureForms_iff] at hp
  apply InfinitesimalTypeEigen.Constructions.covectorInfinitesimalRotation_pure p q
  exact ProjectiveCovectorConnection.Constructions.euclideanChartForm_pure (X.componentVariety C) e he p q _ (hp C) hz

theorem componentRotation_euclideanChart
    (he : e ∈ atlas (X.componentVariety C).analyticModel (X.componentVariety C).analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel (X.componentVariety C)) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain (X.componentVariety C) e)
    (a : X.componentForms n) :
    componentEuclideanChartEval X n C e z (ComponentRotation.Constructions.componentRotation X n a) =
      ComplexRotationDifferentials.Constructions.complexFormRotation n (componentEuclideanChartEval X n C e z a) := by
  rw [ComponentRotation.Constructions.componentRotation_apply, map_sum]
  simp only [map_smul]
  have hp (i : Core.Constructions.Bidegree n) := componentEuclideanChartEval_projection_rotation X n C e he z hz i a
  simp_rw [← hp]
  rw [← map_sum, ← map_sum, Projectors.Constructions.sum_componentProjection]

end

end OAI.Analysis.HodgeTheory.Decomposition.ComponentRotationCharts.Constructions
