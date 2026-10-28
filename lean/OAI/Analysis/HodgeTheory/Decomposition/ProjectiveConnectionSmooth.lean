import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnection
import OAI.Analysis.HodgeTheory.Decomposition.KoszulSmooth

/-! # Projective Connection Smooth -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions

noncomputable section

/-! The actual projective connection coefficients are smooth on every
genuine holomorphic chart domain. -/

open scoped ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

local instance projectiveBilinearNormed : NormedAddCommGroup
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) := inferInstance
local instance projectiveBilinearNormedSpace : NormedSpace ℝ
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) := inferInstance

include he

theorem projectiveEuclideanMetricDerivative_smooth :
    ContDiffOn ℝ ∞ (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative V e)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).fderiv_of_isOpen (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (by simp)

theorem projectiveConnectionCoefficient_smooth :
    ContDiffOn ℝ ∞ (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  KoszulSmooth.Constructions.koszulConnection_smoothOn (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative V e)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he)
    (projectiveEuclideanMetricDerivative_smooth V e he)
    (fun _ hz => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions
