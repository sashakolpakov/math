import OAI.Analysis.HodgeTheory.Decomposition.KoszulSmooth
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth

/-! # Projective Sharp Derivative -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveSharpDerivative.Constructions

noncomputable section

/-! The inverse of the genuine projective metric differentiates by the
constructed connection coefficient in every actual chart. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem projectiveMetricSharp_derivative {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (α : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) :
    fderiv ℝ (fun y => KoszulConnection.Constructions.bilinearMetricSharp (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e y) α) z u =
      -ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e z u (KoszulConnection.Constructions.bilinearMetricSharp (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) α) -
        KoszulConnection.Constructions.bilinearMetricSharp (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (α.comp (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e z u)) :=
  KoszulSmooth.Constructions.bilinearMetricSharp_derivative (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he) (fun _ hy => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hy)
    hz u (ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e z u) (ProjectiveConnection.Constructions.projectiveConnectionCoefficient_metric V e he hz u) α

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveSharpDerivative.Constructions
