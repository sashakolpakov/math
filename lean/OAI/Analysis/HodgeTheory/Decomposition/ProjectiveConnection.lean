import OAI.Analysis.HodgeTheory.Decomposition.KahlerKoszul
import OAI.Analysis.HodgeTheory.Decomposition.EuclideanMetricDerivative

/-! # Projective Connection -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions

noncomputable section

/-! Actual torsion-free metric connection coefficients on each projective
holomorphic chart, proved to preserve the complex structure. -/

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def projectiveConnectionCoefficient (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V :=
  KoszulConnection.Constructions.koszulConnection (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative V e z)

include he

theorem projectiveConnectionCoefficient_symmetric {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    projectiveConnectionCoefficient V e z u v = projectiveConnectionCoefficient V e z v u :=
  KoszulConnection.Constructions.koszulConnection_symmetric _ _ (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative_symmetric V e he hz) u v

theorem projectiveConnectionCoefficient_metric {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v w : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z (projectiveConnectionCoefficient V e z u v) w +
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z v (projectiveConnectionCoefficient V e z u w) =
        fderiv ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) z u v w :=
  KoszulConnection.Constructions.koszulConnection_metric _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz) _
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative_symmetric V e he hz) u v w

theorem projectiveConnectionCoefficient_J_right {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    projectiveConnectionCoefficient V e z u (Complex.I • v) = Complex.I • projectiveConnectionCoefficient V e z u v :=
  KahlerKoszul.Constructions.koszulConnection_J_right _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz) _
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative_symmetric V e he hz)
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative_J_skew V e he hz)
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative_closed V e he hz) u v

theorem projectiveConnectionCoefficient_J_left {z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    projectiveConnectionCoefficient V e z (Complex.I • u) v = Complex.I • projectiveConnectionCoefficient V e z u v :=
  KahlerKoszul.Constructions.koszulConnection_J_left _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz)
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetric_J_skew V e he hz) _
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative_symmetric V e he hz)
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative_J_skew V e he hz)
    (EuclideanMetricDerivative.Constructions.projectiveEuclideanMetricDerivative_closed V e he hz) u v

end

end OAI.Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions
