import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.Adjoint
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.SchwartzGradient
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.WeakMatrix

/-! # Schwartz Tests -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Actual compact adjoint tests for all four blocks of the complete native Bochner matrix. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
  (hq : HasCompactSupport q)
  (hs : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerGradientSchwartzTest :
    𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) :=
  Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineSobolevCoefficient V e 1 i)
    (Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq)
    (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
    (h.projectiveLineSobolevCoefficient_smooth V e he 1 i)
    (Compact.SchwartzGradient.compactSchwartzGradient_compact _ q hq) ((Compact.SchwartzGradient.compactSchwartzGradient_tsupport _ q hq).trans hs) +
  Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineGradientValueCoefficient V e 1 i) q
    (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
    (h.projectiveLineGradientValueCoefficient_smooth V e he 1 i) hq hs

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerValueSchwartzTest :
    𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) :=
  Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineValueGradientCoefficient V e 1 i)
    (Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq)
    (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
    (h.projectiveLineValueGradientCoefficient_smooth V e he 1 i)
    (Compact.SchwartzGradient.compactSchwartzGradient_compact _ q hq) ((Compact.SchwartzGradient.compactSchwartzGradient_tsupport _ q hq).trans hs) +
  Compact.Adjoint.compactAdjointSchwartz (h.projectiveLineWeakValueCoefficient V e i) q
    (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
    (h.projectiveLineWeakValueCoefficient_smooth V e he i) hq hs

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerGradientSchwartzTest_apply (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    h.projectiveBochnerGradientSchwartzTest V e he i q hq hs z =
      (h.projectiveLineSobolevCoefficient V e 1 i z).adjoint
        (Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq z) +
      (h.projectiveLineGradientValueCoefficient V e 1 i z).adjoint (q z) := rfl

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerValueSchwartzTest_apply (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    h.projectiveBochnerValueSchwartzTest V e he i q hq hs z =
      (h.projectiveLineValueGradientCoefficient V e 1 i z).adjoint
        (Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq z) +
      (h.projectiveLineWeakValueCoefficient V e i z).adjoint (q z) := rfl

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerSchwartzTests_pair
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (a : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)
    (v : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) :
    let w := Compact.SchwartzGradient.compactSchwartzGradient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) q hq z
    inner ℝ (h.projectiveLineSobolevCoefficient V e 1 i z v) w +
      inner ℝ (h.projectiveLineValueGradientCoefficient V e 1 i z a) w +
      inner ℝ (h.projectiveLineGradientValueCoefficient V e 1 i z v) (q z) +
      inner ℝ (h.projectiveLineWeakValueCoefficient V e i z a) (q z) =
        inner ℝ v (h.projectiveBochnerGradientSchwartzTest V e he i q hq hs z) +
        inner ℝ a (h.projectiveBochnerValueSchwartzTest V e he i q hq hs z) :=
  Compact.Adjoint.weak_matrix_pair_adjoint _ _ _ _ a (q z) v _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
