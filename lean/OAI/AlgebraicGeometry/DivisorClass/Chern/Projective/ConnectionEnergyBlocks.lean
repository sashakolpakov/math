import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.ConnectionMatrix
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.SobolevCoefficient
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionMatrixSmooth

/-! # Connection Energy Blocks -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The native connection energy's three lower-order matrix coefficients, with the exact normalized-gradient convention and original smooth connection. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def Projective.ConnectionEnergyBlocks.projectivePhysicalGradientScale (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ]
      GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  ((2 * Real.pi * Complex.I : ℂ) • ContinuousLinearMap.id ℂ
    (GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)).restrictScalars ℝ

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineValueGradientCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ]
      GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  ConnectionEnergyMatrix.connectionValueGradientMatrix (h.projectiveLineGradientCoefficient V e n i z)
    (Projective.ConnectionEnergyBlocks.projectivePhysicalGradientScale V n) (h.projectiveLineConnectionCoefficient V e n i z)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineValueGradientCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveLineValueGradientCoefficient V e n i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :=
  ConnectionMatrixSmooth.connectionValueGradientMatrix_smoothOn (Projective.ConnectionEnergyBlocks.projectivePhysicalGradientScale V n) _ _
    (h.projectiveLineGradientCoefficient_smooth V e he n i)
    (h.projectiveLineConnectionCoefficient_smooth V e he n i)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineGradientValueCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ]
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  ConnectionEnergyMatrix.connectionGradientValueMatrix (h.projectiveLineGradientCoefficient V e n i z)
    (Projective.ConnectionEnergyBlocks.projectivePhysicalGradientScale V n) (h.projectiveLineConnectionCoefficient V e n i z)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineGradientValueCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveLineGradientValueCoefficient V e n i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :=
  ConnectionMatrixSmooth.connectionGradientValueMatrix_smoothOn (Projective.ConnectionEnergyBlocks.projectivePhysicalGradientScale V n) _ _
    (h.projectiveLineGradientCoefficient_smooth V e he n i)
    (h.projectiveLineConnectionCoefficient_smooth V e he n i)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineConnectionValueCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ]
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  ConnectionEnergyMatrix.connectionValueMatrix (h.projectiveLineGradientCoefficient V e n i z) (h.projectiveLineConnectionCoefficient V e n i z)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineConnectionValueCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveLineConnectionValueCoefficient V e n i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :=
  ConnectionMatrixSmooth.connectionValueMatrix_smoothOn _ _
    (h.projectiveLineGradientCoefficient_smooth V e he n i)
    (h.projectiveLineConnectionCoefficient_smooth V e he n i)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
