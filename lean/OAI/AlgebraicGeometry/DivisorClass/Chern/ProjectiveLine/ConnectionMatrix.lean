import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionEnergyMatrix
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.Gradient

/-! # Connection Matrix -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual projective line connection and its full covariant energy in the same fixed Hilbert coordinates as the elliptic principal coefficient. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineConnectionCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ]
      GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  Line.ConnectionCoefficientComplex.lineGradientConnectionCoefficient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e z) (h.projectiveConnectionChart V e i z)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineConnectionCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveLineConnectionCoefficient V e n i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :=
  Line.ConnectionCoefficientComplex.lineGradientConnectionCoefficient_smoothOn _ n _ _
    ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hx => hx.1))
    (h.projectiveConnectionChart_smooth V e he i)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullEnergyPair_matrix (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    (a c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let K := h.projectiveLineConnectionCoefficient V e n i z
    let v := TensorGradientCoordinates.covectorTensorGradientCoordinates b n (fderiv ℝ a z)
    let t := TensorGradientCoordinates.covectorTensorGradientCoordinates b n (fderiv ℝ c z)
    (1 / 2 : ℝ) * (Line.RoughDivergence.lineCovectorFullEnergyPair b n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
      (h.projectiveConnectionChart V e i) (h.projectiveWeightChart V e i) a c z).re =
      inner ℝ (h.projectiveLineGradientCoefficient V e n i z (v + K (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (a z))))
        (t + K (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (c z))) := by
  have hw : h.projectiveWeightChart V e i z = Complex.ofReal (h.projectiveWeightChart V e i z).re := by
    rw [h.projectiveWeightChart_apply V e i hz, Complex.ofReal_re]
  exact Line.ConnectionEnergyMatrix.lineCovectorFullEnergyPair_matrix _ n _ _ _ _ a c z hw

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
