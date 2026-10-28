import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.ConnectionEnergyBlocks

/-! # Normalized Connection Energy -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original full covariant energy has exactly the native normalized principal coefficient and the three explicit smooth connection blocks. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullEnergyPair_normalized_matrix (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    (a c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v w : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    (hv : (2 * Real.pi * Complex.I : ℂ) • v =
      TensorGradientCoordinates.covectorTensorGradientCoordinates (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (fderiv ℝ a z))
    (hw : (2 * Real.pi * Complex.I : ℂ) • w =
      TensorGradientCoordinates.covectorTensorGradientCoordinates (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (fderiv ℝ c z)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let av := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (a z)
    let cv := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (c z)
    (1 / 2 : ℝ) * (Line.RoughDivergence.lineCovectorFullEnergyPair b n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
      (h.projectiveConnectionChart V e i) (h.projectiveWeightChart V e i) a c z).re =
      inner ℝ (h.projectiveLineSobolevCoefficient V e n i z v) w +
      inner ℝ (h.projectiveLineValueGradientCoefficient V e n i z av) w +
      inner ℝ (h.projectiveLineGradientValueCoefficient V e n i z v) cv +
      inner ℝ (h.projectiveLineConnectionValueCoefficient V e n i z av) cv := by
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let A := h.projectiveLineGradientCoefficient V e n i z
  let K := h.projectiveLineConnectionCoefficient V e n i z
  let S := Projective.ConnectionEnergyBlocks.projectivePhysicalGradientScale V n
  let av := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (a z)
  let cv := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (c z)
  have he := h.projectiveFullEnergyPair_matrix V e n i a c hz
  have hl : TensorGradientCoordinates.covectorTensorGradientCoordinates b n (fderiv ℝ a z) + K av = S v + K av :=
    congrArg (fun q => q + K av) hv.symm
  have hr : TensorGradientCoordinates.covectorTensorGradientCoordinates b n (fderiv ℝ c z) + K cv = S w + K cv :=
    congrArg (fun q => q + K cv) hw.symm
  have ht := congrArg₂ (fun p q => inner ℝ (A p) q) hl hr
  exact (he.trans ht).trans (ConnectionEnergyMatrix.connectionEnergy_matrix_expansion A S K v w av cv)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
