import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CurvatureCoefficient
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.NormalizedConnectionEnergy

/-! # Weak Matrix -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The complete smooth zeroth-order coefficient combines the actual connection value block with the correctly oriented full curvature adjoint. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem ProjectiveBochner.WeakMatrix.real_three_terms_merge_value_operators
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (p q r : ℝ) (D J : F →L[ℝ] F) (a c : F) :
    (p + q + r + inner ℝ (D a) c) + inner ℝ (J a) c =
      p + q + r + inner ℝ ((D + J) a) c := by
  rw [_root_.add_apply, inner_add_left, add_assoc]

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineWeakValueCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ]
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 :=
  h.projectiveLineConnectionValueCoefficient V e 1 i z + h.projectiveLineWeakCurvatureCoefficient V e i z

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineWeakValueCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveLineWeakValueCoefficient V e i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :=
  (h.projectiveLineConnectionValueCoefficient_smooth V e he 1 i).add
    (h.projectiveLineWeakCurvatureCoefficient_smooth V e he i)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerWeakPair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
    (a c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℝ :=
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  (1 / 2 : ℝ) * (Line.RoughDivergence.lineCovectorFullEnergyPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (h.projectiveConnectionChart V e i) (h.projectiveWeightChart V e i) a c z).re +
      (Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i) (fun _ => a z)
        (fun _ => BochnerCurvature.fullBochnerCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (OneCovectorAntiProjection.oneCovectorAntiProjection (c z))) z).re

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerWeakPair_matrix (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
    (a c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v w : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)
    (hv : (2 * Real.pi * Complex.I : ℂ) • v =
      TensorGradientCoordinates.covectorTensorGradientCoordinates (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 (fderiv ℝ a z))
    (hw : (2 * Real.pi * Complex.I : ℂ) • w =
      TensorGradientCoordinates.covectorTensorGradientCoordinates (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 (fderiv ℝ c z)) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let av := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1 (a z)
    let cv := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1 (c z)
    h.projectiveBochnerWeakPair V e i a c z =
      inner ℝ (h.projectiveLineSobolevCoefficient V e 1 i z v) w +
      inner ℝ (h.projectiveLineValueGradientCoefficient V e 1 i z av) w +
      inner ℝ (h.projectiveLineGradientValueCoefficient V e 1 i z v) cv +
      inner ℝ (h.projectiveLineWeakValueCoefficient V e i z av) cv := by
  have he := h.projectiveFullEnergyPair_normalized_matrix V e 1 i a c hz v w hv hw
  have hc := h.projectiveLineWeakCurvatureCoefficient_pair V e i hz (a z) (c z)
  have hp := congrArg₂ (fun p q : ℝ => p + q) he hc.symm
  exact hp.trans (ProjectiveBochner.WeakMatrix.real_three_terms_merge_value_operators _ _ _
    (h.projectiveLineConnectionValueCoefficient V e 1 i z)
    (h.projectiveLineWeakCurvatureCoefficient V e i z)
    (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 (a z))
    (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 (c z)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
