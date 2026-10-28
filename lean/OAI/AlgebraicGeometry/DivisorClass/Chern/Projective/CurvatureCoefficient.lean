import OAI.AlgebraicGeometry.DivisorClass.Chern.CurvatureActionSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorPairCoefficient
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.Gradient
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorAntiProjection

/-! # Curvature Coefficient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The exact weighted curvature coefficient of the native weak equation, with the antiholomorphic test projection and the adjoint in their original order. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullCurvatureOperator (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 :=
  CurvatureActionOperators.fullBochnerCurvatureCLM (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLinePairCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ]
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  CovectorPairCoefficient.covectorPairCoefficient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (h.projectiveWeightChart V e i z).re)

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineWeakCurvatureCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ]
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 :=
  CovectorPairCoefficient.covectorWeakActionCoefficient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (h.projectiveWeightChart V e i z).re)
    ((h.projectiveFullCurvatureOperator V e z).comp OneCovectorAntiProjection.oneCovectorAntiProjection)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLinePairCoefficient_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    inner ℝ (h.projectiveLinePairCoefficient V e n i z (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a))
      (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n c) =
      (Line.TensorMetricTest.lineMetricTestPair b n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
        (fun _ => a) (fun _ => c) z).re := by
  dsimp only
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLinePairCoefficient, CovectorPairCoefficient.covectorPairCoefficient_pair]
  unfold Line.TensorMetricTest.lineMetricTestPair
  rw [h.projectiveWeightChart_apply V e i hz]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  rfl

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineWeakCurvatureCoefficient_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    inner ℝ (h.projectiveLineWeakCurvatureCoefficient V e i z (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1 a))
      (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b 1 c) =
      (Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
        (fun _ => a) (fun _ => BochnerCurvature.fullBochnerCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
          (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z)
          (OneCovectorAntiProjection.oneCovectorAntiProjection c)) z).re := by
  dsimp only
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineWeakCurvatureCoefficient, CovectorPairCoefficient.covectorWeakActionCoefficient_pair,
    ContinuousLinearMap.comp_apply, HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullCurvatureOperator, CurvatureActionOperators.fullBochnerCurvatureCLM_apply]
  unfold Line.TensorMetricTest.lineMetricTestPair
  rw [h.projectiveWeightChart_apply V e i hz]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  rfl

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLinePairCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveLinePairCoefficient V e n i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :=
  CovectorPairCoefficient.covectorPairCoefficient_smoothOn _ n _ _
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hx => hx.1))
    (((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).mono (fun _ hx => hx.1)).mul
      (Complex.reCLM.contDiff.comp_contDiffOn (h.projectiveWeightChart_smooth V e he i)))
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hx.1)
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hx.1)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineWeakCurvatureCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveLineWeakCurvatureCoefficient V e i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  apply CovectorPairCoefficient.covectorWeakActionCoefficient_smoothOn _ 1 _ _ _
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hx => hx.1))
    (((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).mono (fun _ hx => hx.1)).mul
      (Complex.reCLM.contDiff.comp_contDiffOn (h.projectiveWeightChart_smooth V e he i)))
    _ (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hx.1)
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hx.1)
  intro a
  have hs := CurvatureActionSmooth.fullBochnerCurvatureAction_smoothOn
    (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val) (fun _ => OneCovectorAntiProjection.oneCovectorAntiProjection a) D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hx => hx.1))
    ((Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hx => hx.1))
    ((Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm_smooth V e he 2 h.curvature).mono (fun _ hx => hx.1)) contDiffOn_const
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hx.1)
  simpa only [ContinuousLinearMap.comp_apply, HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveFullCurvatureOperator, CurvatureActionOperators.fullBochnerCurvatureCLM_apply] using hs

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
