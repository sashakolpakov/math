import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.WeightedSchwartzPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzTestIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest

/-! # Test Source Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! On the support of each inserted test, the original bounded frame localization has exactly the original bundle coefficients. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))

theorem Holomorphic.TestSourceCoordinates.holomorphicLineFrameCoefficient_on_test_support (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ tsupport g) :
    HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i 1 (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) a z =
        Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
          (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z) := by
  let f := Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs
  have hfield := HolomorphicCompact.ChartField.holomorphicLineCompactChartField_inFrame V e i 1 f
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) a (hs hz)
  have hmul := Holomorphic.CutoffCoordinates.holomorphicLineSmoothMul_covector V e i f
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs) 1 a (hs hz)
  have hone := Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_one V u e he i g hg hs z hz
  have heq := hfield.trans (hmul.trans ((congrArg (fun r : ℂ => r •
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z) hone).trans (one_smul ℂ _)))
  exact (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_coefficients V e i 1 f
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) a z).symm.trans
      (congrArg (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1) heq)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameCoefficient_weighted_test_pair (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    inner ℝ (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i 1 (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) a z)
      (h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c z) =
      (Line.TensorMetricTest.lineMetricTestPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension)
        (fun x => g x • OneCovectorAntiProjection.oneCovectorAntiProjection
          ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c x))) z).re := by
  by_cases hz : z ∈ tsupport g
  · have hc := Holomorphic.TestSourceCoordinates.holomorphicLineFrameCoefficient_on_test_support V e he i g hg hs a hz
    have hp := h.projectiveWeightedAntiSchwartzTest_pair V e he i g hg hs c
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z) (hs hz)
    have heval := congrArg Complex.re (Line.TensorMetricTest.lineMetricTestPair_constant_values
      (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension)
      (fun x => g x • OneCovectorAntiProjection.oneCovectorAntiProjection
        ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c x))) z)
    exact (congrArg (fun v => inner ℝ v (h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c z)) hc).trans
      (hp.trans heval)
  · have ht : h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hsupp => hz
        (h.projectiveWeightedAntiSchwartzTest_tsupport V e he i g hg hs c hsupp))
    have hgzero : g z = 0 := image_eq_zero_of_notMem_tsupport hz
    have htestzero : g z • OneCovectorAntiProjection.oneCovectorAntiProjection
        ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c z)) = 0 :=
      (congrArg (fun r : ℂ => r • OneCovectorAntiProjection.oneCovectorAntiProjection
        ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c z))) hgzero).trans
          (zero_smul ℂ (OneCovectorAntiProjection.oneCovectorAntiProjection
            ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c z))))
    have hpzero := Line.TensorMetricTest.lineMetricTestPair_zero_right_value
      (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension)
      (fun x => g x • OneCovectorAntiProjection.oneCovectorAntiProjection
        ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c x))) z htestzero
    exact ((congrArg (fun v => inner ℝ
      (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i 1 (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
        (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
        (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) a z) v) ht).trans (inner_zero_right _)).trans
      (congrArg Complex.re hpzero).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
