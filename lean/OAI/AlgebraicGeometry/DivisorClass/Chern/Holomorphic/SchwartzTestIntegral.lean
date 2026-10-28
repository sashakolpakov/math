import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzTestCutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.FrameIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.PairIntegrability

/-! # Schwartz Test Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual global pairing with an inserted antiholomorphic test is exactly its prescribed compact Euclidean chart integral. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
  (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))

theorem Holomorphic.SchwartzTestIntegral.holomorphicLineAntiSchwartzFrameInsertion_compact_field (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val z =
        g z • OneCovectorAntiProjection.oneCovectorAntiProjection
          ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c z)) := by
  let f := Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs
  let A := (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val
  by_cases hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  · have hf := HolomorphicCompact.ChartField.holomorphicLineCompactChartField_inFrame V e i 1 f
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) A hz
    have hm := congrArg (fun a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1 =>
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z)
        (Holomorphic.SchwartzTestCutoff.holomorphicLineAntiSchwartzFrameInsertion_cutoff V u e he i g hg hs c)
    exact hf.trans (hm.trans (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion_covector V u e he i g hg hs c hz))
  · have hleft : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f
        (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
        (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) A z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hz (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f
        (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
        (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) A ht))
    have hgz : g z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hs ht))
    exact hleft.trans ((congrArg (fun q : ℂ => q • OneCovectorAntiProjection.oneCovectorAntiProjection
      ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c z))) hgz).trans
        (zero_smul ℂ (OneCovectorAntiProjection.oneCovectorAntiProjection
          ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c z))))).symm

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.schwartzFramePair_integral (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    (∫ z, Line.TensorMetricTest.lineMetricTestPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension)
      (fun x => g x • OneCovectorAntiProjection.oneCovectorAntiProjection
        ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c x))) z) =
      h.formIntegralPair V 1 a (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val := by
  have hp := h.compactFramePair_integral V e he i 1 (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val a
  have hi := congrArg (fun F : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 =>
    ∫ z, Line.TensorMetricTest.lineMetricTestPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) F z)
    (funext (Holomorphic.SchwartzTestIntegral.holomorphicLineAntiSchwartzFrameInsertion_compact_field V e he i g hg hs c))
  exact hi.symm.trans (hp.trans (congrArg (h.formIntegralPair V 1 a)
    (Holomorphic.SchwartzTestCutoff.holomorphicLineAntiSchwartzFrameInsertion_cutoff V u e he i g hg hs c)))

include he hg hs in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.schwartzFramePair_integrable (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    Integrable (Line.TensorMetricTest.lineMetricTestPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension)
      (fun x => g x • OneCovectorAntiProjection.oneCovectorAntiProjection
        ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c x)))) := by
  have hi := h.compactFramePair_integrable V e he i (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) 1
    (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val a
  have heq := congrArg (Line.TensorMetricTest.lineMetricTestPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension))
    (funext (Holomorphic.SchwartzTestIntegral.holomorphicLineAntiSchwartzFrameInsertion_compact_field V e he i g hg hs c))
  exact Eq.mp (congrArg (fun F : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ => Integrable F) heq) hi

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
