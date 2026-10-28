import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.FrameIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.Curvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughAnti

/-! # Bochner -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The full Bochner formula for literal compact chart fields of the original global cutoff forms. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

def HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 :=
  ⟨Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a.val, Holomorphic.AntiMultiplication.holomorphicLineSmoothMul_anti u ⊤ f hf 1 a⟩

def HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullRoughPair (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
    (Line.RoughAnti.lineCovectorFullRoughLaplacian b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
      (h.projectiveConnectionChart V e i) c) c

def HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvaturePair (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
    (fun z => BochnerCurvature.fullBochnerCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (c z)) c

include he in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactBochnerPair (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    h.compactFramePair V e i 1 f hf hs a.val
      (h.smoothDolbeaultLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)) z =
        (1 / 2 : ℂ) * h.compactFullRoughPair V e i f hf hs a z +
          h.compactFullCurvaturePair V e i f hf hs a z := by
  let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
  by_cases hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  · have hb := h.smoothDolbeaultLaplacianOne_full_curvature V e he i A hz
    have hc := HolomorphicCompact.ChartField.holomorphicLineCompactChartField_eventually_inFrame V e i 1 f hf hs a.val hz
    have hR := Line.RoughAnti.lineCovectorFullRoughLaplacian_congr
      (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
      (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i) _ _ hc
    dsimp only [A, HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm] at hb
    rw [← hR, ← HolomorphicCompact.ChartField.holomorphicLineCompactChartField_inFrame V e i 1 f hf hs a.val hz] at hb
    unfold HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullRoughPair HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvaturePair Line.TensorMetricTest.lineMetricTestPair
    dsimp only [HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm]
    rw [hb, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left, Line.ConnectionOperator.bilinearFormMetricPair_complex_smul_left]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  · have hc : c z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hz (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs a.val ht))
    change _ = _
    simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair, HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullRoughPair, HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvaturePair, Line.TensorMetricTest.lineMetricTestPair]
    change _ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ 1 _ _ (c z) =
      (1 / 2 : ℂ) * (_ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ 1 _ _ (c z)) + _ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ 1 _ _ (c z)
    simp only [hc, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero, inner_zero_right, mul_zero, add_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
