import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.Bochner
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CrossEnergy

/-! # Bochner Cross -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The full native Bochner formula paired with an independent original compact bundle test. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
  (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

def HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullRoughCrossPair (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  let t := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val
  Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
    (Line.RoughAnti.lineCovectorFullRoughLaplacian b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
      (h.projectiveConnectionChart V e i) s) t

def HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvatureCrossPair (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  let t := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val
  Line.TensorMetricTest.lineMetricTestPair b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
    (fun z => BochnerCurvature.fullBochnerCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (s z)) t

include he in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactBochnerCrossPair (a c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    h.compactFramePair V e i 1 f hf hs c.val
      (h.smoothDolbeaultLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)) z =
        (1 / 2 : ℂ) * h.compactFullRoughCrossPair V e i f hf hs a c z +
          h.compactFullCurvatureCrossPair V e i f hf hs a c z := by
  let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val
  let t := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs c.val
  let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
  by_cases hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  · have hb := h.smoothDolbeaultLaplacianOne_full_curvature V e he i A hz
    have ha := HolomorphicCompact.ChartField.holomorphicLineCompactChartField_eventually_inFrame V e i 1 f hf hs a.val hz
    have hR := Line.RoughAnti.lineCovectorFullRoughLaplacian_congr
      (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
      (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i) _ _ ha
    dsimp only [A, HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm] at hb
    rw [← hR, ← HolomorphicCompact.ChartField.holomorphicLineCompactChartField_inFrame V e i 1 f hf hs a.val hz] at hb
    unfold HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullRoughCrossPair HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvatureCrossPair Line.TensorMetricTest.lineMetricTestPair
    dsimp only [HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm]
    rw [hb, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left, Line.ConnectionOperator.bilinearFormMetricPair_complex_smul_left]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  · have ht : t z = 0 := image_eq_zero_of_notMem_tsupport
      (fun hsupp => hz (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hs c.val hsupp))
    simp only [HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair, HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullRoughCrossPair, HolomorphicMetric.Data.HolomorphicLineMetricData.compactFullCurvatureCrossPair, Line.TensorMetricTest.lineMetricTestPair]
    change _ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ 1 _ _ (t z) =
      (1 / 2 : ℂ) * (_ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ 1 _ _ (t z)) + _ * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair _ 1 _ _ (t z)
    simp only [ht, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero, inner_zero_right, mul_zero, add_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
