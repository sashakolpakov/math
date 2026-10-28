import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.WeakMatrix
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.EnergySupport

/-! # Pair Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The full native weak Bochner density vanishes off the support of its source. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem ProjectiveBochner.PairSupport.lineMetricTestPair_zero_left_value {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] [LinearOrder ι]
    (b : Module.Basis ι ℝ E) (n : ℕ) (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ)
    (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (z : E) (ha : a z = 0) :
    Line.TensorMetricTest.lineMetricTestPair b n B w a c z = 0 := by
  unfold Line.TensorMetricTest.lineMetricTestPair
  rw [ha, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero, map_zero, inner_zero_left, mul_zero]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochnerWeakPair_zero_left (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (i : V.analyticSpace)
    (a c : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (ha : z ∉ tsupport a) : h.projectiveBochnerWeakPair V e i a c z = 0 := by
  let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  have hE := Line.EnergySupport.lineCovectorFullEnergyPair_zero_left b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e)
    (h.projectiveConnectionChart V e i) (h.projectiveWeightChart V e i) a c z ha
  have hC := ProjectiveBochner.PairSupport.lineMetricTestPair_zero_left_value b 1 (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i)
    (fun _ => a z) (fun _ => BochnerCurvature.fullBochnerCurvatureAction b (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) z
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z) (OneCovectorAntiProjection.oneCovectorAntiProjection (c z))) z (image_eq_zero_of_notMem_tsupport ha)
  have heq := congrArg₂ (fun p q : ℂ => (1 / 2 : ℝ) * p.re + q.re) hE hC
  exact heq.trans (by norm_num)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
