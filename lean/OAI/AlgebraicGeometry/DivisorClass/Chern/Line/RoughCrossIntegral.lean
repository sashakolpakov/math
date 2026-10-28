import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughDivergence

/-! # Rough Cross Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughCrossIntegral

noncomputable section

/-! Integration by parts for the actual full rough Laplacian against an independent compact test. -/

open _root_.MeasureTheory
open scoped ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  RoughSmooth.roughSmooth_metricNormed RoughSmooth.roughSmooth_metricSpace RoughSmooth.roughSmooth_connectionNormed RoughSmooth.roughSmooth_connectionSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem lineCovectorFullRoughLaplacian_integral_cross_pair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (hw : ContDiffOn ℝ ∞ w U) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ U)
    (hc : ContDiff ℝ ∞ c) (hcc : HasCompactSupport c) (hcs : tsupport c ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hmetric : ∀ x ∈ U, ∀ v p q, B x (G x v p) q + B x p (G x v q) = fderiv ℝ B x v p q)
    (hGs : ∀ x ∈ U, ∀ v t, G x v t = G x t v)
    (hweight : ∀ x ∈ U, ∀ v, fderiv ℝ w x v = w x * (conj (A x v) + A x v)) :
    (∫ x, TensorMetricTest.lineMetricTestPair b n B w (RoughAnti.lineCovectorFullRoughLaplacian b n B G A a) c x ∂μ) =
      ∫ x, RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c x ∂μ := by
  let N := ConnectionSymbols.lineCovectorConnectionDerivative n G A a
  have hN : ContDiff ℝ ∞ N := CovectorConnectionSupport.lineCovectorConnectionDerivative_global_smooth n G A a hU hG hA ha hs
  have hz := TensorIntegration.lineCovectorTensorDivergence_integral_zero μ b n B G A w N c hU hB hw hN.contDiffOn hc hcc hcs hBs hpos hmetric hGs hweight
  have hL := RoughDivergence.lineCovectorFullRoughCrossPair_integrable μ b n B G A w a c hU hB hG hA hw ha hs hc hcc hcs hBs hpos
  have hE := RoughDivergence.lineCovectorFullEnergyPair_integrable μ b n B G A w a c hU hB hG hA hw ha hs hc hcc hcs hBs hpos
  have heq (x : E) :
      (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x *
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (TensorMetricTest.lineCovectorTensorDivergence b n B G A N x) (c x) +
          ∑ i, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
            (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap))
            (ConnectionSymbols.lineCovectorConnectionDerivative n G A c x (b i))) =
      -TensorMetricTest.lineMetricTestPair b n B w (RoughAnti.lineCovectorFullRoughLaplacian b n B G A a) c x +
        RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c x := by
    unfold TensorMetricTest.lineMetricTestPair
    rw [RoughDivergence.lineCovectorFullRoughLaplacian_divergence b n B G A a (hN.differentiable (by simp) x)]
    simp only [RoughDivergence.lineCovectorFullEnergyPair,
      Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_neg_left, CovectorTensorAlgebra.covectorTensorMetricPair, N]
    ring
  simp_rw [heq] at hz
  have hi := integral_add hL.neg hE
  simp only [Pi.neg_apply] at hi
  rw [hi, integral_neg] at hz
  linear_combination -hz

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughCrossIntegral
