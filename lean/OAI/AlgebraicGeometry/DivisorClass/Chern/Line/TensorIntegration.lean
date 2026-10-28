import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest

/-! # Tensor Integration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorIntegration

noncomputable section

/-! Compactly supported tests eliminate every boundary term from the actual line tensor divergence. -/

open _root_.MeasureTheory Filter
open scoped ContDiff _root_.Topology ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]

omit μ [Measure.IsAddHaarMeasure μ] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [LinearOrder ι] [FiniteDimensional ℝ E] in
theorem lineCovectorConnectionDerivative_off_support (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (hx : x ∉ tsupport a) (v : E) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A a x v = 0 := by
  rw [ConnectionSymbols.lineCovectorConnectionDerivative_apply, Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply,
    fderiv_of_notMem_tsupport ℝ hx, image_eq_zero_of_notMem_tsupport hx]
  simp

theorem lineCovectorTensorDivergence_integral_zero (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (w : E → ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hw : ContDiffOn ℝ ∞ w U) (hN : ContDiffOn ℝ ∞ N U)
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hs : tsupport a ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hG : ∀ x ∈ U, ∀ v p q, B x (G x v p) q + B x p (G x v q) = fderiv ℝ B x v p q)
    (hGs : ∀ x ∈ U, ∀ v t, G x v t = G x t v)
    (hA : ∀ x ∈ U, ∀ v, fderiv ℝ w x v = w x * (conj (A x v) + A x v)) :
    (∫ x, (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x *
      (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (TensorMetricTest.lineCovectorTensorDivergence b n B G A N x) (a x) +
        ∑ i, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
          (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap))
          (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x (b i))) ∂μ) = 0 := by
  have hf (i : ι) := TensorMetricTest.lineTensorFlux_smooth b n B w N a hU hB hw hN ha hs hBs hpos i
  have hc (i : ι) := TensorMetricTest.lineTensorFlux_hasCompactSupport b n B w N a hac i
  have heq (x : E) :
      (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x *
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (TensorMetricTest.lineCovectorTensorDivergence b n B G A N x) (a x) +
          ∑ i, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
            (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap))
            (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x (b i))) =
        ∑ i, fderiv ℝ (TensorMetricTest.lineTensorFlux b n B w N a i) x (b i) := by
    by_cases hx : x ∈ U
    · exact (TensorMetricTest.lineCovectorTensorDivergence_pair b n B G A w N a hU hB hpos hx
        ((hw.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
        ((hN.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
        (ha.differentiable (by simp) x)
        (((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity_smoothOn b B hB hBs hpos).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
        (hBs x hx) (hG x hx) (hGs x hx) (hA x hx)).symm
    · have hxa : x ∉ tsupport a := fun ht => hx (hs ht)
      have hz (i : ι) : x ∉ tsupport (TensorMetricTest.lineTensorFlux b n B w N a i) :=
        fun ht => hxa (TensorMetricTest.lineTensorFlux_tsupport b n B w N a i ht)
      simp only [image_eq_zero_of_notMem_tsupport hxa, lineCovectorConnectionDerivative_off_support n G A a hxa,
        fderiv_of_notMem_tsupport ℝ (hz _), Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero,
        inner_zero_right, zero_apply, Finset.sum_const_zero, add_zero, mul_zero]
  simp_rw [heq]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.smooth_directional_derivative _ (hf i) (b i)).continuous.integrable_of_hasCompactSupport
      ((hc i).fderiv_apply ℝ (b i)))]
  simp only [TensorMetricTest.compact_smooth_directional_integral_zero μ _ (hf _) (hc _), Finset.sum_const_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorIntegration
