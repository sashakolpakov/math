import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughAnti
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughIntegrability

/-! # Rough Divergence -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughDivergence

noncomputable section

section

/-! Genuine full covariant energy and integrability of its compact chart pairings. -/

open _root_.MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  RoughSmooth.roughSmooth_metricNormed RoughSmooth.roughSmooth_metricSpace RoughSmooth.roughSmooth_connectionNormed RoughSmooth.roughSmooth_connectionSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
theorem lineCovectorFullRoughLaplacian_divergence (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (ha : DifferentiableAt ℝ (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x) :
    RoughAnti.lineCovectorFullRoughLaplacian b n B G A a x =
      -TensorMetricTest.lineCovectorTensorDivergence b n B G A (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x := by
  simp only [RoughAnti.lineCovectorFullRoughLaplacian, TensorMetricTest.lineCovectorTensorDivergence,
    HessianBilinear.lineCovectorTensorDerivative_hessian n G A a ha]

def lineCovectorFullEnergy (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : ℂ :=
  (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x * CovectorTensorAlgebra.covectorTensorMetricPair b n (B x)
    (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x) (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x)

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem lineCovectorFullRoughPair_integrable (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (hw : ContDiffOn ℝ ∞ w U) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hs : tsupport a ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    Integrable (TensorMetricTest.lineMetricTestPair b n B w (RoughAnti.lineCovectorFullRoughLaplacian b n B G A a) a) μ := by
  have hN := CovectorConnectionSupport.lineCovectorConnectionDerivative_global_smooth n G A a hU hG hA ha hs
  have heq : RoughAnti.lineCovectorFullRoughLaplacian b n B G A a =
      fun x => -TensorMetricTest.lineCovectorTensorDivergence b n B G A (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x :=
    funext (fun x => lineCovectorFullRoughLaplacian_divergence b n B G A a (hN.differentiable (by simp) x))
  rw [heq]
  exact TensorMetricTest.lineMetricTestPair_integrable μ b n B w _ a hU hB hw
    (RoughSmooth.lineCovectorTensorDivergence_smoothOn b n B G A _ hU hB hG hA hN.contDiffOn hpos).neg ha hac hs hBs hpos

theorem lineCovectorFullEnergy_integrable (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (hw : ContDiffOn ℝ ∞ w U) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hs : tsupport a ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    Integrable (lineCovectorFullEnergy b n B G A w a) μ := by
  let M := ConnectionSymbols.lineCovectorConnectionDerivative n G A a
  have hM : ContDiff ℝ ∞ M := CovectorConnectionSupport.lineCovectorConnectionDerivative_global_smooth n G A a hU hG hA ha hs
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos
  have hi (i : ι) : Integrable (TensorMetricTest.lineMetricTestPair b n B w
      (fun x => M x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)) (fun x => M x (b i))) μ := by
    have ht := CovectorConnectionSupport.lineCovectorConnectionDerivative_column_tsupport n G A a (b i)
    have hsi : ContDiffOn ℝ ∞ (fun x => Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) U :=
      hS.clm_apply (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))
    exact TensorMetricTest.lineMetricTestPair_integrable μ b n B w _ _ hU hB hw
      (hM.contDiffOn.clm_apply hsi) (hM.clm_apply contDiff_const)
      (hac.isCompact.of_isClosed_subset (isClosed_tsupport _) ht) (ht.trans hs) hBs hpos
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  unfold lineCovectorFullEnergy CovectorTensorAlgebra.covectorTensorMetricPair
  simp only [Finset.mul_sum]
  simpa only [TensorMetricTest.lineMetricTestPair, M] using hsum

end

section

/-! Integration of the full covariant rough Laplacian gives the full original first-derivative energy. -/

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

theorem lineCovectorFullRoughLaplacian_integral_pair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (hw : ContDiffOn ℝ ∞ w U) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hs : tsupport a ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hmetric : ∀ x ∈ U, ∀ v p q, B x (G x v p) q + B x p (G x v q) = fderiv ℝ B x v p q)
    (hGs : ∀ x ∈ U, ∀ v t, G x v t = G x t v)
    (hweight : ∀ x ∈ U, ∀ v, fderiv ℝ w x v = w x * (conj (A x v) + A x v)) :
    (∫ x, TensorMetricTest.lineMetricTestPair b n B w (RoughAnti.lineCovectorFullRoughLaplacian b n B G A a) a x ∂μ) =
      ∫ x, lineCovectorFullEnergy b n B G A w a x ∂μ := by
  let N := ConnectionSymbols.lineCovectorConnectionDerivative n G A a
  have hN : ContDiff ℝ ∞ N := CovectorConnectionSupport.lineCovectorConnectionDerivative_global_smooth n G A a hU hG hA ha hs
  have hz := TensorIntegration.lineCovectorTensorDivergence_integral_zero μ b n B G A w N a hU hB hw hN.contDiffOn ha hac hs hBs hpos hmetric hGs hweight
  have hL := lineCovectorFullRoughPair_integrable μ b n B G A w a hU hB hG hA hw ha hac hs hBs hpos
  have hE := lineCovectorFullEnergy_integrable μ b n B G A w a hU hB hG hA hw ha hac hs hBs hpos
  have heq (x : E) :
      (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x *
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (TensorMetricTest.lineCovectorTensorDivergence b n B G A N x) (a x) +
          ∑ i, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
            (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap))
            (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x (b i))) =
      -TensorMetricTest.lineMetricTestPair b n B w (RoughAnti.lineCovectorFullRoughLaplacian b n B G A a) a x +
        lineCovectorFullEnergy b n B G A w a x := by
    unfold TensorMetricTest.lineMetricTestPair
    rw [lineCovectorFullRoughLaplacian_divergence b n B G A a (hN.differentiable (by simp) x)]
    simp only [lineCovectorFullEnergy,
      Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_neg_left, CovectorTensorAlgebra.covectorTensorMetricPair, N]
    ring
  simp_rw [heq] at hz
  have hi := integral_add hL.neg hE
  simp only [Pi.neg_apply] at hi
  rw [hi, integral_neg] at hz
  linear_combination -hz

end

/-! The full covariant derivative pairing for two independent compact chart fields. -/

open _root_.MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  RoughSmooth.roughSmooth_metricNormed RoughSmooth.roughSmooth_metricSpace RoughSmooth.roughSmooth_connectionNormed RoughSmooth.roughSmooth_connectionSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def lineCovectorFullEnergyPair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : ℂ :=
  (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x * CovectorTensorAlgebra.covectorTensorMetricPair b n (B x)
    (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x) (ConnectionSymbols.lineCovectorConnectionDerivative n G A c x)

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem lineCovectorFullRoughCrossPair_integrable (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (hw : ContDiffOn ℝ ∞ w U) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ U)
    (hc : ContDiff ℝ ∞ c) (hcc : HasCompactSupport c) (hcs : tsupport c ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    Integrable (TensorMetricTest.lineMetricTestPair b n B w (RoughAnti.lineCovectorFullRoughLaplacian b n B G A a) c) μ := by
  have hN := CovectorConnectionSupport.lineCovectorConnectionDerivative_global_smooth n G A a hU hG hA ha hs
  have heq : RoughAnti.lineCovectorFullRoughLaplacian b n B G A a =
      fun x => -TensorMetricTest.lineCovectorTensorDivergence b n B G A (ConnectionSymbols.lineCovectorConnectionDerivative n G A a) x :=
    funext (fun x => lineCovectorFullRoughLaplacian_divergence b n B G A a (hN.differentiable (by simp) x))
  rw [heq]
  exact TensorMetricTest.lineMetricTestPair_integrable μ b n B w _ c hU hB hw
    (RoughSmooth.lineCovectorTensorDivergence_smoothOn b n B G A _ hU hB hG hA hN.contDiffOn hpos).neg hc hcc hcs hBs hpos

theorem lineCovectorFullEnergyPair_integrable (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (hw : ContDiffOn ℝ ∞ w U) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ U)
    (hc : ContDiff ℝ ∞ c) (hcc : HasCompactSupport c) (hcs : tsupport c ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    Integrable (lineCovectorFullEnergyPair b n B G A w a c) μ := by
  let M := ConnectionSymbols.lineCovectorConnectionDerivative n G A a
  let N := ConnectionSymbols.lineCovectorConnectionDerivative n G A c
  have hM : ContDiff ℝ ∞ M := CovectorConnectionSupport.lineCovectorConnectionDerivative_global_smooth n G A a hU hG hA ha hs
  have hN : ContDiff ℝ ∞ N := CovectorConnectionSupport.lineCovectorConnectionDerivative_global_smooth n G A c hU hG hA hc hcs
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos
  have hi (i : ι) : Integrable (TensorMetricTest.lineMetricTestPair b n B w
      (fun x => M x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)) (fun x => N x (b i))) μ := by
    have ht := CovectorConnectionSupport.lineCovectorConnectionDerivative_column_tsupport n G A c (b i)
    have hsi : ContDiffOn ℝ ∞ (fun x => Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) U :=
      hS.clm_apply (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))
    exact TensorMetricTest.lineMetricTestPair_integrable μ b n B w _ _ hU hB hw
      (hM.contDiffOn.clm_apply hsi) (hN.clm_apply contDiff_const)
      (hcc.isCompact.of_isClosed_subset (isClosed_tsupport _) ht) (ht.trans hcs) hBs hpos
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  unfold lineCovectorFullEnergyPair CovectorTensorAlgebra.covectorTensorMetricPair
  simp only [Finset.mul_sum]
  simpa only [TensorMetricTest.lineMetricTestPair, M, N] using hsum

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughDivergence
