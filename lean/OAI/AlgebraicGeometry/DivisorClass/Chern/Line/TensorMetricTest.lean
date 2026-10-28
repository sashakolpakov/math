import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.HessianBilinear
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.WeightedMetricDerivative
import OAI.Analysis.HodgeTheory.Decomposition.KoszulSmooth
import OAI.Analysis.HodgeTheory.Decomposition.ConnectionTrace
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts

/-! # Tensor Metric Test -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest

noncomputable section

section

/-! Differentiation of the actual inverse-metric tensor contraction and cancellation of the connection's volume trace. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem lineCovectorTensor_metricInsertion (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (hN : DifferentiableAt ℝ N x) (v : E)
    (hG : ∀ p q, B x (G x v p) q + B x p (G x v q) = fderiv ℝ B x v p q)
    (ξ : E →L[ℝ] ℝ) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A (fun y => N y (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B y) ξ)) x v =
      HessianBilinear.lineCovectorTensorDerivative n G A N x v (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) ξ) -
        N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (ξ.comp (G x v))) := by
  have hS := (((Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos).clm_apply
    (contDiffOn_const (c := ξ))).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [ConnectionSymbols.lineCovectorConnectionDerivative_apply, Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply,
    fderiv_clm_apply hN hS]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rw [Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_derivative B hU hB hpos hx v (G x v) hG ξ]
  simp only [HessianBilinear.lineCovectorTensorDerivative, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_neg]
  abel

theorem lineTensor_metric_trace_cancel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E →L[ℝ] E →L[ℝ] E) (hG : ∀ v w, G v w = G w v) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    (∑ i, (LinearMap.toMatrix b b (G (b i)).toLinearMap).trace •
      N (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)) =
      ∑ i, N (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B ((b.coord i).toContinuousLinearMap.comp (G (b i)))) := by
  have h := congrArg (N.comp (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B)) (Analysis.HodgeTheory.Decomposition.ConnectionTrace.Constructions.symmetricConnection_trace_covector b G hG)
  simpa only [map_sum, map_smul, ContinuousLinearMap.comp_apply] using h

end

section

/-! The actual tensor divergence is the formal adjoint of the covariant derivative for the original line and volume weights. -/

open scoped ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem bilinearFormMetricPair_real_smul_left (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (r : ℝ) :
    Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (r • a) c = r • Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c := by
  rw [Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner]
  have hQ := ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ).map_smul r a
  change Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (r • a) = r • Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a at hQ
  rw [hQ, map_smul, inner_smul_left_eq_smul]

def lineCovectorTensorDivergence (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  ∑ i, HessianBilinear.lineCovectorTensorDerivative n G A N x (b i)
    (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)

theorem lineCovectorTensorDivergence_pair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (w : E → ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (hw : DifferentiableAt ℝ w x) (hN : DifferentiableAt ℝ N x)
    (ha : DifferentiableAt ℝ a x) (hρ : DifferentiableAt ℝ (fun y => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y)) x)
    (hBs : ∀ v t, B x v t = B x t v)
    (hG : ∀ v p q, B x (G x v p) q + B x p (G x v q) = fderiv ℝ B x v p q)
    (hGs : ∀ v t, G x v t = G x t v)
    (hA : ∀ v, fderiv ℝ w x v = w x * (conj (A x v) + A x v)) :
    (∑ i, fderiv ℝ (fun y => (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) *
      (w y * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B y)
        (N y (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B y) (b.coord i).toContinuousLinearMap)) (a y))) x (b i)) =
      (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x *
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (lineCovectorTensorDivergence b n B G A N x) (a x) +
          ∑ i, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
            (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap))
            (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x (b i))) := by
  have hBd := (hB.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hS (i : ι) := (((Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos).clm_apply
    (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hd (i : ι) := WeightedMetricDerivative.lineWeightedMetricPair_derivative b n B G A w
    (fun y => N y (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B y) (b.coord i).toContinuousLinearMap)) a x (b i)
    hBd hw (hN.clm_apply (hS i)) ha hρ hBs (hpos x hx) (hG (b i)) (hA (b i))
  simp_rw [lineCovectorTensor_metricInsertion n B G A N hU hB hpos hx hN _ (hG _) _] at hd
  rw [Finset.sum_congr rfl (fun i _ => hd i), ← Finset.mul_sum]
  simp only [Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sub_left, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have ht := congrArg (fun c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) c (a x))
    (lineTensor_metric_trace_cancel b n (B x) (G x) hGs (N x))
  simp only [Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sum_left, bilinearFormMetricPair_real_smul_left] at ht
  have ht' :
      (∑ i, (LinearMap.toMatrix b b (G x (b i)).toLinearMap).trace •
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
          (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)) (a x)) =
      ∑ i, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
        (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) ((b.coord i).toContinuousLinearMap.comp (G x (b i))))) (a x) := by
    exact ht
  rw [ht', lineCovectorTensorDivergence, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sum_left]
  ring

end

section

/-! The native tensor divergence flux is smooth and compactly supported when the test form is supported inside the actual coefficient domain. -/

open _root_.MeasureTheory Filter
open scoped ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def lineTensorFlux (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (i : ι) (x : E) : ℂ :=
  (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * (w x * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
    (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)) (a x))

theorem lineTensorFlux_zero (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (i : ι) {x : E} (ha : a x = 0) :
    lineTensorFlux b n B w N a i x = 0 := by
  simp [lineTensorFlux, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, ha]

theorem lineTensorFlux_tsupport (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (i : ι) : tsupport (lineTensorFlux b n B w N a i) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  exact lineTensorFlux_zero b n B w N a i hx

theorem lineTensorFlux_smooth (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hw : ContDiffOn ℝ ∞ w U) (hN : ContDiffOn ℝ ∞ N U)
    (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) (i : ι) :
    ContDiff ℝ ∞ (lineTensorFlux b n B w N a i) := by
  have hS := (Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos).clm_apply
    (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))
  have hp := Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth.Constructions.bilinearFormMetricPair_smoothOn b n B _ a hB (hN.clm_apply hS) ha.contDiffOn
    (fun x hx => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) (hBs x hx) (hpos x hx))
  have hρ := Complex.ofRealCLM.contDiff.comp_contDiffOn (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity_smoothOn b B hB hBs hpos)
  have hf : ContDiffOn ℝ ∞ (lineTensorFlux b n B w N a i) U := hρ.mul (hw.mul hp)
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · have hz : a =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hs ht))
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    exact lineTensorFlux_zero b n B w N a i hy

theorem lineTensorFlux_hasCompactSupport (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (ha : HasCompactSupport a) (i : ι) :
    HasCompactSupport (lineTensorFlux b n B w N a i) :=
  ha.isCompact.of_isClosed_subset (isClosed_tsupport _) (lineTensorFlux_tsupport b n B w N a i)

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem compact_smooth_directional_integral_zero (f : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (v : E) :
    (∫ x, fderiv ℝ f x v ∂μ) = 0 := by
  have h := ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction.integral_mul_directional_on μ (fun _ => (1 : ℂ)) f isOpen_univ
    contDiffOn_const hf hc (Set.subset_univ _) v
  simpa only [one_mul, fderiv_const_apply, zero_apply, zero_mul, integral_zero, neg_zero] using h

end

section

/-! The actual weighted metric pairing with a compactly supported test is smooth and integrable on the chart domain. -/

open _root_.MeasureTheory Filter
open scoped ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def lineMetricTestPair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (g a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : ℂ :=
  (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (g x) (a x)

theorem lineMetricTestPair_tsupport (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (g a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    tsupport (lineMetricTestPair b n B w g a) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  simp [lineMetricTestPair, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, hx]

theorem lineMetricTestPair_smooth (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (g a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U) (hw : ContDiffOn ℝ ∞ w U)
    (hg : ContDiffOn ℝ ∞ g U) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiff ℝ ∞ (lineMetricTestPair b n B w g a) := by
  have hp := Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth.Constructions.bilinearFormMetricPair_smoothOn b n B g a hB hg ha.contDiffOn
    (fun x hx => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) (hBs x hx) (hpos x hx))
  have hρ := Complex.ofRealCLM.contDiff.comp_contDiffOn (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity_smoothOn b B hB hBs hpos)
  have hf : ContDiffOn ℝ ∞ (lineMetricTestPair b n B w g a) U := (hρ.mul hw).mul hp
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp
      (fun ht => hx (hs (lineMetricTestPair_tsupport b n B w g a ht))))

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem lineMetricTestPair_integrable (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (g a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U) (hw : ContDiffOn ℝ ∞ w U)
    (hg : ContDiffOn ℝ ∞ g U) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hs : tsupport a ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    Integrable (lineMetricTestPair b n B w g a) μ :=
  (lineMetricTestPair_smooth b n B w g a hU hB hw hg ha hs hBs hpos).continuous.integrable_of_hasCompactSupport
    (hac.isCompact.of_isClosed_subset (isClosed_tsupport _) (lineMetricTestPair_tsupport b n B w g a))

end

/-! Pointwise evaluation and vanishing of the original line metric test pairing. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicIntegrationByParts.CM.Construction

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [FiniteDimensional ℝ E] in
theorem lineMetricTestPair_constant_values (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    lineMetricTestPair b n B w (fun _ => a x) (fun _ => c x) x = lineMetricTestPair b n B w a c x := rfl

theorem lineMetricTestPair_zero_right_value (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E)
    (hc : c x = 0) : lineMetricTestPair b n B w a c x = 0 := by
  unfold lineMetricTestPair
  rw [hc, Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero, inner_zero_right, mul_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest
