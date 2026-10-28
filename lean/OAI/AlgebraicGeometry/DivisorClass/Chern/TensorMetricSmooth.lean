import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricRe
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest

/-! # Tensor Metric Smooth -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricSmooth

noncomputable section

/-! Local smoothness of the native tensor pairing and divergence flux. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem covectorTensorMetricPair_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (N P : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hN : ContDiffOn ℝ ∞ N U) (hP : ContDiffOn ℝ ∞ P U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (fun x => CovectorTensorAlgebra.covectorTensorMetricPair b n (B x) (N x) (P x)) U := by
  apply ContDiffOn.sum
  intro i _
  have hS := (Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos).clm_apply
    (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))
  exact Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth.Constructions.bilinearFormMetricPair_smoothOn b n B _ _ hB (hN.clm_apply hS)
    (hP.clm_apply contDiffOn_const)
    (fun x hx => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) (hBs x hx) (hpos x hx))

theorem lineTensorFlux_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hw : ContDiffOn ℝ ∞ w U)
    (hN : ContDiffOn ℝ ∞ N U) (ha : ContDiffOn ℝ ∞ a U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) (i : ι) :
    ContDiffOn ℝ ∞ (Line.TensorMetricTest.lineTensorFlux b n B w N a i) U := by
  have hS := (Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos).clm_apply
    (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))
  have hp := Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth.Constructions.bilinearFormMetricPair_smoothOn b n B _ a hB (hN.clm_apply hS) ha
    (fun x hx => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) (hBs x hx) (hpos x hx))
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity_smoothOn b B hB hBs hpos)).mul (hw.mul hp)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricSmooth
