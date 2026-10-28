import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorConnectionSupport
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorProjection

/-! # Rough Integrability -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughIntegrability

noncomputable section

/-! Both integrands in the native rough Laplacian energy formula are integrable for compact chart tests. -/

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

local instance roughEnergy_sharpNormed : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance
local instance roughEnergy_sharpSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E) := inferInstance

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def lineCovectorRoughEnergy (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : ℂ :=
  (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * w x * CovectorTensorAlgebra.covectorTensorMetricPair b n (B x)
    (RoughAnti.lineCovectorAntiDerivative n G A a x) (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x)

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]

theorem lineCovectorRoughPair_integrable (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (hw : ContDiffOn ℝ ∞ w U) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hs : tsupport a ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    Integrable (TensorMetricTest.lineMetricTestPair b n B w (RoughAnti.lineCovectorRoughLaplacian b n B G A a) a) μ :=
  TensorMetricTest.lineMetricTestPair_integrable μ b n B w _ a hU hB hw
    (RoughSmooth.lineCovectorRoughLaplacian_smoothOn b n B G A a hU hB hG hA ha.contDiffOn hpos) ha hac hs hBs hpos

theorem lineCovectorRoughEnergy_integrable (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (hw : ContDiffOn ℝ ∞ w U) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (hs : tsupport a ⊆ U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    Integrable (lineCovectorRoughEnergy b n B G A w a) μ := by
  let M := ConnectionSymbols.lineCovectorConnectionDerivative n G A a
  let N := RoughAnti.lineCovectorAntiDerivative n G A a
  have hM : ContDiff ℝ ∞ M := CovectorConnectionSupport.lineCovectorConnectionDerivative_global_smooth n G A a hU hG hA ha hs
  have hN : ContDiff ℝ ∞ N := ((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)).restrictScalars ℝ).contDiff.comp hM
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos
  have hi (i : ι) : Integrable (TensorMetricTest.lineMetricTestPair b n B w
      (fun x => N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)) (fun x => M x (b i))) μ := by
    have ht := CovectorConnectionSupport.lineCovectorConnectionDerivative_column_tsupport n G A a (b i)
    have hsi : ContDiffOn ℝ ∞ (fun x => Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) U :=
      (ContinuousLinearMap.apply ℝ E (b.coord i).toContinuousLinearMap).contDiff.comp_contDiffOn hS
    exact TensorMetricTest.lineMetricTestPair_integrable μ b n B w _ _ hU hB hw
      (hN.contDiffOn.clm_apply hsi)
      (hM.clm_apply contDiff_const)
      (hac.isCompact.of_isClosed_subset (isClosed_tsupport _) ht) (ht.trans hs) hBs hpos
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  unfold lineCovectorRoughEnergy CovectorTensorAlgebra.covectorTensorMetricPair
  simp only [Finset.mul_sum]
  simpa only [TensorMetricTest.lineMetricTestPair, M, N] using hsum

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughIntegrability
