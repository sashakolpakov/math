import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughAnti

/-! # Rough Smooth -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughSmooth

noncomputable section

/-! Smoothness of the native covariant tensor divergence and rough Laplacian on the actual coefficient domain. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  CovectorConnectionOperator.lineOperator_endNormed CovectorConnectionOperator.lineOperator_endSpace

section Linear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lineCovectorTensorDerivative_smoothOn (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U : Set E} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (hN : ContDiffOn ℝ ∞ N U) (v : E) :
    ContDiffOn ℝ ∞ (fun x => HessianBilinear.lineCovectorTensorDerivative n G A N x v) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ N) U := hN.fderiv_of_isOpen hU (by simp)
  have hGv := hG.clm_apply (contDiffOn_const (c := v))
  have hAv := hA.clm_apply (contDiffOn_const (c := v))
  have hL := (CovectorConnectionOperator.covectorActionOperator (E := E) n).contDiff.comp_contDiffOn hGv
  exact (((hD.clm_apply contDiffOn_const).sub (hN.clm_comp hGv)).sub
    (hL.clm_comp hN)).add (hAv.smul hN)

end Linear

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem lineCovectorTensorDivergence_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (hN : ContDiffOn ℝ ∞ N U) (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (TensorMetricTest.lineCovectorTensorDivergence b n B G A N) U := by
  have hS := Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos
  apply ContDiffOn.sum
  intro i _
  exact (lineCovectorTensorDerivative_smoothOn n G A N hU hG hA hN (b i)).clm_apply
    (hS.clm_apply contDiffOn_const)

local instance roughSmooth_metricNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance roughSmooth_metricSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance roughSmooth_connectionNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance roughSmooth_connectionSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem lineCovectorRoughLaplacian_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (ha : ContDiffOn ℝ ∞ a U) (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ContDiffOn ℝ ∞ (RoughAnti.lineCovectorRoughLaplacian b n B G A a) U := by
  have hN := ((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)).restrictScalars ℝ).contDiff.comp_contDiffOn
    (CovectorNeg.lineCovectorConnectionDerivative_smoothOn n G A a hU hG hA ha)
  exact (lineCovectorTensorDivergence_smoothOn b n B G A _ hU hB hG hA hN hpos).neg

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughSmooth
