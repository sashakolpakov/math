import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughDivergence
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorAlgebra

/-! # Energy Expansion -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.EnergyExpansion

noncomputable section

/-! Exact separation of ordinary derivatives and lower-order connection terms in the native full energy. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace
  CovectorConnectionOperator.lineOperator_formNormed CovectorConnectionOperator.lineOperator_formSpace CovectorConnectionOperator.lineOperator_endNormed CovectorConnectionOperator.lineOperator_endSpace

section Linear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def lineCovectorConnectionValueTensor (n : ℕ) (G : E →L[ℝ] E →L[ℝ] E)
    (A : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  (CovectorConnectionOperator.lineCovectorConnectionOperator n G A).flip a

theorem lineCovectorConnectionDerivative_tensor_split (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A a x =
      fderiv ℝ a x + lineCovectorConnectionValueTensor n (G x) (A x) (a x) := by
  ext v
  rw [CovectorConnectionOperator.lineCovectorConnectionDerivative_operator, OperatorConnectionCurvature.operatorConnectionDerivative]
  rfl

end Linear

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def lineOrdinaryTensorPair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (w : ℂ) (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : ℂ :=
  (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b B : ℂ) * w * CovectorTensorAlgebra.covectorTensorMetricPair b n B N P

theorem lineCovectorFullEnergyPair_expansion (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    let K := lineCovectorConnectionValueTensor n (G x) (A x)
    RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c x =
      lineOrdinaryTensorPair b n (B x) (w x) (fderiv ℝ a x) (fderiv ℝ c x) +
      lineOrdinaryTensorPair b n (B x) (w x) (K (a x)) (fderiv ℝ c x) +
      lineOrdinaryTensorPair b n (B x) (w x) (fderiv ℝ a x) (K (c x)) +
      lineOrdinaryTensorPair b n (B x) (w x) (K (a x)) (K (c x)) := by
  dsimp only
  unfold RoughDivergence.lineCovectorFullEnergyPair lineOrdinaryTensorPair
  rw [lineCovectorConnectionDerivative_tensor_split, lineCovectorConnectionDerivative_tensor_split,
    CovectorTensorAlgebra.covectorTensorMetricPair_add_add]
  exact mul_add _ _ _ |>.trans (congrArg₂ (· + ·) (mul_add _ _ _ |>.trans
    (congrArg₂ (· + ·) (mul_add _ _ _) rfl)) rfl)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.EnergyExpansion
