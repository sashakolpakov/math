import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionCoefficientComplex
import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorCoefficient

/-! # Connection Energy Matrix -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionEnergyMatrix

noncomputable section

/-! The genuine full covariant energy is the explicit positive gradient matrix applied to ordinary derivatives plus the original line-connection coefficient. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem lineCovectorFullEnergyPair_matrix (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (hw : w x = Complex.ofReal (w x).re) :
    let K := ConnectionCoefficientComplex.lineGradientConnectionCoefficient b n (G x) (A x)
    let v := TensorGradientCoordinates.covectorTensorGradientCoordinates b n (fderiv ℝ a x)
    let t := TensorGradientCoordinates.covectorTensorGradientCoordinates b n (fderiv ℝ c x)
    (1 / 2 : ℝ) * (RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c x).re =
      inner ℝ (GradientTensorCoefficient.covectorGradientCoefficient b n (B x) ((1 / 2 : ℝ) * ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) * (w x).re)
        (v + K (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (a x)))) (t + K (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (c x))) := by
  dsimp only
  rw [GradientTensorCoefficient.covectorGradientCoefficient_pair,
    ConnectionCoefficientComplex.lineCovectorConnectionDerivative_gradient_coordinates, ConnectionCoefficientComplex.lineCovectorConnectionDerivative_gradient_coordinates]
  unfold RoughDivergence.lineCovectorFullEnergyPair
  rw [hw]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero, mul_assoc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionEnergyMatrix
