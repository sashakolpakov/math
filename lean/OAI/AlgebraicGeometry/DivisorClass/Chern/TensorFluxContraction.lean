import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorCutoffBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest

/-! # Tensor Flux Contraction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TensorFluxContraction

noncomputable section

/-! Exact contraction of the native tensor flux against a real covector. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem lineTensorFlux_contract (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (ξ : E →L[ℝ] ℝ) (x : E) :
    (∑ i, Line.TensorMetricTest.lineTensorFlux b n B w N a i x * (ξ (b i) : ℂ)) =
      (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * (w x *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) ξ)) (a x)) := by
  have hp := TensorCutoffBound.covectorTensorMetricPair_rankOne_right b n (B x) (N x) ξ (a x)
  simp only [CovectorTensorAlgebra.covectorTensorMetricPair, ContinuousLinearMap.smulRight_apply,
    Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_real_smul_right, Complex.real_smul] at hp
  calc
    _ = (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * (w x *
        ∑ i, (ξ (b i) : ℂ) * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
          (N x (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)) (a x)) := by
      simp only [Line.TensorMetricTest.lineTensorFlux, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [hp]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TensorFluxContraction
