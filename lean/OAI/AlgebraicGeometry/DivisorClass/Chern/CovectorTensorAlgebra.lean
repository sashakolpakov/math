import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.MetricTrace
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest

/-! # Covector Tensor Algebra -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorAlgebra

noncomputable section

section

/-! Nonnegativity of the genuine inverse-metric contraction of covector-valued tensors. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def covectorTensorMetricPair (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : ℂ :=
  ∑ i, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (N (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)) (P (b i))

def covectorTensorRealBilinear (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (N v) (P w)).re)
    (fun v t w => by rw [map_add, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left, Complex.add_re])
    (fun r v w => by rw [map_smul, Line.TensorMetricTest.bilinearFormMetricPair_real_smul_left]; simp [Complex.real_smul])
    (fun v w t => by rw [map_add, Line.ConnectionOperator.bilinearFormMetricPair_add_right, Complex.add_re])
    (fun r v w => by rw [map_smul, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_real_smul_right]; simp [Complex.real_smul])

theorem covectorTensorMetricPair_nonneg (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    0 ≤ (covectorTensorMetricPair b n B N N).re := by
  have hn (v : E) : 0 ≤ covectorTensorRealBilinear b n B N N v v := by
    change 0 ≤ (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (N v) (N v)).re
    rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b n B hB hpos]
    exact Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg n _
  have h := Positive.MetricTrace.bilinearMetric_trace_nonneg B hB hpos b (covectorTensorRealBilinear b n B N N) hn
  simpa only [covectorTensorMetricPair, Complex.re_sum, covectorTensorRealBilinear, LinearMap.mk₂_apply] using h

end

/-! Complex bilinearity rules for the actual covector tensor metric pairing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem covectorTensorMetricPair_add_left (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (N P Q : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    covectorTensorMetricPair b n B (N + P) Q =
      covectorTensorMetricPair b n B N Q + covectorTensorMetricPair b n B P Q := by
  simp only [covectorTensorMetricPair, _root_.add_apply, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left,
    Finset.sum_add_distrib]

theorem covectorTensorMetricPair_add_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (N P Q : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    covectorTensorMetricPair b n B N (P + Q) =
      covectorTensorMetricPair b n B N P + covectorTensorMetricPair b n B N Q := by
  simp only [covectorTensorMetricPair, _root_.add_apply, Line.ConnectionOperator.bilinearFormMetricPair_add_right,
    Finset.sum_add_distrib]

theorem covectorTensorMetricPair_add_add (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (N P Q R : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    covectorTensorMetricPair b n B (N + P) (Q + R) =
      covectorTensorMetricPair b n B N Q + covectorTensorMetricPair b n B P Q +
        covectorTensorMetricPair b n B N R + covectorTensorMetricPair b n B P R := by
  rw [covectorTensorMetricPair_add_right, covectorTensorMetricPair_add_left,
    covectorTensorMetricPair_add_left, ← add_assoc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorAlgebra
