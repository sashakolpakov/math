import OAI.AlgebraicGeometry.DivisorClass.Chern.BilinearComplexTrace

/-! # Covector Tensor Projection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorProjection

noncomputable section

/-! The actual antiholomorphic derivative-slot projection is orthogonal for the original tensor metric. -/

open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def covectorTensorComplexBilinear (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : E →ₗ[ℝ] E →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ (fun v w => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (N v) (P w))
    (fun v t w => by rw [map_add, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left])
    (fun r v w => by rw [map_smul, Line.TensorMetricTest.bilinearFormMetricPair_real_smul_left])
    (fun v w t => by rw [map_add, Line.ConnectionOperator.bilinearFormMetricPair_add_right])
    (fun r v w => by rw [map_smul, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_real_smul_right])

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [Fintype ι] [LinearOrder ι] [FiniteDimensional ℝ E] in
theorem covectorTensorAntiProjection_idempotent (n : ℕ) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N) =
      Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N := by
  apply ContinuousLinearMap.ext
  intro v
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_I_smul]
  simp only [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  module

theorem covectorTensorAntiProjection_adjoint (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))
    (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    CovectorTensorAlgebra.covectorTensorMetricPair b n B (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N) P =
      CovectorTensorAlgebra.covectorTensorMetricPair b n B N (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) P) := by
  have hJ := BilinearComplexTrace.bilinear_metric_trace_J b B hpos hBJ (covectorTensorComplexBilinear b n B N P)
  change (∑ i, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B
      (N (Complex.I • Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)) (P (b i))) =
    -(∑ i, Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B
      (N (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)) (P (Complex.I • b i))) at hJ
  have hh : conj (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
    simp only [map_div₀, map_one, map_ofNat]
  simp only [CovectorTensorAlgebra.covectorTensorMetricPair, Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply,
    Line.ConnectionOperator.bilinearFormMetricPair_complex_smul_left, Line.ConnectionOperator.bilinearFormMetricPair_complex_smul_right,
    Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left, Line.ConnectionOperator.bilinearFormMetricPair_add_right,
    hh, Complex.conj_I, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hJ]
  ring

theorem covectorTensorAntiProjection_pair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))
    (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    CovectorTensorAlgebra.covectorTensorMetricPair b n B (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N) N =
      CovectorTensorAlgebra.covectorTensorMetricPair b n B (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N)
        (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N) := by
  have h := covectorTensorAntiProjection_adjoint b n B hpos hBJ
    (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N) N
  rw [covectorTensorAntiProjection_idempotent] at h
  exact h

theorem covectorTensorAntiProjection_nonneg (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))
    (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    0 ≤ (CovectorTensorAlgebra.covectorTensorMetricPair b n B (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N) N).re := by
  rw [covectorTensorAntiProjection_pair b n B hpos hBJ]
  exact CovectorTensorAlgebra.covectorTensorMetricPair_nonneg b n B hB hpos _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorProjection
