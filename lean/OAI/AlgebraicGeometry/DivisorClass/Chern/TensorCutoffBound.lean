import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricRe
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorProjection

/-! # Tensor Cutoff Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TensorCutoffBound

noncomputable section

/-! The original positive tensor metric absorbs cutoff cross terms with the exact inverse-metric error. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem covectorTensorMetricPair_rankOne_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (ξ : E →L[ℝ] ℝ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    CovectorTensorAlgebra.covectorTensorMetricPair b n B N (ξ.smulRight a) =
      Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (N (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B ξ)) a := by
  have he := congrArg (fun v => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (N v) a)
    (Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions.bilinearMetricSharp_dual_expansion B b ξ)
  simp only [map_sum, map_smul, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sum_left, Line.TensorMetricTest.bilinearFormMetricPair_real_smul_left] at he
  simpa only [CovectorTensorAlgebra.covectorTensorMetricPair, ContinuousLinearMap.smulRight_apply,
    Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_real_smul_right] using he

theorem covectorTensorMetricPair_rankOne_self (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (ξ : E →L[ℝ] ℝ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    (CovectorTensorAlgebra.covectorTensorMetricPair b n B (ξ.smulRight a) (ξ.smulRight a)).re =
      ξ (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B ξ) * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a a).re := by
  rw [covectorTensorMetricPair_rankOne_right, ContinuousLinearMap.smulRight_apply,
    Line.TensorMetricTest.bilinearFormMetricPair_real_smul_left, Complex.smul_re, smul_eq_mul]

theorem covectorTensorMetricPair_young_lower (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (r : ℝ) :
    -(CovectorTensorAlgebra.covectorTensorMetricPair b n B P P).re ≤
      r ^ 2 * (CovectorTensorAlgebra.covectorTensorMetricPair b n B N N).re +
        2 * r * (CovectorTensorAlgebra.covectorTensorMetricPair b n B N P).re := by
  have hn := CovectorTensorAlgebra.covectorTensorMetricPair_nonneg b n B hB hpos (r • N + P)
  simp only [TensorMetricRe.covectorTensorMetricPair_re_add_left, TensorMetricRe.covectorTensorMetricPair_re_add_right,
    TensorMetricRe.covectorTensorMetricPair_re_real_smul_left, TensorMetricRe.covectorTensorMetricPair_re_real_smul_right] at hn
  rw [TensorMetricRe.covectorTensorMetricPair_re_symm b n B hB hpos P N] at hn
  nlinarith

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem covectorAntiTensor_cutoff_lower_bound (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
    (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))
    (M : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (ξ : E →L[ℝ] ℝ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (r : ℝ) :
    let N := Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) M;
    -ξ (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B ξ) * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a a).re ≤
      r ^ 2 * (CovectorTensorAlgebra.covectorTensorMetricPair b n B N M).re +
        2 * r * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (N (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B ξ)) a).re := by
  dsimp only
  rw [CovectorTensorProjection.covectorTensorAntiProjection_pair b n B hpos hBJ M]
  have hy := covectorTensorMetricPair_young_lower b n B hB hpos
    (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) M) (ξ.smulRight a) r
  rw [covectorTensorMetricPair_rankOne_self, covectorTensorMetricPair_rankOne_right] at hy
  simpa only [neg_mul] using hy

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TensorCutoffBound
