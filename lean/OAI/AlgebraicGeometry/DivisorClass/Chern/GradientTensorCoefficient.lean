import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricRe
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Gradient Tensor Coefficient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorCoefficient

noncomputable section

/-! The full tensor principal form is an explicit positive coefficient operator on genuine Hilbert gradient coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def covectorGradientCoefficient (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) :
    GradientTensorCoordinates.CovectorGradientCoordinates ι n →L[ℝ] GradientTensorCoordinates.CovectorGradientCoordinates ι n :=
  ∑ i, ∑ j, (r * b.repr (OAI.Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) j) •
    ((GradientTensorCoordinates.covectorGradientComponent n i).adjoint.comp
      ((OAI.Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions.realMatrixOperator (OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram b n B)⁻¹).comp (GradientTensorCoordinates.covectorGradientComponent n j)))

theorem covectorGradientCoefficient_pair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ) (v w : GradientTensorCoordinates.CovectorGradientCoordinates ι n) :
    inner ℝ (covectorGradientCoefficient b n B r v) w =
      r * (CovectorTensorAlgebra.covectorTensorMetricPair b n B (GradientTensorCoordinates.covectorGradientTensor b n v) (GradientTensorCoordinates.covectorGradientTensor b n w)).re := by
  simp only [covectorGradientCoefficient, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, sum_inner, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, GradientTensorCoordinates.covectorGradientComponent_apply]
  simp only [CovectorTensorAlgebra.covectorTensorMetricPair, GradientTensorCoordinates.covectorGradientTensor_basis]
  simp only [GradientTensorCoordinates.covectorGradientTensor_apply,
    OAI.Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sum_left, Line.TensorMetricTest.bilinearFormMetricPair_real_smul_left,
    Complex.re_sum, Complex.smul_re, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply, OAI.Analysis.HodgeTheory.Decomposition.CoordinateMetric.Constructions.euclidean_real_inner_eq_re, mul_assoc]

theorem covectorGradientCoefficient_positive (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (r : ℝ) (hr : 0 < r)
    (v : GradientTensorCoordinates.CovectorGradientCoordinates ι n) (hv : v ≠ 0) :
    0 < inner ℝ (covectorGradientCoefficient b n B r v) v := by
  rw [covectorGradientCoefficient_pair]
  apply mul_pos hr
  apply TensorMetricRe.covectorTensorMetricPair_re_pos b n B hB hpos
  intro hz
  apply hv
  exact GradientTensorCoordinates.covectorGradientTensor_injective b n (hz.trans (map_zero _).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorCoefficient
