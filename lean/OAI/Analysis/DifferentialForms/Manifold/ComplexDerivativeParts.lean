import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum

/-! # Complex Derivative Parts -/

namespace OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts

noncomputable section

/-!
# Complex-linear and conjugate-linear parts of a real derivative

The two projections are continuous complex-linear operators on the space of
continuous real-linear maps. Their values are respectively complex-linear and
conjugate-linear in the input vector, and their sum is the original map.
-/

variable (E F : Type*)
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

/-- Precomposition by multiplication by `I`, as a continuous complex-linear
operator on the space of real-linear maps. -/
def complexInputRotationCLM : (E →L[ℝ] F) →L[ℂ] (E →L[ℝ] F) where
  toFun D := D.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
  map_add' D G := by ext v; rfl
  map_smul' c D := by ext v; rfl
  cont := continuous_id.clm_comp_const (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)

@[simp]
theorem complexInputRotationCLM_apply (D : E →L[ℝ] F) (v : E) :
    complexInputRotationCLM E F D v = D (Complex.I • v) := rfl

/-- Projection of a continuous real-linear map to its complex-linear part. -/
def complexLinearPartCLM : (E →L[ℝ] F) →L[ℂ] (E →L[ℝ] F) :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ (E →L[ℝ] F) -
    Complex.I • complexInputRotationCLM E F)

/-- Projection of a continuous real-linear map to its conjugate-linear part. -/
def complexAntilinearPartCLM : (E →L[ℝ] F) →L[ℂ] (E →L[ℝ] F) :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ (E →L[ℝ] F) +
    Complex.I • complexInputRotationCLM E F)

/-- The usual formula for the complex-linear part. -/
@[simp]
theorem complexLinearPartCLM_apply (D : E →L[ℝ] F) (v : E) :
    complexLinearPartCLM E F D v =
      (1 / 2 : ℂ) • (D v - Complex.I • D (Complex.I • v)) := rfl

/-- The usual formula for the conjugate-linear part. -/
@[simp]
theorem complexAntilinearPartCLM_apply (D : E →L[ℝ] F) (v : E) :
    complexAntilinearPartCLM E F D v =
      (1 / 2 : ℂ) • (D v + Complex.I • D (Complex.I • v)) := rfl

/-- The two parts sum to the original continuous real-linear map. -/
theorem complexDerivativeParts_add (D : E →L[ℝ] F) :
    complexLinearPartCLM E F D + complexAntilinearPartCLM E F D = D := by
  ext v
  change complexLinearPartCLM E F D v + complexAntilinearPartCLM E F D v = D v
  rw [complexLinearPartCLM_apply, complexAntilinearPartCLM_apply]
  module

/-- The complex-linear part commutes with multiplication of the input by `I`. -/
theorem complexLinearPartCLM_apply_I_smul (D : E →L[ℝ] F) (v : E) :
    complexLinearPartCLM E F D (Complex.I • v) =
      Complex.I • complexLinearPartCLM E F D v := by
  have hII : Complex.I • (Complex.I • v) = -v := by
    simp [smul_smul]
  rw [complexLinearPartCLM_apply, hII, map_neg, smul_neg, sub_neg_eq_add,
    complexLinearPartCLM_apply, smul_comm Complex.I (1 / 2 : ℂ), smul_sub,
    smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, add_comm]

/-- The conjugate-linear part conjugates multiplication of the input by `I`. -/
theorem complexAntilinearPartCLM_apply_I_smul (D : E →L[ℝ] F) (v : E) :
    complexAntilinearPartCLM E F D (Complex.I • v) =
      (-Complex.I) • complexAntilinearPartCLM E F D v := by
  have hII : Complex.I • (Complex.I • v) = -v := by
    simp [smul_smul]
  rw [complexAntilinearPartCLM_apply, hII, map_neg, smul_neg,
    complexAntilinearPartCLM_apply, smul_comm (-Complex.I) (1 / 2 : ℂ)]
  congr 1
  rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
  abel

/-- The projected map is complex-linear in the input vector. -/
theorem complexLinearPartCLM_apply_smul (D : E →L[ℝ] F) (z : ℂ) (v : E) :
    complexLinearPartCLM E F D (z • v) = z • complexLinearPartCLM E F D v := by
  have hE (r : ℝ) (w : E) : (r : ℂ) • w = r • w := algebraMap_smul ℂ r w
  have hF (r : ℝ) (w : F) : (r : ℂ) • w = r • w := algebraMap_smul ℂ r w
  rw [← Complex.re_add_im z]
  simp only [add_smul, mul_smul, hE, hF, map_add, ContinuousLinearMap.map_smul,
    complexLinearPartCLM_apply_I_smul]

/-- The projected map is conjugate-linear in the input vector. -/
theorem complexAntilinearPartCLM_apply_smul (D : E →L[ℝ] F) (z : ℂ) (v : E) :
    complexAntilinearPartCLM E F D (z • v) =
      (star z) • complexAntilinearPartCLM E F D v := by
  have hE (r : ℝ) (w : E) : (r : ℂ) • w = r • w := algebraMap_smul ℂ r w
  have hF (r : ℝ) (w : F) : (r : ℂ) • w = r • w := algebraMap_smul ℂ r w
  rw [← Complex.re_add_im z]
  simp only [add_smul, mul_smul, hE, hF, map_add, ContinuousLinearMap.map_smul,
    complexAntilinearPartCLM_apply_I_smul, star_add, star_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  rw [smul_comm z.im (-Complex.I)]

end

end OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts
