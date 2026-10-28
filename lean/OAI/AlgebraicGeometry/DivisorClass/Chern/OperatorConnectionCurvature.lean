import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! # Operator Connection Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OperatorConnectionCurvature

noncomputable section

section

/-! The curvature of an actual first-order connection, obtained by commuting its derivatives. -/

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def operatorConnectionDerivative (K : E → E →L[ℝ] F →L[ℝ] F)
    (a : E → F) (x v : E) : F :=
  fderiv ℝ a x v + K x v (a x)

def operatorConnectionCurvature (K : E → E →L[ℝ] F →L[ℝ] F)
    (x v w : E) : F →L[ℝ] F :=
  fderiv ℝ K x v w - fderiv ℝ K x w v +
    (K x v).comp (K x w) - (K x w).comp (K x v)

theorem operatorConnectionDerivative_derivative (K : E → E →L[ℝ] F →L[ℝ] F)
    (a : E → F) {x : E} (hK : DifferentiableAt ℝ K x)
    (ha : ContDiffAt ℝ ∞ a x) (v w : E) :
    fderiv ℝ (fun y => operatorConnectionDerivative K a y w) x v =
      fderiv ℝ (fderiv ℝ a) x v w + fderiv ℝ K x v w (a x) +
        K x w (fderiv ℝ a x v) := by
  have hs : ContDiffAt ℝ ∞ (fderiv ℝ a) x := ha.fderiv_right (by simp)
  have hda : DifferentiableAt ℝ (fderiv ℝ a) x := hs.differentiableAt (by simp)
  have had := ha.differentiableAt (by simp)
  have hKw := hK.clm_apply (differentiableAt_const w)
  unfold operatorConnectionDerivative
  rw [fderiv_fun_add (hda.clm_apply (differentiableAt_const w)) (hKw.clm_apply had),
    fderiv_clm_apply hda (differentiableAt_const w), fderiv_clm_apply hKw had,
    fderiv_clm_apply hK (differentiableAt_const w)]
  simp only [fderiv_const_apply, _root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, _root_.zero_apply, map_zero, zero_add]
  abel

theorem operatorConnectionDerivative_commutator (K : E → E →L[ℝ] F →L[ℝ] F)
    (a : E → F) {x : E} (hK : DifferentiableAt ℝ K x)
    (ha : ContDiffAt ℝ ∞ a x) (v w : E) :
    operatorConnectionDerivative K (fun y => operatorConnectionDerivative K a y w) x v -
      operatorConnectionDerivative K (fun y => operatorConnectionDerivative K a y v) x w =
      operatorConnectionCurvature K x v w (a x) := by
  have hs := ha.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) v w
  change fderiv ℝ (fun y => operatorConnectionDerivative K a y w) x v +
      K x v (fderiv ℝ a x w + K x w (a x)) -
    (fderiv ℝ (fun y => operatorConnectionDerivative K a y v) x w +
      K x w (fderiv ℝ a x v + K x v (a x))) = _
  rw [operatorConnectionDerivative_derivative K a hK ha v w,
    operatorConnectionDerivative_derivative K a hK ha w v, hs]
  simp only [operatorConnectionCurvature, _root_.add_apply, _root_.sub_apply,
    ContinuousLinearMap.comp_apply, map_add]
  abel

end

/-! Actual connection curvature as a continuous linear operator in its second tangent direction. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def operatorConnectionCurvatureRight (K : E → E →L[ℝ] F →L[ℝ] F) (x v : E) :
    E →L[ℝ] F →L[ℝ] F :=
  fderiv ℝ K x v - (fderiv ℝ K x).flip v +
    (ContinuousLinearMap.compL ℝ F F F (K x v)).comp (K x) -
    ((ContinuousLinearMap.compL ℝ F F F).flip (K x v)).comp (K x)

theorem operatorConnectionCurvatureRight_apply (K : E → E →L[ℝ] F →L[ℝ] F) (x v w : E) :
    operatorConnectionCurvatureRight K x v w = operatorConnectionCurvature K x v w := rfl

theorem operatorConnectionCurvatureRight_bound (K : E → E →L[ℝ] F →L[ℝ] F) (x v : E)
    (C : ℝ) (hC : 0 ≤ C) (hR : ∀ w : E, ‖operatorConnectionCurvature K x v w‖ ≤ C * ‖v‖ * ‖w‖) :
    ‖operatorConnectionCurvatureRight K x v‖ ≤ C * ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg v)) hR

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OperatorConnectionCurvature
