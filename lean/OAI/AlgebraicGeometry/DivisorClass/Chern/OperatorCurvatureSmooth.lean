import OAI.AlgebraicGeometry.DivisorClass.Chern.OperatorConnectionCurvature
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Operator Curvature Smooth -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OperatorCurvatureSmooth

noncomputable section

/-! Smoothness of the actual connection curvature, including its continuous operator dependence on the second tangent direction. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance curvatureSmooth_endNormed : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
local instance curvatureSmooth_endSpace : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
local instance curvatureSmooth_directionNormed : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] F) := inferInstance
local instance curvatureSmooth_directionSpace : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] F) := inferInstance

omit [FiniteDimensional ℝ E] in
theorem operatorConnectionCurvature_smoothOn
    (K : E → E →L[ℝ] F →L[ℝ] F) (v w : E → E) {U : Set E}
    (hU : IsOpen U) (hK : ContDiffOn ℝ ∞ K U)
    (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun x => OperatorConnectionCurvature.operatorConnectionCurvature K x (v x) (w x)) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ K) U := hK.fderiv_of_isOpen hU (by simp)
  exact ((((hD.clm_apply hv).clm_apply hw).sub ((hD.clm_apply hw).clm_apply hv)).add
    ((hK.clm_apply hv).clm_comp (hK.clm_apply hw))).sub
      ((hK.clm_apply hw).clm_comp (hK.clm_apply hv))

theorem operatorConnectionCurvatureRight_smoothOn
    (K : E → E →L[ℝ] F →L[ℝ] F) (v : E → E) {U : Set E}
    (hU : IsOpen U) (hK : ContDiffOn ℝ ∞ K U) (hv : ContDiffOn ℝ ∞ v U) :
    ContDiffOn ℝ ∞ (fun x => OperatorConnectionCurvature.operatorConnectionCurvatureRight K x (v x)) U := by
  apply contDiffOn_clm_apply.mpr
  intro w
  exact operatorConnectionCurvature_smoothOn K v (fun _ => w) hU hK hv contDiffOn_const

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OperatorCurvatureSmooth
