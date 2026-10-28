import OAI.AlgebraicGeometry.DivisorClass.Chern.OperatorConnectionCurvature
import Mathlib.Topology.Order.Compact

/-! # Connection Curvature Bounds -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionCurvatureBounds

noncomputable section

/-! Quantitative curvature bounds from actual connection coefficients and their derivatives. -/

open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance curvatureBounds_endNormed : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
local instance curvatureBounds_endSpace : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
local instance curvatureBounds_directionNormed : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] F) := inferInstance
local instance curvatureBounds_directionSpace : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] F) := inferInstance
local instance curvatureBounds_derivativeNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) := inferInstance
local instance curvatureBounds_derivativeSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) := inferInstance

theorem operatorConnectionCurvature_norm_le (K : E → E →L[ℝ] F →L[ℝ] F)
    (x v w : E) :
    ‖OperatorConnectionCurvature.operatorConnectionCurvature K x v w‖ ≤
      (2 * (‖fderiv ℝ K x‖ + ‖K x‖ ^ 2)) * ‖v‖ * ‖w‖ := by
  have hd (p q : E) : ‖fderiv ℝ K x p q‖ ≤ ‖fderiv ℝ K x‖ * ‖p‖ * ‖q‖ :=
    ((fderiv ℝ K x p).le_opNorm q).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ K x).le_opNorm p) (norm_nonneg q))
  have hc (p q : E) : ‖(K x p).comp (K x q)‖ ≤ (‖K x‖ * ‖p‖) * (‖K x‖ * ‖q‖) :=
    ((K x p).opNorm_comp_le (K x q)).trans
      (mul_le_mul ((K x).le_opNorm p) ((K x).le_opNorm q) (norm_nonneg _) (by positivity))
  calc
    ‖OperatorConnectionCurvature.operatorConnectionCurvature K x v w‖ ≤
        (‖fderiv ℝ K x v w‖ + ‖fderiv ℝ K x w v‖) +
          ‖(K x v).comp (K x w)‖ + ‖(K x w).comp (K x v)‖ := by
      unfold OperatorConnectionCurvature.operatorConnectionCurvature
      have h1 := norm_sub_le (fderiv ℝ K x v w) (fderiv ℝ K x w v)
      have h2 := norm_add_le (fderiv ℝ K x v w - fderiv ℝ K x w v) ((K x v).comp (K x w))
      have h3 := norm_sub_le (fderiv ℝ K x v w - fderiv ℝ K x w v + (K x v).comp (K x w)) ((K x w).comp (K x v))
      linarith only [h1, h2, h3]
    _ ≤ (‖fderiv ℝ K x‖ * ‖v‖ * ‖w‖ + ‖fderiv ℝ K x‖ * ‖w‖ * ‖v‖) +
        (‖K x‖ * ‖v‖) * (‖K x‖ * ‖w‖) + (‖K x‖ * ‖w‖) * (‖K x‖ * ‖v‖) :=
      add_le_add (add_le_add (add_le_add (hd v w) (hd w v)) (hc v w)) (hc w v)
    _ = _ := by ring

theorem operatorConnectionCurvature_bound_on_compact
    (K : E → E →L[ℝ] F →L[ℝ] F) {U T : Set E} (hU : IsOpen U)
    (hK : ContDiffOn ℝ ∞ K U) (hT : IsCompact T) (hTU : T ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ T, ∀ v w : E,
      ‖OperatorConnectionCurvature.operatorConnectionCurvature K x v w‖ ≤ C * ‖v‖ * ‖w‖ := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ K) U := hK.fderiv_of_isOpen hU (by simp)
  have hb : ContinuousOn (fun x => 2 * (‖fderiv ℝ K x‖ + ‖K x‖ ^ 2)) T :=
    continuousOn_const.mul ((hd.continuousOn.mono hTU).norm.add ((hK.continuousOn.mono hTU).norm.pow 2))
  obtain ⟨B, hB⟩ := hT.bddAbove_image hb
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  intro x hx v w
  apply (operatorConnectionCurvature_norm_le K x v w).trans
  have hbnd : 2 * (‖fderiv ℝ K x‖ + ‖K x‖ ^ 2) ≤ max B 0 + 1 :=
    (hB ⟨x, hx, rfl⟩).trans ((le_max_left B 0).trans (by linarith))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbnd (norm_nonneg v)) (norm_nonneg w)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionCurvatureBounds
