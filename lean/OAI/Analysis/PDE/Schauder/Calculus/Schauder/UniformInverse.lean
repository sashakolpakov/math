import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MatrixInverse

/-! A uniform inverse bound on a fixed small coefficient ball. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem smallMatrixSolutionOperator_norm_le {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ < 1)
    (hhalf : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ ≤ 1 / 2) :
    ‖smallMatrixSolutionOperator hm hα hα1 B hB hsmall‖ ≤
      2 * ‖poissonHolderOperator hm hα hα1 R‖ := by
  let a := matrixCoefficientField B
  have ha : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = 0 :=
    fun x hx => matrixCoefficientField_zero B x (hB x hx)
  let K := coefficientFeedback hm hα hα1 a ha
  have hK : ‖K‖ ≤ 1 / 2 := by
    apply (norm_coefficientFeedback_le hm hα hα1 a ha).trans
    apply le_trans _ hhalf
    gcongr
    exact norm_matrixCoefficientField_le B
  have hgap : 0 < 1 - ‖K‖ := by linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have hb := smallCoefficientSolutionOperator_bound hm hα hα1 a ha
    (matrixCoefficient_small hm hα hα1 B hsmall) f
  change ‖smallMatrixSolutionOperator hm hα hα1 B hB hsmall f‖ ≤
    ‖poissonHolderOperator hm hα hα1 R‖ * (‖f‖ / (1 - ‖K‖)) at hb
  have hd : ‖f‖ / (1 - ‖K‖) ≤ 2 * ‖f‖ := by
    apply (div_le_iff₀ hgap).mpr
    nlinarith [norm_nonneg f]
  calc
    _ ≤ ‖poissonHolderOperator hm hα hα1 R‖ * (‖f‖ / (1 - ‖K‖)) := hb
    _ ≤ ‖poissonHolderOperator hm hα hα1 R‖ * (2 * ‖f‖) := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = _ := by ring

end OAI.Analysis.PDE.Schauder
