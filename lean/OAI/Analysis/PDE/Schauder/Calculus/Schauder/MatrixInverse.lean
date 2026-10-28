import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MatrixFunctional
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PerturbationInverse
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.MatrixMaximum

/-! Matrix-coefficient solvability and C²→C²,α regularity without a prior Hölder-Hessian premise. -/

noncomputable section
open Set Metric Filter Laplacian
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem nondivergenceOperator_one_sub {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    nondivergenceOperator (fun y => 1 - A y) u x = laplacian u x - nondivergenceOperator A u x := by
  rw [laplacian_sub_nondivergenceOperator]
  rfl

theorem matrixCoefficient_small {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ < 1) :
    2 * ‖matrixCoefficientField B‖ * ‖poissonHolderOperator hm hα hα1 R‖ < 1 := by
  apply lt_of_le_of_lt _ hsmall
  gcongr
  exact norm_matrixCoefficientField_le B

def smallMatrixSolutionOperator {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ < 1) :
    SupportedHolder m α R →L[ℝ] GlobalC2Holder m α :=
  smallCoefficientSolutionOperator hm hα hα1 (matrixCoefficientField B)
    (fun x hx => matrixCoefficientField_zero B x (hB x hx))
    (matrixCoefficient_small hm hα hα1 B hsmall)

theorem smallMatrixSolutionOperator_solves {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ < 1)
    (f : SupportedHolder m α R) (x : EuclideanSpace ℝ (Fin m)) :
    nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y)
      (globalC2Value (smallMatrixSolutionOperator hm hα hα1 B hB hsmall f)) x = OAI.Analysis.PDE.Schauder.SupportedHolder.value f x := by
  rw [nondivergenceOperator_one_sub]
  exact smallCoefficientSolutionOperator_solves hm hα hα1 (matrixCoefficientField B)
    (fun x hx => matrixCoefficientField_zero B x (hB x hx))
    (matrixCoefficient_small hm hα hα1 B hsmall) f x

theorem smallMatrixSolutionOperator_tendsto_zero {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ < 1)
    (f : SupportedHolder m α R) :
    Tendsto (globalC2Value (smallMatrixSolutionOperator hm hα hα1 B hB hsmall f)) (cocompact _) (𝓝 0) :=
  smallCoefficientSolutionOperator_tendsto_zero hm hα hα1 (matrixCoefficientField B)
    (fun x hx => matrixCoefficientField_zero B x (hB x hx))
    (matrixCoefficient_small hm hα hα1 B hsmall) f

theorem compact_C2_small_coefficient_holder {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hsmall : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ < 1)
    (hPD : ∀ x, (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B x).PosDef)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (f : SupportedHolder m α R)
    (heq : ∀ x, nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.PDE.Schauder.SupportedHolder.value f x) :
    ∃ U : GlobalC2Holder m α, globalC2Value U = u ∧
      ‖U‖ ≤ ‖smallMatrixSolutionOperator hm hα hα1 B hB hsmall‖ * ‖f‖ := by
  let T := smallMatrixSolutionOperator hm hα hα1 B hB hsmall
  refine ⟨T f, ?_, T.le_opNorm f⟩
  apply matrix_uniqueness_at_infinity (by omega) (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) hPD
    (globalC2Value (T f)) u (contDiff_globalC2Value _) hu
  · intro x
    exact (smallMatrixSolutionOperator_solves hm hα hα1 B hB hsmall f x).trans (heq x).symm
  · exact smallMatrixSolutionOperator_tendsto_zero hm hα hα1 B hB hsmall f
  · exact compactSupport_tendsto_zero u huc

end OAI.Analysis.PDE.Schauder
