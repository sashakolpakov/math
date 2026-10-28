import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.InvariantGram
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialIntegration

/-! # Invariant Form Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantFormDerivative.Construction

noncomputable section

/-! Differentiating invariance of a bilinear form along actual matrix
group exponential curves. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.Matrix NormedSpace

def matrixTransposeCLM {n : ℕ} :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  (show Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ from
    { toFun := Matrix.transpose
      map_add' := Matrix.transpose_add
      map_smul' := fun c A => Matrix.transpose_smul c A }).toContinuousLinearMap

theorem matrix_congruence_exponential_hasDerivAt {n : ℕ}
    (A Q : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => (exp (t • A)).transpose * Q * exp (t • A))
      (A.transpose * Q + Q * A) 0 := by
  have hd : HasDerivAt (fun t : ℝ => exp (t • A)) A 0 := by
    convert! hasDerivAt_exp_smul_const A (0 : ℝ) using 1
    simp only [zero_smul, exp_zero, Matrix.one_mul]
  have ht := (matrixTransposeCLM (n := n)).hasFDerivAt.comp_hasDerivAt 0 hd
  have hm := (ht.mul_const Q).mul hd
  convert! hm using 1
  simp [matrixTransposeCLM]
  rfl

theorem invariant_form_infinitesimal {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup ℝ n) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ g : G.RationalPoints,
      (g.val : Matrix (Fin n) (Fin n) ℝ).transpose * Q *
        (g.val : Matrix (Fin n) (Fin n) ℝ) = Q)
    (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) : A.val.transpose * Q + Q * A.val = 0 := by
  have he : (fun t : ℝ => (exp (t • A.val)).transpose * Q * exp (t • A.val)) =
      fun _ => Q := by
    funext t
    exact hQ (ExponentialIntegration.Construction.infinitesimalExponential G A t)
  have hd := matrix_congruence_exponential_hasDerivAt A.val Q
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 Q)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantFormDerivative.Construction
