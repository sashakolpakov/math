import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ChangeDerivative
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketConstraints

/-! # Exponential Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ExponentialEquiv.Construction

noncomputable section

/-! Operator exponentials are continuous changes of basis, so the
exponential perturbation preserves the full Lie bracket equations. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]

def continuousLinearMapExpEquiv [CompleteSpace L] (A : L →L[ℝ] L) : L ≃L[ℝ] L := by
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hi : exp (-A) * exp A = (1 : L →L[ℝ] L) := by
    rw [← exp_add_of_commute (Commute.refl A).neg_left, neg_add_cancel, exp_zero]
  have hj : exp A * exp (-A) = (1 : L →L[ℝ] L) := by
    rw [← exp_add_of_commute (Commute.refl A).neg_right, add_neg_cancel, exp_zero]
  exact {
    toLinearEquiv := {
      toLinearMap := (exp A).toLinearMap
      invFun := (exp (-A) : L →L[ℝ] L)
      left_inv x := DFunLike.congr_fun hi x
      right_inv x := DFunLike.congr_fun hj x }
    continuous_toFun := (exp A).continuous
    continuous_invFun := (exp (-A)).continuous }

theorem continuousLinearMapExpEquiv_apply [CompleteSpace L] (A : L →L[ℝ] L) (x : L) :
    continuousLinearMapExpEquiv A x = exp A x := rfl

theorem continuousLinearMapExpEquiv_symm_apply [CompleteSpace L] (A : L →L[ℝ] L) (x : L) :
    (continuousLinearMapExpEquiv A).symm x = exp (-A) x := rfl

theorem continuousBracketExponentialPerturbation_add [CompleteSpace L]
    (B C : L →L[ℝ] L →L[ℝ] L) (A : L →L[ℝ] L) :
    B + ChangeDerivative.Construction.continuousBracketExponentialPerturbation B (A, C) =
      ContinuousBracketChange.Construction.continuousBracketChange (continuousLinearMapExpEquiv A) (B + C) := by
  change B + (ContinuousBracketChange.Construction.continuousBracketTransform (exp A) (exp (-A)) (B + C) - B) =
    ContinuousBracketChange.Construction.continuousBracketTransform (exp A) (exp (-A)) (B + C)
  abel

theorem continuousBracketExponentialPerturbation_preserves [FiniteDimensional ℝ L]
    (B C : L →L[ℝ] L →L[ℝ] L) (A : L →L[ℝ] L) :
    ContinuousBracketConstraints.Construction.IsContinuousLieBracket (B + ChangeDerivative.Construction.continuousBracketExponentialPerturbation B (A, C)) ↔
      ContinuousBracketConstraints.Construction.IsContinuousLieBracket (B + C) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  rw [continuousBracketExponentialPerturbation_add, ContinuousBracketConstraints.Construction.isContinuousLieBracket_change_iff]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ExponentialEquiv.Construction
