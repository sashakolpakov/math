import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumTensor
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # Finite Sum Weights -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumWeights.Tensor

noncomputable section

/-! The tensor exponents of the actual finite-sum pullback are evaluations
of fixed rational polynomials of total degree two. -/

universe v

variable {ι : Type v} [Fintype ι]

def weightPolynomial (t : Fin (Fintype.card (ι × ι))) : MvPolynomial ι ℚ :=
  MvPolynomial.C 2 * MvPolynomial.X ((Fintype.equivFin (ι × ι)).symm t).1 *
    MvPolynomial.X ((Fintype.equivFin (ι × ι)).symm t).2

theorem weightPolynomial_eval (a : ι → ℕ) (t : Fin (Fintype.card (ι × ι))) :
    MvPolynomial.eval (fun i => (a i : ℚ)) (weightPolynomial t) = (FiniteSumTensor.weight a t : ℚ) := by
  simp only [weightPolynomial, FiniteSumTensor.weight, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Nat.cast_mul, Nat.cast_ofNat, mul_assoc]

theorem weightPolynomial_totalDegree (t : Fin (Fintype.card (ι × ι))) :
    (weightPolynomial t).totalDegree ≤ 2 := by
  have h₁ := MvPolynomial.totalDegree_mul (MvPolynomial.C (2 : ℚ))
    (MvPolynomial.X ((Fintype.equivFin (ι × ι)).symm t).1)
  have h₂ := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (2 : ℚ) * MvPolynomial.X ((Fintype.equivFin (ι × ι)).symm t).1)
    (MvPolynomial.X ((Fintype.equivFin (ι × ι)).symm t).2)
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] at h₁ h₂
  change _ ≤ 2
  exact h₂.trans (Nat.add_le_add_right h₁ 1)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumWeights.Tensor
