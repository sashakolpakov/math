import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.DerivationExponential

/-! # Adjoint Exponential Conjugation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointExponentialConjugation.Construction

noncomputable section

/-! The exponential of a represented commutator operator is matrix
conjugation by the exponential in the ambient algebra. -/

open scoped Classical
open NormedSpace

theorem exp_represented_commutator
    {L A : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (i : L →L[ℝ] A) (D : L →L[ℝ] L) (a : A)
    (hD : ∀ x, i (D x) = a * i x - i x * a) (x : L) :
    i (exp D x) = exp a * i x * exp (-a) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  let F : ℝ → A := fun t => exp (t • (-a)) * i (exp (t • D) x) * exp (t • a)
  have hd (t : ℝ) : HasDerivAt F 0 t := by
    have hl := hasDerivAt_exp_smul_const (-a) t
    have hm := i.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_exp_smul_const' D t).clm_apply (hasDerivAt_const t x))
    have hr := hasDerivAt_exp_smul_const' a t
    have hf := (hl.mul hm).mul hr
    convert! hf using 1
    simp only [mul_apply_eq_comp, map_zero, add_zero, Function.comp_apply, Pi.mul_apply]
    rw [hD]
    noncomm_ring
  have hc : F 1 = F 0 := is_const_of_deriv_eq_zero
    (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  have hi : exp a * exp (-a) = (1 : A) := by
    rw [← exp_add_of_commute (Commute.refl a).neg_right, add_neg_cancel, exp_zero]
  have he := congrArg (fun z => exp a * z * exp (-a)) hc
  simp only [F, one_smul, zero_smul, exp_zero, one_apply_eq_self,
    one_mul, mul_one, ← mul_assoc, hi] at he
  simpa only [mul_assoc, hi, mul_one] using he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointExponentialConjugation.Construction
