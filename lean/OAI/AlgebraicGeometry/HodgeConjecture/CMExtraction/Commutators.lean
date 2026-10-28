import OAI.Geometry.ComplexBall.Generation
import Mathlib.GroupTheory.IsPerfect

/-! # Commutators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Commutators.Local

noncomputable section

/-! Every elementary matrix in SL3 is a commutator inside SL3.
This supplies the group-theoretic input for removing scalar characters. -/

open scoped Classical _root_.Matrix commutatorElement
open _root_.Matrix _root_.Matrix.SpecialLinearGroup

variable {K : Type*} [Field K]

theorem single_mul_single_cond (i j k l : Fin 3) (a b : K) :
    single i j a * single k l b = if j = k then single i l (a * b) else 0 := by
  by_cases h : j = k
  · subst k
    simp only [ite_true, single_mul_single_same]
  · rw [ite_eq_right h]
    exact Matrix.single_mul_single_of_ne (c := a) i j k h b

theorem sl3_transvection_commutator {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (a : K) :
    transvection hij a = ⁅transvection hik a, transvection hkj (1 : K)⁆ := by
  rw [commutatorElement_def, transvection_inv, transvection_inv]
  apply Subtype.ext
  change 1 + single i j a =
    (1 + single i k a) * (1 + single k j 1) * (1 + single i k (-a)) * (1 + single k j (-1))
  simp only [mul_add, add_mul, mul_one, one_mul]
  simp only [single_mul_single_cond, hik.symm, hij.symm, hkj.symm, ite_false, ite_true,
    mul_one, one_mul, mul_neg, neg_neg, zero_mul, add_zero]
  rw [← Matrix.single_neg, ← Matrix.single_neg, ← Matrix.single_neg]
  abel

theorem sl3_commutator_eq_top : commutator (SpecialLinearGroup (Fin 3) K) = ⊤ := by
  apply top_unique
  intro g _
  apply Geometry.ComplexBall.Generation.ArithmeticQuotient.sl3_transvection_induction
    (fun g : SpecialLinearGroup (Fin 3) K => g ∈ commutator (SpecialLinearGroup (Fin 3) K)) _ _ g
  · intro i j hij a
    obtain ⟨k, hik, hkj⟩ : ∃ k : Fin 3, i ≠ k ∧ k ≠ j := by
      fin_cases i <;> fin_cases j <;> decide
    rw [sl3_transvection_commutator hij hik hkj a]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · exact fun _ _ => Subgroup.mul_mem _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Commutators.Local
