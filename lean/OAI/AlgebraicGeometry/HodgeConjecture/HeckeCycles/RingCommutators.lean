import Mathlib

/-! # Ring Commutators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RingCommutators.CM

noncomputable section

/-! Elementary SL3 matrices are commutators over every commutative
ring. In particular the identity does not require division in the
coefficient ring of an integral local subgroup. -/

open scoped Classical _root_.Matrix commutatorElement
open _root_.Matrix _root_.Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R]

theorem single_product (i j k l : Fin 3) (a b : R) :
    single i j a * single k l b = if j = k then single i l (a * b) else 0 := by
  by_cases h : j = k
  · subst k
    simp only [ite_true, single_mul_single_same]
  · rw [ite_eq_right h]
    exact Matrix.single_mul_single_of_ne (c := a) i j k h b

theorem elementary_commutator {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (a : R) :
    transvection hij a = ⁅transvection hik a, transvection hkj (1 : R)⁆ := by
  rw [commutatorElement_def, transvection_inv, transvection_inv]
  apply Subtype.ext
  change 1 + single i j a =
    (1 + single i k a) * (1 + single k j 1) * (1 + single i k (-a)) * (1 + single k j (-1))
  simp only [mul_add, add_mul, mul_one, one_mul]
  simp only [single_product, hik.symm, hij.symm, hkj.symm, ite_false, ite_true,
    mul_one, one_mul, mul_neg, neg_neg, zero_mul, add_zero]
  rw [← Matrix.single_neg, ← Matrix.single_neg, ← Matrix.single_neg]
  abel

theorem elementary_mem_commutator (i j : Fin 3) (hij : i ≠ j) (a : R) :
    transvection hij a ∈ commutator (SpecialLinearGroup (Fin 3) R) := by
  obtain ⟨k, hik, hkj⟩ : ∃ k : Fin 3, i ≠ k ∧ k ≠ j := by
    fin_cases i <;> fin_cases j <;> decide
  rw [elementary_commutator hij hik hkj a]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RingCommutators.CM
