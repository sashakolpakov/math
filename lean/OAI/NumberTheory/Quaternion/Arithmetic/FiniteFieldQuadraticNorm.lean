import Mathlib

/-! # Finite Field Quadratic Norm -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteFieldQuadraticNorm

noncomputable section

/-! A binary norm equation over a finite field of odd characteristic
always has a solution. This provides the residue-field starting point
for unramified local quaternion splitting. -/

open scoped Classical
open _root_.Polynomial

variable {k : Type*} [Field k] [Fintype k]

theorem finiteField_binary_norm_surjective (hchar : ringChar k ≠ 2) (a : k) (ha : a ≠ 0) (b : k) :
    ∃ x y : k, x ^ 2 - a * y ^ 2 = b := by
  let f : Polynomial k := X ^ 2
  let g : Polynomial k := C (-a) * X ^ 2 - C b
  have hf : f.degree = 2 := degree_X_pow 2
  have hquad : (C (-a) * X ^ 2 : Polynomial k).degree = 2 :=
    degree_C_mul_X_pow 2 (neg_ne_zero.mpr ha)
  have hg : g.degree = 2 := by
    change (C (-a) * X ^ 2 - C b).degree = 2
    rw [degree_sub_eq_left_of_degree_lt, hquad]
    rw [hquad]
    exact lt_of_le_of_lt degree_C_le (by decide)
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (FiniteField.odd_card_of_char_ne_two hchar)
  refine ⟨x, y, ?_⟩
  simp only [f, g, eval_pow, eval_X, eval_sub, eval_mul, eval_C, neg_mul] at hxy
  linear_combination hxy

theorem finiteField_binary_norm_solution_nonzero (hchar : ringChar k ≠ 2)
    (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x y : k, x ^ 2 - a * y ^ 2 = b ∧ (x ≠ 0 ∨ y ≠ 0) := by
  obtain ⟨x, y, hxy⟩ := finiteField_binary_norm_surjective hchar a ha b
  refine ⟨x, y, hxy, ?_⟩
  by_contra h
  push Not at h
  apply hb
  simpa only [h.1, h.2, zero_pow (by omega : 2 ≠ 0), mul_zero, sub_zero] using hxy.symm

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteFieldQuadraticNorm
