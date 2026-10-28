import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! # Gram Schmidt Positive Diagonal -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.GramSchmidtPositiveDiagonal.Construction

noncomputable section

/-! Gram--Schmidt has a strictly positive triangular diagonal on
a linearly independent family. -/

open InnerProductSpace
open scoped Classical

theorem gramSchmidt_inner_original
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (f : Fin n → E) (i : Fin n) :
    inner ℝ (gramSchmidt ℝ f i) (f i) = ‖gramSchmidt ℝ f i‖ ^ 2 := by
  conv_lhs => rhs; rw [gramSchmidt_def'' ℝ f i]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [inner_add_right, inner_sum]
  have hs : (∑ j ∈ Finset.Iio i,
      inner ℝ (gramSchmidt ℝ f i)
        ((inner ℝ (gramSchmidt ℝ f j) (f i) / ‖gramSchmidt ℝ f j‖ ^ 2) • gramSchmidt ℝ f j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [real_inner_smul_right, gramSchmidt_orthogonal ℝ f (ne_of_gt (Finset.mem_Iio.mp hj)), mul_zero]
  rw [hs, add_zero, real_inner_self_eq_norm_sq]

theorem gramSchmidtNormed_inner_original
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (f : Fin n → E) (hf : LinearIndependent ℝ f) (i : Fin n) :
    inner ℝ (gramSchmidtNormed ℝ f i) (f i) = ‖gramSchmidt ℝ f i‖ := by
  rw [gramSchmidtNormed, real_inner_smul_left, gramSchmidt_inner_original]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hn : ‖gramSchmidt ℝ f i‖ ≠ 0 := norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hf)
  field_simp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.GramSchmidtPositiveDiagonal.Construction
