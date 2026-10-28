import Mathlib.NumberTheory.NumberField.Basic

/-! # Coefficient Clearing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.CoefficientClearing

noncomputable section

/-! One positive rational integer clears an arbitrary finite family of
number-field coefficients. In particular, the original form matrix and
fixed reflection vector can be made integral without changing fields.
-/

variable (E : Type*) [Field E] [NumberField E]

theorem finite_coefficients_positive_integer_multiple
    {I : Type*} [Fintype I] (x : I → E) :
    ∃ d : ℤ, 0 < d ∧ ∃ y : I → NumberField.RingOfIntegers E,
      ∀ i, (y i : E) = (d : E) * x i := by
  classical
  obtain ⟨a, ha, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image x)
  have hi (i : I) : IsIntegral ℤ (a • (a • x i)) :=
    (hint (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).smul a
  refine ⟨a ^ 2, sq_pos_of_ne_zero ha,
    fun i => ⟨a • (a • x i), hi i⟩, ?_⟩
  intro i
  change a • (a • x i) = ((a ^ 2 : ℤ) : E) * x i
  rw [← mul_smul]
  simp only [Algebra.smul_def, eq_intCast, pow_two]

theorem matrix_and_vector_positive_integer_multiple
    {I : Type*} [Fintype I] (H : Matrix I I E) (w : I → E) :
    ∃ d : ℤ, 0 < d ∧
      ∃ H₀ : Matrix I I (NumberField.RingOfIntegers E),
      ∃ w₀ : I → NumberField.RingOfIntegers E,
        (∀ i j, (H₀ i j : E) = (d : E) * H i j) ∧
        (∀ i, (w₀ i : E) = (d : E) * w i) := by
  let x : (I × I) ⊕ I → E := Sum.elim (fun ij => H ij.1 ij.2) w
  obtain ⟨d, hd, y, hy⟩ := finite_coefficients_positive_integer_multiple E x
  exact ⟨d, hd, fun i j => y (Sum.inl (i, j)), fun i => y (Sum.inr i),
    fun i j => hy (Sum.inl (i, j)), fun i => hy (Sum.inr i)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.CoefficientClearing
