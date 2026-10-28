import OAI.NumberTheory.ArithmeticGroups.Coordinates
import OAI.NumberTheory.ArithmeticGroups.Trace

/-! # Diagonal -/

namespace OAI.NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel

noncomputable section

open scoped Classical

variable {E Place : Type*} [Field E] [Algebra ℚ E]
  (σ : Place → E →ₐ[ℚ] ℂ)

lemma localB_diagonal (b : E) (τ : Place) (x y : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b]) τ x y =
      x 0 * y 0 + x 1 * y 1 + σ τ b * x 2 * y 2 := by
  simp [Geometry.ComplexBall.PrescribedSignsB.localB, Matrix.diagonal, Fin.sum_univ_succ]
  ring

lemma localB_diagonal_real (b : E) (τ : Place) (x : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    (Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b]) τ x (star x)).re =
      Complex.normSq (x 0) + Complex.normSq (x 1) +
        (σ τ b).re * Complex.normSq (x 2) := by
  rw [localB_diagonal]
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

lemma three_normSq_positive (x : Geometry.ComplexBall.PrescribedSignsB.Vec) (hx : x ≠ 0) :
    0 < Complex.normSq (x 0) + Complex.normSq (x 1) + Complex.normSq (x 2) := by
  have h0 := Complex.normSq_nonneg (x 0)
  have h1 := Complex.normSq_nonneg (x 1)
  have h2 := Complex.normSq_nonneg (x 2)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hp := Complex.normSq_pos.mpr hi
  fin_cases i
  · change 0 < Complex.normSq (x 0) at hp
    linarith
  · change 0 < Complex.normSq (x 1) at hp
    linarith
  · change 0 < Complex.normSq (x 2) at hp
    linarith

lemma diagonal_positive_plane (b : E) (μ : Place)
    (x : Geometry.ComplexBall.PrescribedSignsB.Vec) (hx : x ≠ 0) (hx2 : x 2 = 0) :
    0 < (Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b]) μ x (star x)).re := by
  rw [localB_diagonal_real, hx2]
  simpa [hx2] using three_normSq_positive x hx

lemma diagonal_positive_definite (b : E) (τ : Place) (hb : 0 < (σ τ b).re)
    (x : Geometry.ComplexBall.PrescribedSignsB.Vec) (hx : x ≠ 0) :
    0 < (Geometry.ComplexBall.PrescribedSignsB.localB σ (Matrix.diagonal ![1, 1, b]) τ x (star x)).re := by
  rw [localB_diagonal_real]
  have h0 := Complex.normSq_nonneg (x 0)
  have h1 := Complex.normSq_nonneg (x 1)
  by_cases h2 : x 2 = 0
  · simpa [h2] using three_normSq_positive x hx
  · have hp := mul_pos hb (Complex.normSq_pos.mpr h2)
    linarith

variable [NumberField E] [NumberField.IsCMField E]

omit [Algebra ℚ E] in
lemma diagonal_hermitian (b : E) (hb : NumberField.IsCMField.complexConj E b = b) :
    ∀ j k : Fin 3, (Matrix.diagonal ![1, 1, b]) j k =
      NumberField.IsCMField.complexConj E ((Matrix.diagonal ![1, 1, b]) k j) := by
  intro j k
  by_cases h : j = k
  · subst k
    fin_cases j <;> simp [Matrix.diagonal, hb]
  · simp [Matrix.diagonal, h, Ne.symm h]

omit [Algebra ℚ E] in
lemma trace_matrix_diagonal (b : E) (x y : Data.CongruenceLevel.VE E) :
    (∑ j : Fin 3, ∑ k : Fin 3, x j * (Matrix.diagonal ![1, 1, b]) j k *
      NumberField.IsCMField.complexConj E (y k)) = Data.CongruenceLevel.hermitian b x y := by
  simp [Matrix.diagonal, Data.CongruenceLevel.hermitian, Fin.sum_univ_succ, mul_comm, mul_left_comm, mul_assoc]

include σ in
lemma exists_nonzero_imaginary (μ : Place) :
    ∃ δ : E, δ ≠ 0 ∧ NumberField.IsCMField.complexConj E δ = -δ := by
  obtain ⟨x, hx⟩ := AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.exists_positive_im (σ μ)
  refine ⟨x - NumberField.IsCMField.complexConj E x, ?_, ?_⟩
  · intro h
    have hi := congrArg (fun y : E => (σ μ y).im) h
    have he : (σ μ) (NumberField.IsCMField.complexConj E x) = star ((σ μ) x) :=
      NumberField.IsCMField.complexEmbedding_complexConj E (σ μ).toRingHom x
    simp only [map_sub, map_zero, Complex.sub_im, Complex.zero_im] at hi
    rw [he] at hi
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  · rw [map_sub, NumberField.IsCMField.complexConj_apply_apply]
    abel

end

end OAI.NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel
