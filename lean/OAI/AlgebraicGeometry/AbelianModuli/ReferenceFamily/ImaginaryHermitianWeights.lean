import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm
import Mathlib.Tactic

/-! # Imaginary Hermitian Weights -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ImaginaryHermitianWeights

noncomputable section

/-! Purely imaginary trace coefficients give nonzero real Hermitian
weights. Their signs and a positive distinguished normalization are
computed explicitly. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

theorem imaginaryHermitianWeight_re (c z : ℂ) (hc : c.re = 0) :
    (Complex.I * c * z).re = -c.im * z.re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hc,
    zero_mul, one_mul, zero_sub, add_zero, mul_zero, sub_zero]

theorem definite_of_real_weight {V : Type*} [Zero V] (B : V → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hB : (∀ x : V, x ≠ 0 → 0 < c * B x) ∨ (∀ x : V, x ≠ 0 → c * B x < 0)) :
    (∀ x : V, x ≠ 0 → 0 < B x) ∨ (∀ x : V, x ≠ 0 → B x < 0) := by
  rcases lt_or_gt_of_ne hc with hc | hc
  · rcases hB with hB | hB
    · right
      intro x hx
      exact ((mul_pos_iff.mp (hB x hx)).resolve_left (fun h => (not_lt_of_ge hc.le) h.1)).2
    · left
      intro x hx
      exact ((mul_neg_iff.mp (hB x hx)).resolve_left (fun h => (not_lt_of_ge hc.le) h.1)).2
  · rcases hB with hB | hB
    · left
      intro x hx
      exact ((mul_pos_iff.mp (hB x hx)).resolve_right (fun h => (not_lt_of_ge hc.le) h.1)).2
    · right
      intro x hx
      exact ((mul_neg_iff.mp (hB x hx)).resolve_right (fun h => (not_lt_of_ge hc.le) h.1)).2

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem imaginaryScalar_embedding_re (σ : E →ₐ[ℚ] ℂ) (ξ : E) (hξ : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ) :
    (σ ξ).re = 0 := by
  have h : star (σ ξ) = -σ ξ := (ComplexMultiplication.CM.TraceForm.cmFieldConjugation_embedding E σ ξ).symm.trans
    ((congrArg σ hξ).trans (map_neg σ ξ))
  have hr := congrArg Complex.re h
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  linarith

theorem imaginaryScalar_embedding_im_ne_zero (σ : E →ₐ[ℚ] ℂ) (ξ : E) (hne : ξ ≠ 0)
    (hξ : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ) : (σ ξ).im ≠ 0 := by
  intro hzero
  apply hne
  apply σ.injective
  apply Complex.ext
  · exact (imaginaryScalar_embedding_re σ ξ hξ).trans (congrArg Complex.re (map_zero σ)).symm
  · exact hzero.trans (congrArg Complex.im (map_zero σ)).symm

def positiveImaginaryScalar (σ : E →ₐ[ℚ] ℂ) (ξ : E) : E :=
  if 0 < (σ ξ).im then ξ else -ξ

theorem positiveImaginaryScalar_spec (σ : E →ₐ[ℚ] ℂ) (ξ : E) (hne : ξ ≠ 0)
    (hξ : ComplexMultiplication.CM.TraceForm.cmFieldConjugation E ξ = -ξ) :
    positiveImaginaryScalar σ ξ ≠ 0 ∧
      ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (positiveImaginaryScalar σ ξ) = -positiveImaginaryScalar σ ξ ∧
      0 < (σ (positiveImaginaryScalar σ ξ)).im := by
  unfold positiveImaginaryScalar
  split_ifs with h
  · exact ⟨hne, hξ, h⟩
  · refine ⟨neg_ne_zero.mpr hne, ?_, ?_⟩
    · rw [map_neg, hξ]
    · have hn := imaginaryScalar_embedding_im_ne_zero σ ξ hne hξ
      rw [map_neg, Complex.neg_im]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hn)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ImaginaryHermitianWeights
