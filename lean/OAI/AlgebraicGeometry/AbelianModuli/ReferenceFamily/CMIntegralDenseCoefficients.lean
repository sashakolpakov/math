import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLocalizedVectors
import Mathlib.NumberTheory.NumberField.CMField

/-! # CM Integral Dense Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMIntegralDenseCoefficients

noncomputable section

/-! The required nonreal coefficient can be chosen in the actual ring
of integers of a CM field. Thus the dense affine vector sets use integral
coefficients and powers of the single chosen denominator. -/

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem exists_integral_nonreal_coefficient (μ : E →+* ℂ) :
    ∃ z : NumberField.RingOfIntegers E, (μ (z : E)).im ≠ 0 := by
  classical
  by_contra h
  have hc (a : NumberField.RingOfIntegers E) :
      star (μ (a : E)) = μ (a : E) :=
    Complex.conj_eq_iff_im.mpr (not_not.mp (not_exists.mp h a))
  apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal μ
  apply NumberField.ComplexEmbedding.isReal_iff.mpr
  apply RingHom.ext
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (NumberField.RingOfIntegers E) x
  change star (μ ((a : E) / (b : E))) = μ ((a : E) / (b : E))
  rw [map_div₀, star_div₀, hc, hc]

theorem exists_integral_dense_affine_coefficients {I : Type*}
    (μ : E →+* ℂ) (b : ℕ) (hb : 2 ≤ b) (v₀ : I → E) (m : E) (hm : m ≠ 0) :
    ∃ z : NumberField.RingOfIntegers E,
      (μ (z : E)).im ≠ 0 ∧ Dense (EmbeddedLocalizedVectors.embeddedLocalizedVectors μ b (z : E) v₀ m) := by
  obtain ⟨z, hz⟩ := exists_integral_nonreal_coefficient μ
  exact ⟨z, hz, EmbeddedLocalizedVectors.embeddedLocalizedVectors_dense μ b hb (z : E) hz v₀ m hm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMIntegralDenseCoefficients
