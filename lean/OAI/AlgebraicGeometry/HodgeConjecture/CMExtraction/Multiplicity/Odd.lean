import OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType

/-! # Odd -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd

noncomputable section

/-!
# The multiplicity line with the prescribed inverse-embedding signs

Weak approximation constructs the imaginary coefficient ξ with signs
v(τ⁻¹). Relative to a common imaginary reference coefficient δ, the
multiplicity line is the genuine rank-one E-Hermitian space with coefficient
a = ξ / δ. Its oriented skew-Hermitian coefficient is δa = ξ. The sign
identity is proved from the signs of this constructed coefficient.
-/

open scoped Classical
open OAI.AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

abbrev Sign := ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)

/-- Inversion of embedding labels is part of the source construction. -/
def inverseType (v : Sign E) : Sign E :=
  ⟨fun τ => v.val τ⁻¹, fun τ => by
    change v.val ((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ)⁻¹) = !v.val τ⁻¹
    have hc : (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)⁻¹ = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E := by
      apply inv_eq_of_mul_eq_one_left
      apply AlgEquiv.ext
      exact ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply E
    rw [mul_inv_rev, hc, ← (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E τ⁻¹).eq]
    exact v.property τ⁻¹⟩

/-- The actual imaginary coefficient constructed by weak approximation. -/
def imaginaryCoefficient (v : Sign E) : E :=
  (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E (inverseType E v)).imaginaryElement

theorem imaginaryCoefficient_conjugate (v : Sign E) :
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (imaginaryCoefficient E v) = -imaginaryCoefficient E v :=
  (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E (inverseType E v)).imaginaryElement_conjugate

theorem imaginaryCoefficient_ne_zero (v : Sign E) : imaginaryCoefficient E v ≠ 0 :=
  (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E (inverseType E v)).imaginaryElement_ne_zero

theorem imaginaryCoefficient_positive (v : Sign E) (τ : Gal(E/ℚ))
    (h : v.val τ⁻¹ = true) :
    0 < ((τ (imaginaryCoefficient E v) : E) : ℂ).im := by
  apply (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E (inverseType E v)).imaginaryElement_positive
    (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)
  rw [ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType_apply]
  exact h

theorem imaginaryCoefficient_negative (v : Sign E) (τ : Gal(E/ℚ))
    (h : v.val τ⁻¹ = false) :
    ((τ (imaginaryCoefficient E v) : E) : ℂ).im < 0 := by
  apply (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType E (inverseType E v)).imaginaryElement_negative
    (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)
  rw [ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.embeddingType_apply]
  exact h

/-- A fixed reference type supplies δ; all multiplicity lines can share it. -/
def hermitianCoefficient (reference v : Sign E) : E :=
  imaginaryCoefficient E v / imaginaryCoefficient E reference

theorem hermitianCoefficient_real (reference v : Sign E) :
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (hermitianCoefficient E reference v) =
      hermitianCoefficient E reference v := by
  simp only [hermitianCoefficient, map_div₀, imaginaryCoefficient_conjugate,
    neg_div, div_neg, neg_neg]

theorem hermitianCoefficient_ne_zero (reference v : Sign E) :
    hermitianCoefficient E reference v ≠ 0 :=
  div_ne_zero (imaginaryCoefficient_ne_zero E v) (imaginaryCoefficient_ne_zero E reference)

/-- The actual Hermitian pairing on the rank-one E-module E. -/
def multiplicityPairing (reference v : Sign E) (x y : E) : E :=
  hermitianCoefficient E reference v * x * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E y

theorem multiplicityPairing_hermitian (reference v : Sign E) (x y : E) :
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (multiplicityPairing E reference v x y) =
      multiplicityPairing E reference v y x := by
  simp only [multiplicityPairing, map_mul, hermitianCoefficient_real,
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply]
  ring

theorem multiplicityPairing_nondegenerate (reference v : Sign E) (x : E)
    (hx : ∀ y, multiplicityPairing E reference v x y = 0) : x = 0 := by
  have h := hx 1
  simp only [multiplicityPairing, map_one, mul_one] at h
  exact (mul_eq_zero.mp h).resolve_left (hermitianCoefficient_ne_zero E reference v)

omit [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E] in
theorem multiplicity_rank_one : Module.finrank E E = 1 := Module.finrank_self E

/-- Signs are measured on the oriented skew-Hermitian trace coefficient. -/
def multiplicitySign (reference v : Sign E) (τ : Gal(E/ℚ)) : ℤ :=
  if 0 < ((τ (imaginaryCoefficient E reference *
      multiplicityPairing E reference v 1 1) : E) : ℂ).im then 1 else -1

theorem orientedCoefficient (reference v : Sign E) :
    imaginaryCoefficient E reference * multiplicityPairing E reference v 1 1 =
      imaginaryCoefficient E v := by
  simp only [multiplicityPairing, map_one, mul_one, hermitianCoefficient]
  exact mul_div_cancel₀ _ (imaginaryCoefficient_ne_zero E reference)

/-- The manuscript's d(τ) = v(τ⁻¹) is derived from the constructed line. -/
theorem multiplicitySign_eq (reference v : Sign E) (τ : Gal(E/ℚ)) :
    multiplicitySign E reference v τ = ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹) := by
  unfold multiplicitySign
  rw [orientedCoefficient]
  cases h : v.val τ⁻¹
  · rw [ite_eq_right (not_lt_of_ge (imaginaryCoefficient_negative E v τ h).le)]
    rfl
  · rw [ite_eq_left (imaginaryCoefficient_positive E v τ h)]
    rfl

theorem multiplicitySign_odd (reference v : Sign E) (τ : Gal(E/ℚ)) :
    multiplicitySign E reference v (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) =
      -multiplicitySign E reference v τ := by
  simp only [multiplicitySign_eq]
  exact congrArg ComplexMultiplication.SignSwitch.CM.signValue ((inverseType E v).property τ) |>.trans (ComplexMultiplication.SignSwitch.CM.signValue_not _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd
