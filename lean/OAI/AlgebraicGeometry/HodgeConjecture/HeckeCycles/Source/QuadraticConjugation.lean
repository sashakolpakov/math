import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource

/-! # Quadratic Conjugation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

/-! Present the original CM coefficient field as a quadratic algebra
over its maximal real subfield, using the source's actual imaginary
symplectic coefficient. This supplies AdelicTheta's concrete field coordinates. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

abbrev RealField := NumberField.maximalRealSubfield E

def discriminant : RealField E :=
  ⟨C.delta ^ 2, (NumberField.IsCMField.complexConj_eq_self_iff _ _).mp (by
    change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (C.delta ^ 2) = C.delta ^ 2
    rw [map_pow, C.delta_imaginary, neg_sq])⟩

theorem delta_not_real : C.delta ∉ RealField E := by
  intro h
  have he := (NumberField.IsCMField.complexConj_eq_self_iff E C.delta).mpr h
  change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E C.delta = C.delta at he
  rw [C.delta_imaginary] at he
  exact C.delta_ne_zero (CharZero.neg_eq_self_iff.mp he)

theorem discriminant_ne_zero : discriminant E C ≠ 0 := by
  intro h
  have he := congrArg (fun x : RealField E => (x : E)) h
  exact (pow_ne_zero 2 C.delta_ne_zero) he

theorem discriminant_not_square : ¬ IsSquare (discriminant E C) := by
  rintro ⟨r, hr⟩
  have he : C.delta ^ 2 = (r : E) ^ 2 := by
    simpa only [discriminant, pow_two, Subfield.coe_mul] using congrArg (fun x : RealField E => (x : E)) hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · exact delta_not_real E C (h ▸ r.property)
  · exact delta_not_real E C (h ▸ (RealField E).neg_mem r.property)

def realPart (x : E) : RealField E :=
  ⟨(x + ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) / 2, (NumberField.IsCMField.complexConj_eq_self_iff E _).mp (by
    change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E ((x + ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) / 2) = _
    rw [map_div₀, map_add, map_ofNat, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply]
    rw [add_comm])⟩

def imaginaryPart (x : E) : RealField E :=
  ⟨(x - ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) / (2 * C.delta),
    (NumberField.IsCMField.complexConj_eq_self_iff E _).mp (by
      change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E ((x - ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) / (2 * C.delta)) = _
      rw [map_div₀, map_sub, map_mul, map_ofNat,
        ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply, C.delta_imaginary]
      field_simp
      ring)⟩

def toOriginal : QuadraticAlgebra (RealField E) (discriminant E C) 0 →ₐ[RealField E] E :=
  QuadraticAlgebra.lift ⟨C.delta, by
    change C.delta * C.delta = C.delta ^ 2 * 1 + (0 : E) * C.delta
    ring⟩

theorem toOriginal_apply (x : QuadraticAlgebra (RealField E) (discriminant E C) 0) :
    toOriginal E C x = (x.re : E) + (x.im : E) * C.delta := by
  change (x.re : E) * 1 + (x.im : E) * C.delta = _
  rw [mul_one]

theorem toOriginal_surjective : Function.Surjective (toOriginal E C) := by
  intro x
  refine ⟨⟨realPart E x, imaginaryPart E C x⟩, ?_⟩
  rw [toOriginal_apply]
  change (x + ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) / 2 + (x - ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) / (2 * C.delta) * C.delta = x
  field_simp [C.delta_ne_zero]
  ring

def fieldEquiv : QuadraticAlgebra (RealField E) (discriminant E C) 0 ≃ₐ[RealField E] E :=
  AlgEquiv.ofBijective (toOriginal E C) ⟨
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (toOriginal E C).toLinearMap)
      (show Module.finrank (RealField E) (QuadraticAlgebra (RealField E) (discriminant E C) 0) =
          Module.finrank (RealField E) E by
        rw [QuadraticAlgebra.finrank_eq_two, Algebra.IsQuadraticExtension.finrank_eq_two])).mpr
          (toOriginal_surjective E C),
    toOriginal_surjective E C⟩

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM

/-! The quadratic presentation preserves the original CM involution.
Consequently the original real Hermitian coefficients and imaginary
symplectic coefficient retain their actual signs under this presentation. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem real_fixed (r : Field.RealField E) : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = (r : E) :=
  NumberField.IsCMField.complexConj_apply_eq_self E r

theorem fieldEquiv_star (x : QuadraticAlgebra (Field.RealField E) (Field.discriminant E C) 0) :
    Field.fieldEquiv E C (star x) = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (Field.fieldEquiv E C x) := by
  change Field.toOriginal E C (star x) = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (Field.toOriginal E C x)
  rw [Field.toOriginal_apply, Field.toOriginal_apply, map_add, map_mul, real_fixed, real_fixed,
    C.delta_imaginary]
  simp only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, zero_mul, add_zero,
    Subfield.coe_neg, neg_mul, mul_neg]

theorem fieldEquiv_symm_conjugation (x : E) :
    (Field.fieldEquiv E C).symm (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) = star ((Field.fieldEquiv E C).symm x) := by
  apply (Field.fieldEquiv E C).injective
  rw [AlgEquiv.apply_symm_apply, fieldEquiv_star, AlgEquiv.apply_symm_apply]

theorem hermitian_coefficient_real : star ((Field.fieldEquiv E C).symm B.b) = (Field.fieldEquiv E C).symm B.b := by
  rw [← fieldEquiv_symm_conjugation, B.conjugate_b]

theorem multiplicity_coefficient_real : star ((Field.fieldEquiv E C).symm C.a) = (Field.fieldEquiv E C).symm C.a := by
  rw [← fieldEquiv_symm_conjugation, C.a_real]

theorem symplectic_coefficient_imaginary :
    star ((Field.fieldEquiv E C).symm C.delta) = -((Field.fieldEquiv E C).symm C.delta) := by
  rw [← fieldEquiv_symm_conjugation, C.delta_imaginary, map_neg]

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM

end

end OAI
