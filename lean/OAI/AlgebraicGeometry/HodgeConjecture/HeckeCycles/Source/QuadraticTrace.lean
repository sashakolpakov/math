import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation
import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm

/-! # Quadratic Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticTrace.CM

noncomputable section

/-! The quadratic-algebra trace is the original CM field trace. The
linear-first and conjugate-first Hermitian conventions are compared
explicitly, including the sign of the imaginary coefficient. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem quadratic_trace (x : QuadraticAlgebra (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) 0) :
    Algebra.trace (QuadraticConjugation.CM.Field.RealField E) E (QuadraticConjugation.CM.Field.fieldEquiv E C x) = QuadraticAlgebra.trace x := by
  have hn : ∃ z : E, NumberField.IsCMField.complexConj E z ≠ z := by
    refine ⟨C.delta, ?_⟩
    intro h
    exact QuadraticConjugation.CM.Field.delta_not_real E C ((NumberField.IsCMField.complexConj_eq_self_iff E _).mp h)
  have h := RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm.Construction.quadratic_trace_formula
    (Algebra.IsQuadraticExtension.finrank_eq_two (QuadraticConjugation.CM.Field.RealField E) E)
    (NumberField.IsCMField.complexConj E) hn (QuadraticConjugation.CM.Field.fieldEquiv E C x)
  apply (algebraMap (QuadraticConjugation.CM.Field.RealField E) E).injective
  rw [h, ← (QuadraticConjugation.CM.Field.fieldEquiv E C).commutes (QuadraticAlgebra.trace x),
    QuadraticAlgebra.algebraMap_trace_eq_add_star, map_add, QuadraticConjugation.CM.fieldEquiv_star]
  rfl

theorem rational_trace (x : QuadraticAlgebra (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) 0) :
    Algebra.trace ℚ (QuadraticConjugation.CM.Field.RealField E) (QuadraticAlgebra.trace x) =
      Algebra.trace ℚ E (QuadraticConjugation.CM.Field.fieldEquiv E C x) := by
  rw [← quadratic_trace E C x, Algebra.trace_trace]

theorem conjugate_hermitian (x y : GeometricSource.CM.Vec E) :
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (GeometricSource.CM.hermitian E B.b x y) = GeometricSource.CM.hermitian E B.b y x := by
  simp only [GeometricSource.CM.hermitian, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = 2 <;>
    simp only [hj, ite_true, ite_false, B.conjugate_b, map_one, ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply]
    <;> ring

theorem trace_conjugation (x : E) :
    Algebra.trace ℚ E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) = Algebra.trace ℚ E x :=
  Algebra.trace_eq_of_algEquiv (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) x

theorem source_trace_as_conjugate_first (x y : GeometricSource.CM.Vec E) :
    Algebra.trace ℚ E (C.delta * C.a * GeometricSource.CM.hermitian E B.b x y) =
      Algebra.trace ℚ E (-C.delta * C.a * GeometricSource.CM.hermitian E B.b y x) := by
  rw [← trace_conjugation E (C.delta * C.a * GeometricSource.CM.hermitian E B.b x y)]
  congr 1
  rw [map_mul, map_mul, C.delta_imaginary, C.a_real, conjugate_hermitian]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticTrace.CM
