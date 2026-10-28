import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionApproximation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionLocalImage
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.Projection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuaternionSourceClosure

/-! # Quaternion Closure -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionClosure.CM.Intrinsic

/-! Specialize quaternion approximation to the actual source Hermitian
group before transporting its rational coordinates. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealCoefficients.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem binary_mem_closure (A : Matrix.SpecialLinearGroup (Fin 2) ℚ_[q]) :
    (CMExtraction.Quaternion.QuadraticUnitary.activeBinaryBlock A, 1) ∈ closure (Set.range
      ((CMExtraction.ActiveAwayProjection.Approximation.activeAwayProjection (QuadraticConjugation.CM.Field.RealField E)
        (d := QuadraticConjugation.CM.Field.discriminant E C) (QuadraticForms.CM.hermitianForm E C) (QadicPlace.CM.place E f)
        (SourceAdelic.Projection.CM.localProjection E C f)).toMonoidHom.comp
        ((RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C)).comp
          (UnitaryMatrix.CM.hom E C)))) :=
  QuaternionSourceClosure.CM.supported (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C)
    (RealCoefficients.CM.hermitianCoefficient E (B := B) 2) (QuadraticForms.CM.hermitianForm E C)
    (QuaternionLocalImage.CM.hermitian_diagonal E C) (QadicPlace.CM.place E f)
    (G := Matrix.SpecialLinearGroup (Fin 3) ℚ_[q]) (Γ := Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (SourceAdelic.Projection.CM.localProjection E C f) (UnitaryMatrix.CM.hom E C)
    (UnitaryEquiv.CM.equivalence E C).surjective
    (QuaternionApproximation.CM.strong_approximation E C)
    (CMExtraction.Quaternion.QuadraticUnitary.activeBinaryBlock A) (QuaternionLocalImage.CM.binary_image E C f A)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionClosure.CM.Intrinsic

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionClosure.CM

/-! Supported binary matrices lie in the closure of the actual rational
source group, with identity at every other finite place. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealCoefficients.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem binary_mem_closure (A : Matrix.SpecialLinearGroup (Fin 2) ℚ_[q]) :
    (CMExtraction.Quaternion.QuadraticUnitary.activeBinaryBlock A, (1 : SourceAdelic.Projection.CM.Away E C f)) ∈
      closure (Set.range (SourceAdelic.Projection.CM.rational E C f)) := by
  exact Intrinsic.binary_mem_closure E C f A

/-- The supported closure statement in the restricted-away coordinate presentation. -/
theorem binary_mem_closure_restricted (A : Matrix.SpecialLinearGroup (Fin 2) ℚ_[q]) :
    (CMExtraction.Quaternion.QuadraticUnitary.activeBinaryBlock A, (1 : CMExtraction.RestrictedAwaySame.Approximation.RestrictedAway
      (SourceFinite.Product.CM.levels E C) (QadicPlace.CM.place E f))) ∈
      closure (Set.range (SourceAdelic.Projection.CM.rational E C f)) :=
  binary_mem_closure E C f A

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionClosure.CM

end

end OAI
