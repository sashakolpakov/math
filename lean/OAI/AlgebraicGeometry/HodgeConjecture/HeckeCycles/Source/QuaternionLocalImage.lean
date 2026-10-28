import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicTopology
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalSplitImage

/-! # Quaternion Local Image -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionLocalImage.CM

noncomputable section

/-! The source's actual quaternion binary subgroup fills the supported
SL2 block in its prescribed q-adic SL3 coordinates. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalSplitImage

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealCoefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem hermitian_diagonal : (QuadraticForms.CM.hermitianForm E C).val =
    CMExtraction.UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap (QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C))
      (RealCoefficients.CM.hermitianCoefficient E (B := B) 2)) := by
  rw [QuadraticForms.CM.hermitianForm_val]
  unfold CMExtraction.UnitaryMatrixEquiv.Quadratic.diagonalForm
  congr 1
  funext i
  fin_cases i
  · simp [QuadraticForms.CM.coefficient, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient]
  · simp [QuadraticForms.CM.coefficient, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient]
  · exact RealCoefficients.CM.hermitian_coefficient E C 2

variable {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

local instance : CharZero ((QadicPlace.CM.place E f).adicCompletion (QuadraticConjugation.CM.Field.RealField E)) :=
  RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero (QuadraticConjugation.CM.Field.RealField E) (.inr (QadicPlace.CM.place E f))

theorem split_matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E C).val (.inr (QadicPlace.CM.place E f)))) :
    (QadicSpecialLinear.CM.equivalence E C f g).val =
      (g.val.val.map (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus (QadicPlace.CM.root E C f) (QadicPlace.CM.root_sq E C f) (QadicPlace.CM.root_ne_zero E C f))).map
        (QadicPlace.CM.completionEquiv E f) := rfl

theorem binary_image (A : Matrix.SpecialLinearGroup (Fin 2) ℚ_[q]) :
    ∃ g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup
        (QuadraticConjugation.CM.Field.discriminant E C) (-RealCoefficients.CM.hermitianCoefficient E (B := B) 2)) (.inr (QadicPlace.CM.place E f)),
      QadicSpecialLinear.CM.equivalence E C f
        (CMExtraction.Quaternion.HermitianAdeles.quaternionLocalHermitian (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C)
          (RealCoefficients.CM.hermitianCoefficient E (B := B) 2) (QuadraticForms.CM.hermitianForm E C) (hermitian_diagonal E C) (QadicPlace.CM.place E f) g) =
          CMExtraction.Quaternion.QuadraticUnitary.activeBinaryBlock A :=
  CMExtraction.Quaternion.LocalSplitImage.quaternionLocalHermitian_split_image (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C)
    (RealCoefficients.CM.hermitianCoefficient E (B := B) 2) (QuadraticForms.CM.hermitianForm E C) (hermitian_diagonal E C)
    (QadicPlace.CM.place E f) (QadicPlace.CM.root E C f) (QadicPlace.CM.root_sq E C f) (QadicPlace.CM.root_ne_zero E C f) (QadicPlace.CM.completionEquiv E f)
    (QadicSpecialLinear.CM.equivalence E C f).toMonoidHom (split_matrix E C f)
    (RealCoefficients.CM.hermitianCoefficient_ne_zero E (B := B) 2) A

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuaternionLocalImage.CM
