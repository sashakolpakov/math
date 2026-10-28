import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorStar
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.UnitaryDet
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryLinear

/-! # PEL Scalar -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELScalar.CM

noncomputable section

/-! The source quadratic coordinates identify the completed coefficient
algebra and its Hermitian matrix with the literal PEL coefficients. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuadraticTensorStar.TestTransport

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)

def equivalence :
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (QuadraticConjugation.CM.Field.RealField E))
      (algebraMap (QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (QuadraticConjugation.CM.Field.RealField E)) (QuadraticConjugation.CM.Field.discriminant E Q)) ≃+*
        AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E :=
  CMExtraction.QuadraticTensorEquiv.TestTransport.quadraticAdelicTensorRingEquiv (QuadraticConjugation.CM.Field.discriminant E Q) (QuadraticConjugation.CM.Field.fieldEquiv E Q)

theorem conjugation (x) : equivalence E Q (star x) = star (equivalence E Q x) :=
  CMExtraction.QuadraticTensorStar.TestTransport.quadraticAdelicTensorMap_star (QuadraticConjugation.CM.Field.discriminant E Q) (QuadraticConjugation.CM.Field.fieldEquiv E Q)
    (QuadraticConjugation.CM.fieldEquiv_star E Q) x

theorem continuous : Continuous (equivalence E Q) :=
  CMExtraction.QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_continuous (QuadraticConjugation.CM.Field.discriminant E Q) (QuadraticConjugation.CM.Field.fieldEquiv E Q)

theorem inverse_continuous : Continuous (equivalence E Q).symm :=
  CMExtraction.QuadraticTensorEquiv.TestTransport.quadraticTensorInverse_continuous (QuadraticConjugation.CM.Field.discriminant E Q) (QuadraticConjugation.CM.Field.fieldEquiv E Q)

theorem rational (z : QuadraticForms.CM.Coefficients E Q) :
    equivalence E Q (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange
      (algebraMap (QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (QuadraticConjugation.CM.Field.RealField E))) (QuadraticConjugation.CM.Field.discriminant E Q) z) =
        AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (QuadraticConjugation.CM.Field.fieldEquiv E Q z) :=
  CMExtraction.QuadraticTensorMap.TestTransport.quadraticAdelicTensorMap_rational (QuadraticConjugation.CM.Field.discriminant E Q) (QuadraticConjugation.CM.Field.fieldEquiv E Q) z

theorem hermitian :
    (CMExtraction.Finite.UnitaryDet.Approximation.finiteHermitianMatrix (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q)).map (equivalence E Q) =
      CMExtraction.UnitaryMatrixEquiv.Quadratic.diagonalForm (AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E B.b) := by
  apply Matrix.ext
  intro i j
  change equivalence E Q (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.quadraticBaseChange
    (algebraMap (QuadraticConjugation.CM.Field.RealField E) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (QuadraticConjugation.CM.Field.RealField E))) (QuadraticConjugation.CM.Field.discriminant E Q)
      ((QuadraticForms.CM.hermitianForm E Q).val i j)) = _
  rw [rational, QuadraticForms.CM.hermitianForm_val]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, AlgEquiv.apply_symm_apply]
    by_cases hi : i = 2
    · simp only [QuadraticForms.CM.coefficient, hi, ite_true, CMExtraction.UnitaryMatrixEquiv.Quadratic.diagonalForm,
        Matrix.diagonal_apply_eq, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient]
    · simp only [QuadraticForms.CM.coefficient, hi, ite_false, map_one, CMExtraction.UnitaryMatrixEquiv.Quadratic.diagonalForm,
        Matrix.diagonal_apply_eq, Geometry.ComplexBall.ArithmeticQuotientEquationsData.diagonalCoefficient]
  · simp only [Matrix.diagonal_apply_ne _ hij, map_zero,
      CMExtraction.UnitaryMatrixEquiv.Quadratic.diagonalForm]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PELScalar.CM
