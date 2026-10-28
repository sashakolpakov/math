import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.HermitianAdeles
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary

/-! # Quaternion Adelic Data -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionAdelicData

noncomputable section

/-! Identify the retained CM Hermitian matrix with the diagonal form
used by the actual quaternion adelic map. -/

open scoped Classical _root_.NumberField _root_.Quaternion _root_.Matrix
open _root_.NumberField QuaternionAlgebra

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary.Quadratic

theorem quaternionRationalUnitary_equiv {F : Type} [Field F] (a b : F)
    (q : (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm a (-b)).ker) :
    Quaternion.PointOne.quaternionRationalUnitary a b (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv a (-b) (RingHom.id F) q) =
      Quaternion.QuadraticUnitary.quaternionQuadraticUnitary a b q := by
  apply Subtype.ext
  apply Units.ext
  change (Quaternion.PointOne.quaternionPointUnitary a b (RingHom.id F) _).val.val = _
  rw [Quaternion.PointOne.quaternionPointUnitary_matrix, NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionMatrixPointsEquiv_matrix,
    Quaternion.PointOne.quaternionQuadraticUnitary_matrix_tuple]
  change Quaternion.PointOne.quaternionUnitaryCoordinateMatrix a b (fun i => NumberTheory.Quaternion.Arithmetic.MatrixQuaternionDet.quaternionRegularMatrix a (-b) q.val.val i 0) = _
  apply congrArg (Quaternion.PointOne.quaternionUnitaryCoordinateMatrix a b)
  funext i
  rw [NumberTheory.Quaternion.Arithmetic.MatrixQuaternionDet.quaternionRegularMatrix_apply]
  fin_cases i <;> rfl

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

include hδ0 in
theorem cmHermitianUnit_scalar_diagonal :
    (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0).val =
      UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap (maximalRealSubfield E)
        (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield E) (QuadraticCoordinates.squareParameter E δ hδ))
        (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)) := by
  rw [Multiplicity.OneUnitary.Quadratic.cmHermitianUnit_diagonal E δ hδ hδ0 b hb hb0]
  exact congrArg UnitaryMatrixEquiv.Quadratic.diagonalForm ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm.commutes
    (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionAdelicData
