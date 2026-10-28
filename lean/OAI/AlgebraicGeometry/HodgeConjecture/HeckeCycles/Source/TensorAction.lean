import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TensorPairing
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryMatrix

/-! # Tensor Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TensorAction.CM

noncomputable section

/-! The AdelicSplitting tensor action is the original source action under a proved
linear identification of their actual vector spaces. -/

open scoped Classical _root_.Matrix Kronecker
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TensorPairing.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def tensorEquiv : GeometricSource.CM.Vec E ≃ₗ[QuadraticConjugation.CM.Field.RealField E] RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (QuadraticConjugation.CM.Field.discriminant E C) 3 1 where
  toFun := TensorPairing.CM.tensorVector E C
  invFun x i := QuadraticConjugation.CM.Field.fieldEquiv E C (x (i, 0))
  left_inv x := by
    funext i
    exact (QuadraticConjugation.CM.Field.fieldEquiv E C).apply_symm_apply _
  right_inv x := by
    funext ij
    change (QuadraticConjugation.CM.Field.fieldEquiv E C).symm (QuadraticConjugation.CM.Field.fieldEquiv E C (x (ij.1, 0))) = x ij
    rw [AlgEquiv.symm_apply_apply]
    exact congrArg x (Prod.ext rfl (Subsingleton.elim _ _))
  map_add' x y := by
    funext ij
    exact (QuadraticConjugation.CM.Field.fieldEquiv E C).symm.map_add _ _
  map_smul' a x := by
    funext ij
    exact (QuadraticConjugation.CM.Field.fieldEquiv E C).symm.toLinearMap.map_smul' a (x ij.1)

def pair (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (QuadraticForms.CM.hermitianForm E C).val × RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Unitary (QuadraticForms.CM.skewForm E C).val :=
  (RepresentationTheory.Theta.Adelic.SpecialUnitary.includeUnitary _ (UnitaryMatrix.CM.hom E C g), 1)

theorem tensor_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (x : GeometricSource.CM.Vec E) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tensorLinear (QuadraticForms.CM.hermitianForm E C).val (QuadraticForms.CM.skewForm E C).val (pair E C g) (TensorPairing.CM.tensorVector E C x) =
      TensorPairing.CM.tensorVector E C (ComplexAction.CM.Symplectic.rationalAction E g x) := by
  funext ij
  change (((UnitaryMatrix.CM.matrix E C g).val ⊗ₖ (1 : Matrix (Fin 1) (Fin 1) (QuadraticForms.CM.Coefficients E C))) *ᵥ
    TensorPairing.CM.tensorVector E C x) ij = _
  have h := congrFun (UnitaryMatrix.CM.vector_action E C g x) ij.1
  have hi : ij.2 = 0 := Subsingleton.elim _ _
  simpa [hi, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, TensorPairing.CM.tensorVector, UnitaryMatrix.CM.vector] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.TensorAction.CM
