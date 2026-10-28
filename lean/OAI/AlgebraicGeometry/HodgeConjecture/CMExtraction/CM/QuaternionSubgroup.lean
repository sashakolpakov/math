import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.QuadraticUnitary
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.UnitaryPresentation

/-! # Quaternion Subgroup -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionSubgroup

noncomputable section

/-! The explicit quaternion subgroup for the actual CM Hermitian
coefficient and the specified imaginary generator. -/

open scoped Classical _root_.Quaternion _root_.Matrix
open _root_.NumberField QuaternionAlgebra _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.UnitaryPresentation.Quadratic

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

local instance cmQuaternionStarRing : StarRing E where
  star := IsCMField.complexConj E
  star_involutive := IsCMField.complexConj_apply_apply E
  star_mul x y := (map_mul (IsCMField.complexConj E) x y).trans (mul_comm _ _)
  star_add := map_add (IsCMField.complexConj E)

def cmQuaternionSubgroup (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) :
    (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm (QuadraticCoordinates.squareParameter E δ hδ) (-Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)).ker →*
      Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b :=
  Quaternion.QuadraticUnitary.quaternionRankThreeUnitary (QuadraticCoordinates.squareParameter E δ hδ) (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)
    δ rfl (IsCMField.complexConj_apply_eq_self E) hδ

theorem cmQuaternionSubgroup_matrix (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (q : (NumberTheory.Quaternion.Arithmetic.Norm.quaternionUnitNorm (QuadraticCoordinates.squareParameter E δ hδ) (-Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)).ker) :
    (cmQuaternionSubgroup E b hb δ hδ q).val.val =
      !![(q.val.val.re : E) + δ * (q.val.val.imI : E), 0,
          -b * ((q.val.val.imJ : E) + δ * (q.val.val.imK : E));
         0, 1, 0;
         (q.val.val.imJ : E) - δ * (q.val.val.imK : E), 0,
          (q.val.val.re : E) - δ * (q.val.val.imI : E)] := by
  change (Quaternion.QuadraticUnitary.activeBinaryBlock (Quaternion.SpecialLinear.unitaryQuaternionNormOneHom _ _ δ rfl q)).val = _
  rw [Quaternion.QuadraticUnitary.activeBinaryBlock_matrix]
  have h := Quaternion.UnitaryMatrix.unitaryQuaternionMap_apply (QuadraticCoordinates.squareParameter E δ hδ)
    (Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb) δ rfl q.val.val
  change (Quaternion.SpecialLinear.unitaryQuaternionNormOneHom _ _ δ rfl q).val = _ at h
  simp only [h]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionSubgroup
