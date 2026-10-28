import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianNormForms
import Mathlib.Topology.Instances.Matrix

/-! # Matrix Unit Topology -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.MatrixUnitTopology.Construction

noncomputable section

/-! Invertible matrices act by continuous additive coordinate changes. -/

open _root_.Matrix

def matrixUnitContinuousAddEquiv
    {E I : Type} [NormedField E] [Fintype I] [DecidableEq I]
    (u : (Matrix I I E)ˣ) : (I → E) ≃ₜ+ (I → E) where
  toFun x := (u : Matrix I I E) *ᵥ x
  invFun x := ((u⁻¹ : (Matrix I I E)ˣ) : Matrix I I E) *ᵥ x
  left_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  right_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add _ x y
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem matrixUnitContinuousAddEquiv_apply
    {E I : Type} [NormedField E] [Fintype I] [DecidableEq I]
    (u : (Matrix I I E)ˣ) (x : I → E) :
    matrixUnitContinuousAddEquiv u x = (u : Matrix I I E) *ᵥ x := rfl

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.MatrixUnitTopology.Construction
