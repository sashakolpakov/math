import OAI.RepresentationTheory.Weil.Local.QuadraticDiagonalData
import OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner

/-! # General Quadratic Algebra -/

namespace OAI.RepresentationTheory.Weil.Local.GeneralQuadraticAlgebra.Construction

noncomputable section

/-! Completing the square for a nonsingular symmetric matrix. -/

open _root_.Matrix

theorem general_quadratic_complete_square
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm) (x y : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic M.val (y + M⁻¹.val *ᵥ x) - FunctionsMetaplectic.Construction.dot x (y + M⁻¹.val *ᵥ x) =
      FunctionsMetaplectic.Construction.quadratic M.val y - FunctionsMetaplectic.Construction.quadratic M⁻¹.val x := by
  have hcancel : M.val *ᵥ (M⁻¹.val *ᵥ x) = x := by
    rw [mulVec_mulVec]
    have h : M.val * M⁻¹.val = 1 := congrArg Units.val (mul_inv_cancel M)
    rw [h, one_mulVec]
  have hcross : FunctionsMetaplectic.Construction.dot (M⁻¹.val *ᵥ x) (M.val *ᵥ y) = FunctionsMetaplectic.Construction.dot y x := by
    have h := Matrix.dotProduct_transpose_mulVec M.val (M⁻¹.val *ᵥ x) y
    change (M⁻¹.val *ᵥ x) ⬝ᵥ M.val *ᵥ y = y ⬝ᵥ x
    simpa only [hM.eq, hcancel] using h
  rw [QuadraticIntertwiner.Construction.quadratic_eq_dot, QuadraticIntertwiner.Construction.quadratic_eq_dot, QuadraticIntertwiner.Construction.quadratic_eq_dot]
  change ((y + M⁻¹.val *ᵥ x) ⬝ᵥ M.val *ᵥ (y + M⁻¹.val *ᵥ x)) / 2 -
    x ⬝ᵥ (y + M⁻¹.val *ᵥ x) = (y ⬝ᵥ M.val *ᵥ y) / 2 -
      (x ⬝ᵥ M⁻¹.val *ᵥ x) / 2
  simp only [mulVec_add, hcancel, add_dotProduct, dotProduct_add]
  change (FunctionsMetaplectic.Construction.dot y (M.val *ᵥ y) + FunctionsMetaplectic.Construction.dot (M⁻¹.val *ᵥ x) (M.val *ᵥ y) +
    (FunctionsMetaplectic.Construction.dot y x + FunctionsMetaplectic.Construction.dot (M⁻¹.val *ᵥ x) x)) / 2 -
      (FunctionsMetaplectic.Construction.dot x y + FunctionsMetaplectic.Construction.dot x (M⁻¹.val *ᵥ x)) = _
  rw [hcross, FourierTools.Construction.dot_comm y x, FourierTools.Construction.dot_comm (M⁻¹.val *ᵥ x) x]
  unfold FunctionsMetaplectic.Construction.dot dotProduct
  ring

end

end OAI.RepresentationTheory.Weil.Local.GeneralQuadraticAlgebra.Construction
