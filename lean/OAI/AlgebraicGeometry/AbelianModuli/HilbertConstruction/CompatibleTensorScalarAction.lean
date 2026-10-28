import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleScalarTensorMap

/-! # Compatible Tensor Scalar Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleTensorScalarAction

noncomputable section

/-! The actual compatible tensor map respects the full left coefficient action, not only the original coefficient ring. -/
open scoped TensorProduct
universe u

variable {R B V G : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable [AddCommGroup V] [Module R V] [AddCommGroup G] [Module R G]
variable (ρ : B →+* Module.End R G)
variable (hρ : ∀ (r : R) (x : G), ρ (algebraMap R B r) x = r • x)

theorem compatibleScalarTensorMap_left_action (a : V →ₗ[R] G)
    (b : B) (z : TensorProduct R B V) :
    CompatibleScalarTensorMap.compatibleScalarTensorMap ρ hρ a (b • z) = ρ b (CompatibleScalarTensorMap.compatibleScalarTensorMap ρ hρ a z) := by
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, CompatibleScalarTensorMap.compatibleScalarTensorMap_tmul,
      CompatibleScalarTensorMap.compatibleScalarTensorMap_tmul, map_mul]
    rfl
  | add z w hz hw =>
    simp only [smul_add, map_add, hz, hw]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleTensorScalarAction
