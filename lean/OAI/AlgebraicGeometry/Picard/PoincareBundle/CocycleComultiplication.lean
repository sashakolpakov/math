import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoalgebraTensorMaps

/-! # Cocycle Comultiplication -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleComultiplication

noncomputable section

/-! The linear comultiplication obtained by multiplying by a cocycle. -/

universe u v

open Coalgebra TensorProduct

variable (k : Type u) (R : Type v) [CommRing k] [CommRing R] [Bialgebra k R]

/-- The original comultiplication multiplied by a tensor. -/
def twisted (c : R ⊗[k] R) : R →ₗ[k] R ⊗[k] R :=
  (LinearMap.mul k (R ⊗[k] R) c).comp comul

@[simp]
theorem twisted_apply (c : R ⊗[k] R) (a : R) : twisted k R c a = c * comul a := rfl

theorem rTensor_twisted (c z : R ⊗[k] R) :
    (twisted k R c).rTensor R z =
      (c ⊗ₜ[k] (1 : R)) * (comul (R := k) (A := R)).rTensor R z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => simp only [map_add, ha, hb, mul_add]

theorem lTensor_twisted (c z : R ⊗[k] R) :
    (twisted k R c).lTensor R z =
      ((1 : R) ⊗ₜ[k] c) * (comul (R := k) (A := R)).lTensor R z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => simp only [map_add, ha, hb, mul_add]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CocycleComultiplication
