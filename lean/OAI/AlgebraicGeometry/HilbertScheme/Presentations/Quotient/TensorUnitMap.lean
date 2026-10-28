import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorRelations
import Mathlib.Algebra.Module.Torsion.Basic

/-! # Tensor Unit Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorUnitMap

noncomputable section

/-! The quotient tensor unit map has precisely the ideal multiple as
kernel, and its codomain is annihilated by that ideal. -/

open TensorProduct

universe u v
variable {B : Type u} [CommRing B] (M : Type v) [AddCommGroup M] [Module B M]

def quotientTensorUnitMap (I : Ideal B) : M →ₗ[B] (B ⧸ I) ⊗[B] M :=
  TensorProduct.mk B (B ⧸ I) M 1

theorem quotientTensorUnitMap_ker (I : Ideal B) :
    (quotientTensorUnitMap M I).ker = I • (⊤ : Submodule B M) := by
  ext m
  exact TensorRelations.quotientTensor_one_eq_zero_iff M I m

theorem quotientTensor_isTorsionBySet (I : Ideal B) :
    Module.IsTorsionBySet B ((B ⧸ I) ⊗[B] M) I := by
  intro x r
  change r.val • x = 0
  induction x with
  | tmul c m =>
    have hr : algebraMap B (B ⧸ I) r.val = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr r.property
    rw [TensorProduct.smul_tmul', Algebra.smul_def, hr, zero_mul, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.TensorUnitMap
