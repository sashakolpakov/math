import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Projective Tensor Dual -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ProjectiveTensorDual.Construction

noncomputable section

/-! Tensoring a finite projective module is represented by linear maps
from its dual. The kernel of a differential is detected on its dual image. -/

open scoped TensorProduct

universe u v w t
variable (R : Type u) [CommRing R]
  (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  (M : Type w) [AddCommGroup M] [Module R M]

def finiteProjectiveTensorDualEquiv :
    TensorProduct R M P ≃ₗ[R] (Module.Dual R P →ₗ[R] M) :=
  (TensorProduct.comm R M P).trans
    ((TensorProduct.congr (Module.evalEquiv R P) (LinearEquiv.refl R M)).trans
      (dualTensorHomEquiv R (Module.Dual R P) M))

theorem finiteProjectiveTensorDualEquiv_tmul (m : M) (p : P) (φ : Module.Dual R P) :
    finiteProjectiveTensorDualEquiv R P M (m ⊗ₜ[R] p) φ = φ p • m := rfl

variable {Q : Type t} [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]

theorem finiteProjectiveTensorDualEquiv_map (d : P →ₗ[R] Q)
    (x : TensorProduct R M P) (φ : Module.Dual R Q) :
    finiteProjectiveTensorDualEquiv R Q M (d.lTensor M x) φ =
      finiteProjectiveTensorDualEquiv R P M x (d.dualMap φ) := by
  induction x using TensorProduct.inductionOn with
  | tmul m p => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem finiteProjectiveTensor_kernel_iff (d : P →ₗ[R] Q) (x : TensorProduct R M P) :
    d.lTensor M x = 0 ↔ ∀ φ : Module.Dual R Q,
      finiteProjectiveTensorDualEquiv R P M x (d.dualMap φ) = 0 := by
  constructor
  · intro hx φ
    rw [← finiteProjectiveTensorDualEquiv_map, hx, map_zero, LinearMap.zero_apply]
  · intro hx
    apply (finiteProjectiveTensorDualEquiv R Q M).injective
    rw [map_zero]
    apply LinearMap.ext
    intro φ
    exact (finiteProjectiveTensorDualEquiv_map R P M d x φ).trans (hx φ)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ProjectiveTensorDual.Construction
