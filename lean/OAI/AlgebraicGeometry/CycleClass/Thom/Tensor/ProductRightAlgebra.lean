import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Product Right Algebra -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightAlgebra.Constructions

noncomputable section

/-! Swapping algebra tensor factors identifies the right algebra
structure with the left one through the actual tensor permutation. -/

open scoped TensorProduct

universe u
variable (k R S : Type u) [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def rightSwap : R ⊗[k] S ≃ₐ[S] S ⊗[k] R :=
  (Algebra.TensorProduct.commRight k S R).symm

theorem rightSwap_tmul (r : R) (s : S) : rightSwap k R S (r ⊗ₜ[k] s) = s ⊗ₜ[k] r := rfl

variable (N : Type u) [AddCommGroup N] [Module k N] [Module S N] [IsScalarTower k S N]

def rightTensorCancel : (R ⊗[k] S) ⊗[S] N ≃ₗ[S] N ⊗[k] R :=
  ((TensorProduct.congr (rightSwap k R S).toLinearEquiv (LinearEquiv.refl S N)).trans
    (TensorProduct.comm S (S ⊗[k] R) N)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k S S N R)

theorem rightTensorCancel_tmul (r : R) (s : S) (n : N) :
    rightTensorCancel k R S N ((r ⊗ₜ[k] s) ⊗ₜ[S] n) = (s • n) ⊗ₜ[k] r := by
  simp only [rightTensorCancel, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    AlgEquiv.toLinearEquiv_apply, rightSwap_tmul, LinearEquiv.refl_apply, TensorProduct.comm_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

def tensorCancel : (R ⊗[k] S) ⊗[S] N ≃ₗ[k] R ⊗[k] N :=
  ((rightTensorCancel k R S N).restrictScalars k).trans (TensorProduct.comm k N R)

theorem tensorCancel_tmul (r : R) (s : S) (n : N) :
    tensorCancel k R S N ((r ⊗ₜ[k] s) ⊗ₜ[S] n) = r ⊗ₜ[k] (s • n) := by
  simp only [tensorCancel, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    rightTensorCancel_tmul, TensorProduct.comm_tmul]

theorem tensorCancel_smul (a : R) (t : (R ⊗[k] S) ⊗[S] N) :
    tensorCancel k R S N (a • t) = a • tensorCancel k R S N t := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul x n =>
    rw [TensorProduct.smul_tmul']
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [smul_add, TensorProduct.add_tmul, map_add, hx, hy]
    | tmul r s => simp only [TensorProduct.smul_tmul', tensorCancel_tmul]

def leftLinearCancel : (R ⊗[k] S) ⊗[S] N ≃ₗ[R] R ⊗[k] N where
  __ := (tensorCancel k R S N).toAddEquiv
  map_smul' := tensorCancel_smul k R S N

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightAlgebra.Constructions
