import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Bilinear Tensor Symmetry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BilinearTensorSymmetry

noncomputable section

/-! Evaluating the alternating coefficient tensor of a bilinear
form detects its symmetry. The calculation uses the original basis and
its dual coordinate forms, without an exterior-algebra comparison. -/

open scoped TensorProduct BigOperators

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]

def dualTensorEvaluation (z w : V) :
    Module.Dual k V ⊗[k] Module.Dual k V →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp
    (TensorProduct.map (LinearMap.applyₗ' k z) (LinearMap.applyₗ' k w))

theorem dualTensorEvaluation_tmul (z w : V) (p q : Module.Dual k V) :
    dualTensorEvaluation z w (p ⊗ₜ[k] q) = p z * q w := by
  change (TensorProduct.lid k k)
    (TensorProduct.map (LinearMap.applyₗ' k z) (LinearMap.applyₗ' k w) (p ⊗ₜ[k] q)) = _
  rw [TensorProduct.map_tmul]
  exact TensorProduct.lid_tmul (q w) (p z)

theorem dualTensorEvaluation_comm (z w : V) (t : Module.Dual k V ⊗[k] Module.Dual k V) :
    dualTensorEvaluation z w (TensorProduct.comm k (Module.Dual k V) (Module.Dual k V) t) =
      dualTensorEvaluation w z t := by
  induction t using TensorProduct.inductionOn with
  | tmul p q => rw [TensorProduct.comm_tmul, dualTensorEvaluation_tmul, dualTensorEvaluation_tmul, mul_comm]
  | add t u ht hu => rw [map_add, map_add, map_add, ht, hu]

variable {I : Type*} [Fintype I] (b : Module.Basis I k V)
    (F : V →ₗ[k] V →ₗ[k] k)

def bilinearCoefficientTensor : Module.Dual k V ⊗[k] Module.Dual k V :=
  ∑ i, F (b i) ⊗ₜ[k] b.coord i

theorem bilinearCoefficientTensor_evaluate (z w : V) :
    dualTensorEvaluation z w (bilinearCoefficientTensor b F) = F w z := by
  unfold bilinearCoefficientTensor
  rw [map_sum]
  simp only [dualTensorEvaluation_tmul, Module.Basis.coord_apply]
  have h := congrArg (fun x => F x z) (b.sum_repr w)
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h
  exact (Finset.sum_congr rfl (fun i _ => mul_comm (F (b i) z) (b.repr w i))).trans h

theorem bilinear_symm_of_alternating_coefficientTensor_zero
    (h : bilinearCoefficientTensor b F -
      TensorProduct.comm k (Module.Dual k V) (Module.Dual k V) (bilinearCoefficientTensor b F) = 0)
    (z w : V) : F z w = F w z := by
  have he := congrArg (dualTensorEvaluation z w) h
  rw [map_sub, map_zero, dualTensorEvaluation_comm,
    bilinearCoefficientTensor_evaluate, bilinearCoefficientTensor_evaluate] at he
  exact (sub_eq_zero.mp he).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BilinearTensorSymmetry
