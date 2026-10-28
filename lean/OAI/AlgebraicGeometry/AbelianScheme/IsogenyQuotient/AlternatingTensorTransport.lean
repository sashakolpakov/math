import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Alternating Tensor Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlternatingTensorTransport.Construction

/-! Transport an alternating tensor relation and cancel a nonzero scalar. -/

open scoped TensorProduct BigOperators

theorem alternatingTensor_transport_cancel
    {k H V I : Type*} [Field k] [AddCommGroup H] [Module k H]
    [AddCommGroup V] [Module k V] [Fintype I]
    (e : H →ₗ[k] V) (x y : I → H) (w z : I → V) (c : k) (hc : c ≠ 0)
    (hx : ∀ i, e (x i) = w i) (hy : ∀ i, e (y i) = c • z i)
    (h : ∑ i, (x i ⊗ₜ[k] y i - y i ⊗ₜ[k] x i) = 0) :
    ∑ i, (w i ⊗ₜ[k] z i - z i ⊗ₜ[k] w i) = 0 := by
  have he := congrArg (TensorProduct.map e e) h
  simp only [map_sum, map_sub, map_zero, TensorProduct.map_tmul, hx, hy] at he
  have hs : c • (∑ i, (w i ⊗ₜ[k] z i - z i ⊗ₜ[k] w i)) = 0 := by
    simpa only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
      ← smul_sub, ← Finset.smul_sum] using he
  exact (smul_eq_zero.mp hs).resolve_left hc

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AlternatingTensorTransport.Construction
