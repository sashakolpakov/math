import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Balance Ideal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.BalanceIdeal.Constructions

noncomputable section

/-! Passing from the tensor product over the base to the tensor
product over an intermediate algebra imposes precisely the differences
between the two intermediate scalar actions. -/

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

universe u v w
variable (k : Type u) (P : Type v) (R : Type w) [CommRing k] [CommRing P] [CommRing R]
  [Algebra k P] [Algebra k R] [Algebra P R] [IsScalarTower k P R]

def balanceMap : R ⊗[k] R →ₐ[R] R ⊗[P] R :=
  Algebra.TensorProduct.mapOfCompatibleSMul P k R R R

def difference (p : P) : R ⊗[k] R :=
  algebraMap P R p ⊗ₜ[k] (1 : R) - (1 : R) ⊗ₜ[k] algebraMap P R p

theorem difference_mem_ker (p : P) : difference k P R p ∈ RingHom.ker (balanceMap k P R).toRingHom := by
  change balanceMap k P R (difference k P R p) = 0
  change (Algebra.TensorProduct.mapOfCompatibleSMul P k R R R)
    (algebraMap P R p ⊗ₜ[k] 1 - 1 ⊗ₜ[k] algebraMap P R p) = 0
  rw [map_sub, Algebra.TensorProduct.mapOfCompatibleSMul_tmul,
    Algebra.TensorProduct.mapOfCompatibleSMul_tmul, sub_eq_zero]
  simpa only [Algebra.smul_def, mul_one] using TensorProduct.smul_tmul p (1 : R) (1 : R)

theorem ker_eq_span : RingHom.ker (balanceMap k P R).toRingHom =
    Ideal.span (Set.range (difference k P R)) := by
  apply le_antisymm
  · have hk : (TensorProduct.mapOfCompatibleSMul P k P R R).ker ≤
        (Ideal.span (Set.range (difference k P R))).restrictScalars P := by
      rw [TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul]
      apply Submodule.span_le.mpr
      rintro _ ⟨p, m, n, rfl⟩
      change (p • m) ⊗ₜ[k] n - m ⊗ₜ[k] (p • n) ∈ Ideal.span (Set.range (difference k P R))
      have hm := Ideal.mul_mem_left (Ideal.span (Set.range (difference k P R)))
        (m ⊗ₜ[k] n) (Ideal.subset_span (Set.mem_range_self p))
      simpa only [difference, mul_sub, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, Algebra.smul_def, mul_comm] using hm
    intro x hx
    exact hk hx
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact difference_mem_ker k P R p

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.BalanceIdeal.Constructions
