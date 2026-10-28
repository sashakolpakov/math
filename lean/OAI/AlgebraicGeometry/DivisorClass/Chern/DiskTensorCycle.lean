import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorBoundary
import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

/-! # Disk Tensor Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.DiskTensorCycle

noncomputable section

/-! The actual tensor of a degree-two cycle and any cycle is closed. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type} [Field k] (C D : ChainComplex (ModuleCat.{0} k) ℕ)

def diskTensorCycle (q : ℕ) (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C 2) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D q) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (C ⊗ D) (2 + q) :=
  ⟨ιTensorObj C D 2 q (2 + q) rfl (x.val ⊗ₜ[k] y.val), by
    cases q with
    | zero =>
        rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
        have h := ConcreteCategory.congr_hom (TensorBoundary.tensorBoundary_rightZero C D 1) (x.val ⊗ₜ[k] y.val)
        change (C ⊗ D).d 2 1 (ιTensorObj C D 2 0 2 _ (x.val ⊗ₜ[k] y.val)) =
          ιTensorObj C D 1 0 1 _ (TensorProduct.map (C.d 2 1).hom LinearMap.id (x.val ⊗ₜ[k] y.val)) at h
        rw [TensorProduct.map_tmul, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero C 2 1 x, TensorProduct.zero_tmul, map_zero] at h
        exact h
    | succ q =>
        change (C ⊗ D).d (2 + (q + 1)) ((ComplexShape.down ℕ).next (2 + (q + 1)))
          (ιTensorObj C D 2 (q + 1) (2 + (q + 1)) rfl (x.val ⊗ₜ[k] y.val)) = 0
        rw [(ComplexShape.down ℕ).next_eq'
          (show (ComplexShape.down ℕ).Rel (2 + (q + 1)) (1 + (q + 1)) from by
            change 1 + (q + 1) + 1 = 2 + (q + 1)
            omega)]
        have h := TensorBoundary.tensorBoundary_disk_apply C D q x.val y.val
        rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero C 2 1 x, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero D (q + 1) q y,
          TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, map_zero, add_zero] at h
        exact h⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.DiskTensorCycle
