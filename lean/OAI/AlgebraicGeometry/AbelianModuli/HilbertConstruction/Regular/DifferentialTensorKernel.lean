import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.DifferentialKernels

/-! # Differential Tensor Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.DifferentialTensorKernel

noncomputable section

/-! A generalized inverse to a differential makes its kernel commute with every tensor module. The proof uses the explicit projection onto the kernel. -/
open scoped TensorProduct
universe u

variable {R : Type u} [CommRing R]

theorem tensor_kernel_range_of_generalizedInverse
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (r : N →ₗ[R] M) (hr : f.comp (r.comp f) = f)
    (B : Type u) [AddCommGroup B] [Module R B] :
    (f.lTensor B).ker ≤ (f.ker.subtype.lTensor B).range := by
  let q : M →ₗ[R] f.ker := (LinearMap.id - r.comp f).codRestrict _ (by
    intro m
    change f (m - r (f m)) = 0
    rw [map_sub]
    have hm : f (r (f m)) = f m := LinearMap.congr_fun hr m
    rw [hm, sub_self])
  have hq : (f.ker.subtype.lTensor B).comp (q.lTensor B) =
      LinearMap.id - (r.lTensor B).comp (f.lTensor B) := by
    apply TensorProduct.ext'
    intro b m
    change b ⊗ₜ[R] (m - r (f m)) = b ⊗ₜ[R] m - b ⊗ₜ[R] r (f m)
    exact TensorProduct.tmul_sub b m (r (f m))
  intro z hz
  refine ⟨q.lTensor B z, ?_⟩
  have h := LinearMap.congr_fun hq z
  change (f.ker.subtype.lTensor B) (q.lTensor B z) = z - r.lTensor B (f.lTensor B z) at h
  change f.lTensor B z = 0 at hz
  rw [hz, map_zero, sub_zero] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.DifferentialTensorKernel
