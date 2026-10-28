import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Differential Kernels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.DifferentialKernels

noncomputable section

/-! The canonical map from tensors of a differential kernel to the kernel of the tensored differential, with its actual values and surjectivity criterion. -/
open _root_.CategoryTheory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (A : Type u) [AddCommGroup A] [Module R A]
variable {M N : ModuleCat.{u} R} (d : M ⟶ N)

def tensorDifferentialKernelMap : A ⊗[R] d.hom.ker →ₗ[R] (d.hom.lTensor A).ker :=
  (d.hom.ker.subtype.lTensor A).codRestrict _ (by
    intro z
    have h : (d.hom.lTensor A).comp (d.hom.ker.subtype.lTensor A) = 0 := by
      rw [← LinearMap.lTensor_comp]
      have hzero : d.hom.comp d.hom.ker.subtype = 0 := by
        ext m
        exact m.property
      rw [hzero]
      exact LinearMap.lTensor_zero A
    exact congrArg (fun f => f z) h)

theorem tensorDifferentialKernelMap_val (z : A ⊗[R] d.hom.ker) :
    (tensorDifferentialKernelMap A d z).val = d.hom.ker.subtype.lTensor A z := rfl

theorem tensorDifferentialKernelMap_tmul_val (a : A) (m : d.hom.ker) :
    (tensorDifferentialKernelMap A d (a ⊗ₜ[R] m)).val = a ⊗ₜ[R] m.val := rfl

theorem tensorDifferentialKernelMap_surjective
    (h : (d.hom.lTensor A).ker ≤ (d.hom.ker.subtype.lTensor A).range) :
    Function.Surjective (tensorDifferentialKernelMap A d) := by
  intro z
  obtain ⟨w, hw⟩ := h z.property
  exact ⟨w, Subtype.ext hw⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.DifferentialKernels
