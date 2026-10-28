import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Kernel -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.Kernel.FlatKernel

noncomputable section

/-! Flat kernels of surjections between flat modules. -/

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem prod [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro A B _ _ _ _ a ha
  let eA := TensorProduct.prodRight R R A M N
  let eB := TensorProduct.prodRight R R B M N
  have hmap : eB.toLinearMap.comp (a.rTensor (M × N)) =
      ((a.rTensor M).prodMap (a.rTensor N)).comp eA.toLinearMap := by
    ext x y <;> simp [eA, eB]
  intro x y hxy
  apply eA.injective
  apply Prod.ext
  · apply Module.Flat.rTensor_preserves_injective_linearMap (M := M) a ha
    exact congrArg Prod.fst ((LinearMap.congr_fun hmap x).symm.trans
      ((congrArg eB hxy).trans (LinearMap.congr_fun hmap y)))
  · apply Module.Flat.rTensor_preserves_injective_linearMap (M := N) a ha
    exact congrArg Prod.snd ((LinearMap.congr_fun hmap x).symm.trans
      ((congrArg eB hxy).trans (LinearMap.congr_fun hmap y)))

theorem flat [Module.Flat R M] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Flat R f.ker := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro A B _ _ _ _ a ha
  have hi := LinearMap.lTensor_injective_of_exact_of_flat f hf f.ker.subtype
    f.ker.subtype_injective (LinearMap.exact_subtype_ker_map f) A
  have ht := Module.Flat.rTensor_preserves_injective_linearMap (M := M) a ha
  intro x y hxy
  apply hi
  apply ht
  have he : (a.rTensor M).comp (f.ker.subtype.lTensor A) =
      (f.ker.subtype.lTensor B).comp (a.rTensor f.ker) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  exact (LinearMap.congr_fun he x).trans
    ((congrArg (f.ker.subtype.lTensor B) hxy).trans (LinearMap.congr_fun he y).symm)

/-- The kernel in this reduction commutes with every scalar tensor,
without a flatness hypothesis on the tensor factor. -/
def tensorIso [Module.Flat R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (A : Type*) [AddCommGroup A] [Module R A] :
    LinearMap.ker (f.lTensor A) ≃ₗ[R] A ⊗[R] f.ker :=
  f.kerLTensorEquivOfSurjective hf A

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.Kernel.FlatKernel
