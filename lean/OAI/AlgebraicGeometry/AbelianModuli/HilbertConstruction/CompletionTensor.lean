import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CokernelCompletion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KernelTransportEquiv
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompletionCokernelEq

/-! # Completion Tensor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompletionTensor.CompletionTensorKernel

noncomputable section

/-! The kernel of the finite replacement computes degree-zero cohomology
after every tensor base change. -/

open scoped TensorProduct

universe u v w z t

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {F : Type z} [AddCommGroup F] [Module R F]
variable (f : M →ₗ[R] N) (v : F →ₗ[R] N)
variable (A : Type t) [AddCommGroup A] [Module R A]

theorem tensor_coprod :
    ((f.lTensor A).coprod (v.lTensor A)).comp (TensorProduct.prodRight R R A M F).toLinearMap =
      (f.coprod v).lTensor A := by
  ext a x <;> simp

def splitKernel : ((f.coprod v).lTensor A).ker ≃ₗ[R]
    ((f.lTensor A).coprod (v.lTensor A)).ker :=
  KernelTransportEquiv.KernelTransport.equiv (TensorProduct.prodRight R R A M F)
    ((f.coprod v).lTensor A) ((f.lTensor A).coprod (v.lTensor A)) (tensor_coprod f v A)

variable [Module.Flat R N] (h : Function.Surjective (f.coprod v))

def completionIso : A ⊗[R] (f.coprod v).ker ≃ₗ[R]
    ((f.lTensor A).coprod (v.lTensor A)).ker :=
  (HilbertConstruction.Flat.Kernel.FlatKernel.tensorIso (f.coprod v) h A).symm.trans (splitKernel f v A)

theorem completionIso_tmul (a : A) (x : (f.coprod v).ker) :
    (completionIso f v A h (a ⊗ₜ[R] x)).val = (a ⊗ₜ[R] x.val.1, a ⊗ₜ[R] x.val.2) := by
  change TensorProduct.prodRight R R A M F
      (((f.coprod v).kerLTensorEquivOfSurjective h A).symm (a ⊗ₜ[R] x)).val = _
  rw [LinearMap.tensorKerEquivOfSurjective_symm_tmul, TensorProduct.prodRight_tmul]

theorem projection_comp :
    (CokernelCompletion.CokernelCompletionKernel.projection (f.lTensor A) (v.lTensor A)).comp
      (completionIso f v A h).toLinearMap =
        (CokernelCompletion.CokernelCompletionKernel.projection f v).lTensor A := by
  ext a x
  change (completionIso f v A h (a ⊗ₜ[R] x)).val.2 = a ⊗ₜ[R] x.val.2
  rw [completionIso_tmul]

def zeroCohomologyIso : ((CokernelCompletion.CokernelCompletionKernel.projection f v).lTensor A).ker ≃ₗ[R]
    (f.lTensor A).ker :=
  (KernelTransportEquiv.KernelTransport.equiv (completionIso f v A h)
    ((CokernelCompletion.CokernelCompletionKernel.projection f v).lTensor A)
    (CokernelCompletion.CokernelCompletionKernel.projection (f.lTensor A) (v.lTensor A))
    (projection_comp f v A h)).trans
      (CokernelCompletion.CokernelCompletionKernel.kernelIso (f.lTensor A) (v.lTensor A))

include h in
omit [Module.Flat R N] in
theorem tensor_surjective : Function.Surjective ((f.lTensor A).coprod (v.lTensor A)) := by
  intro x
  obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective A h x
  exact ⟨TensorProduct.prodRight R R A M F y,
    (LinearMap.congr_fun (tensor_coprod f v A) y).trans hy⟩

include h in
theorem projection_range : ((CokernelCompletion.CokernelCompletionKernel.projection f v).lTensor A).range =
    (CokernelCompletion.CokernelCompletionKernel.projection (f.lTensor A) (v.lTensor A)).range := by
  rw [← projection_comp f v A h]
  apply LinearMap.range_comp_of_range_eq_top
  exact LinearMap.range_eq_top.mpr (completionIso f v A h).surjective

def oneCohomologyIso :
    ((A ⊗[R] F) ⧸ ((CokernelCompletion.CokernelCompletionKernel.projection f v).lTensor A).range) ≃ₗ[R]
      ((A ⊗[R] N) ⧸ (f.lTensor A).range) :=
  (Submodule.quotEquivOfEq _ _ (projection_range f v A h)).trans
    (CompletionCokernelEq.CompletionCokernel.iso (f.lTensor A) (v.lTensor A) (tensor_surjective f v A h))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompletionTensor.CompletionTensorKernel
