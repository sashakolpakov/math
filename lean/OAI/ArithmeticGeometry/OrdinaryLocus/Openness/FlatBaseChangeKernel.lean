import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleBaseChangeComplex
import Mathlib.RingTheory.Flat.Basic

/-! # Flat Base Change Kernel -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatBaseChangeKernel.Construction

noncomputable section

/-! The canonical comparison between the tensor of a kernel and the kernel after flat base change. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u v

variable {R : Type u} (K : Type u) [CommRing R] [CommRing K] [Algebra R K]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N)

theorem baseChange_kernel_subtype_comp :
    (f.baseChange K).comp (f.ker.subtype.baseChange K) = 0 := by
  rw [← LinearMap.baseChange_comp]
  have h : f.comp f.ker.subtype = 0 := by
    ext x
    exact x.property
  rw [h, LinearMap.baseChange_zero]

def baseChangeKernelMap : (K ⊗[R] f.ker) →ₗ[K] (f.baseChange K).ker :=
  (f.ker.subtype.baseChange K).codRestrict _ (fun x ↦
    LinearMap.congr_fun (baseChange_kernel_subtype_comp K f) x)

theorem baseChangeKernelMap_bijective [Module.Flat R K] : Function.Bijective (baseChangeKernelMap K f) := by
  constructor
  · intro x y h
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := K) f.ker.subtype
      Subtype.val_injective (congrArg Subtype.val h)
  · intro z
    have he := Module.Flat.lTensor_exact K f.exact_subtype_ker_map
    obtain ⟨x, hx⟩ := (he z.val).mp z.property
    exact ⟨x, Subtype.ext hx⟩

def flatBaseChangeKernelEquiv [Module.Flat R K] :
    (K ⊗[R] f.ker) ≃ₗ[K] (f.baseChange K).ker :=
  LinearEquiv.ofBijective (baseChangeKernelMap K f) (baseChangeKernelMap_bijective K f)

theorem flatBaseChangeKernelEquiv_tmul [Module.Flat R K] (a : K) (x : f.ker) :
    (flatBaseChangeKernelEquiv K f (a ⊗ₜ[R] x)).val = a ⊗ₜ[R] x.val := rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FlatBaseChangeKernel.Construction
