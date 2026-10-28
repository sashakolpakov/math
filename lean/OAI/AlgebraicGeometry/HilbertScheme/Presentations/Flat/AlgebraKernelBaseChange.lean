import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Algebra Kernel Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.AlgebraKernelBaseChange

noncomputable section

/-! Flat scalar extension preserves the actual kernel ideal of an algebra
map, without a surjectivity assumption on that map. -/

open TensorProduct

universe u v w z
variable {R : Type u} [CommRing R]
variable (A : Type v) [CommRing A] [Algebra R A] [Module.Flat R A]
variable {B : Type w} [CommRing B] [Algebra R B]
variable {C : Type z} [CommRing C] [Algebra R C]

theorem flat_tensor_algebra_kernel (g : B →ₐ[R] C) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R A) g) =
      (RingHom.ker g).map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) := by
  rw [← Submodule.restrictScalars_inj R]
  have he : (RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R A) g)).restrictScalars R =
      LinearMap.ker (LinearMap.lTensor A g.toLinearMap) := rfl
  rw [he, Ideal.map_includeRight_eq]
  rw [(Module.Flat.lTensor_exact A g.toLinearMap.exact_subtype_ker_map).linearMap_ker_eq]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.AlgebraKernelBaseChange
