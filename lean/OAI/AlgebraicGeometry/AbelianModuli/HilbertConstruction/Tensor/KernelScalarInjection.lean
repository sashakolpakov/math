import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Monomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelScalarExactness

/-! # Kernel Scalar Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelScalarInjection

noncomputable section

/-! A native scalar-extension monomorphism gives injectivity of the canonical tensor map on the original differential kernel. -/
open _root_.CategoryTheory
universe u

theorem tensor_kernel_injective_of_native_mono
    {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B)
    {M N : ModuleCat.{u} R} (d : M ⟶ N)
    (h : Mono ((ModuleCat.extendScalars f).map (ModuleCat.ofHom d.hom.ker.subtype))) :
    letI : Algebra R B := f.toAlgebra
    Function.Injective (d.hom.ker.subtype.lTensor B) := by
  let : Algebra R B := f.toAlgebra
  let i : ModuleCat.of R d.hom.ker ⟶ M := ModuleCat.ofHom d.hom.ker.subtype
  have hres : Mono ((ModuleCat.restrictScalars f).map ((ModuleCat.extendScalars f).map i)) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    exact (ModuleCat.mono_iff_injective ((ModuleCat.extendScalars f).map i)).mp h
  have ht : Mono ((Module.TensorFunctor.ModuleTensorFunctor.tensor B).map i) :=
    (Scalar.Monomorphisms.mono_map_iff_of_functor_iso (Extension.TensorExtension.iso f) i).mpr hres
  exact (ModuleCat.mono_iff_injective _).mp ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelScalarInjection
