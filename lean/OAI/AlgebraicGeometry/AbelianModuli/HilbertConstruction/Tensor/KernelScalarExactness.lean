import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ScalarExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.DifferentialKernels

/-! # Kernel Scalar Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelScalarExactness

noncomputable section

/-! Native exactness after scalar extension gives the kernel-range condition for the original tensor module structure. -/
open _root_.CategoryTheory
universe u

theorem tensor_kernel_range_of_native_exact
    {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B)
    {M N : ModuleCat.{u} R} (d : M ⟶ N)
    (h : (d.hom.shortComplexKer.map (ModuleCat.extendScalars f)).Exact) :
    letI : Algebra R B := f.toAlgebra
    (d.hom.lTensor B).ker ≤ (d.hom.ker.subtype.lTensor B).range := by
  let : Algebra R B := f.toAlgebra
  have ht : (d.hom.shortComplexKer.map (Module.TensorFunctor.ModuleTensorFunctor.tensor B)).Exact :=
    (ScalarExactness.tensor_shortComplex_exact_iff_native f d.hom.shortComplexKer).mpr h
  exact (ShortComplex.moduleCat_exact_iff_ker_sub_range _).mp ht

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelScalarExactness
