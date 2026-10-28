import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.KernelFieldCriterion

/-! # Kernel Field Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelFieldCriterion

noncomputable section

/-! The universal completeness criterion is unchanged when tensor
complexes are viewed over the original coefficient ring. This matches
the coefficient convention of the geometric Cech tensor comparison. -/
open _root_.CategoryTheory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]
variable {V M N : Type u}
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable (s : V →ₗ[R] M) (d : M →ₗ[R] N) (h : d.comp s = 0)

def tensorCycleComparison (A : Type u) [AddCommGroup A] [Module R A] :
    (A ⊗[R] V) →ₗ[R] (d.lTensor A).ker :=
  KernelDimensionCriterion.linearKernelComparison (s.lTensor A) (d.lTensor A) (by
    rw [← LinearMap.lTensor_comp, h]
    exact LinearMap.lTensor_zero A)

theorem scalarExtendedCycleComparison_bijective_iff_tensor
    (B : Type u) [CommRing B] [Algebra R B] :
    Function.Bijective (Universal.KernelFieldCriterion.scalarExtendedCycleComparison s d h B) ↔
      Function.Bijective (tensorCycleComparison s d h B) := by
  change Function.Bijective (KernelDimensionCriterion.linearKernelComparison (s.baseChange B) (d.baseChange B) _) ↔
    Function.Bijective (KernelDimensionCriterion.linearKernelComparison (s.lTensor B) (d.lTensor B) _)
  rw [Linear.KernelExactCriterion.linearKernelComparison_bijective_iff_values, Linear.KernelExactCriterion.linearKernelComparison_bijective_iff_values]
  simp only [LinearMap.baseChange_eq_ltensor]

theorem completeKernel_tensor_universal_of_field_tests
    [Module.Finite R V] [Module.Projective R V]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (hfield : ∀ (K : Type u) [Field K] (q : R →+* K),
      letI := q.toAlgebra
      Function.Bijective (tensorCycleComparison s d h K))
    (B : Type u) [CommRing B] [Algebra R B] :
    Function.Bijective (tensorCycleComparison s d h B) := by
  apply (scalarExtendedCycleComparison_bijective_iff_tensor s d h B).mp
  apply Universal.KernelFieldCriterion.completeKernel_universal_of_field_tests s d h
  intro K _ q
  let := q.toAlgebra
  exact (scalarExtendedCycleComparison_bijective_iff_tensor s d h K).mpr (hfield K q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.KernelFieldCriterion
