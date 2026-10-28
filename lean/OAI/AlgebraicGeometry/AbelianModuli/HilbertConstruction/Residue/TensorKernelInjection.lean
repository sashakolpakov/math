import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.LocalFirstCyclesSplitting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitTensorInjection

/-! # Tensor Kernel Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.TensorKernelInjection

noncomputable section

/-! First residue cohomology vanishing makes every further scalar extension of the localized original cycle inclusion injective. -/
open _root_.CategoryTheory
open scoped TensorProduct
universe u

theorem iterated_tensor_original_kernel_injective
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [IsLocalRing A] [Module.Flat R A]
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    (hS : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex A (IsLocalRing.ResidueField A)
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R A S)).Exact) :
    Function.Injective ((S.f.hom.ker.subtype.baseChange A).baseChange B) := by
  obtain ⟨r, hr⟩ := HilbertConstruction.Flat.LocalFirstCyclesSplitting.LocalSectionLifting.firstCycles_inclusion_split_after_flat_local_baseChange S hS
  exact SplitTensorInjection.baseChange_injective_of_linear_retraction (S.f.hom.ker.subtype.baseChange A) r hr

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.TensorKernelInjection
