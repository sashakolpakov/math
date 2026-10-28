import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ResidueCycleLifting
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Algebra.Module.Projective

/-! # Residue Kernel Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ResidueKernelBaseChange

noncomputable section

/-! Under first-cohomology vanishing, every residue-field degree-zero
cycle is a linear combination of cycles of the original complex. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory
open scoped TensorProduct

universe u

theorem residue_cycle_mem_original_kernel_range
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] [Module.Flat R A]
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    (hS : (Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex A (IsLocalRing.ResidueField A)
      (Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R A S)).Exact)
    (z : IsLocalRing.ResidueField A ⊗[A] (A ⊗[R] S.X₁))
    (hz : (S.f.hom.baseChange A).baseChange (IsLocalRing.ResidueField A) z = 0) :
    z ∈ ((S.f.hom.ker.subtype.baseChange A).baseChange (IsLocalRing.ResidueField A)).range := by
  let T := Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R A S
  have : Module.Finite A T.X₁ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₁))
  have : Module.Finite A T.X₂ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₂))
  have : Module.Finite A T.X₃ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₃))
  have : Module.Flat A T.X₁ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₁))
  have : Module.Flat A T.X₂ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₂))
  have : Module.Flat A T.X₃ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₃))
  have : Module.Free A T.X₁ := Module.free_of_flat_of_isLocalRing
  have : Module.Free A T.X₂ := Module.free_of_flat_of_isLocalRing
  have : Module.Free A T.X₃ := Module.free_of_flat_of_isLocalRing
  obtain ⟨x, hx, he⟩ := ResidueCycleLifting.lift_residue_cycle_of_exact T hS z hz
  have hker : x ∈ (S.f.hom.ker.subtype.baseChange A).range := by
    change x ∈ (TensorProduct.AlgebraTensorModule.lTensor A A S.f.hom.ker.subtype).range
    rw [← Module.Flat.ker_lTensor_eq]
    exact hx
  obtain ⟨y, hy⟩ := hker
  refine ⟨(1 : IsLocalRing.ResidueField A) ⊗ₜ[A] y, ?_⟩
  change (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (S.f.hom.ker.subtype.baseChange A y) = z
  rw [hy]
  exact he

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ResidueKernelBaseChange
