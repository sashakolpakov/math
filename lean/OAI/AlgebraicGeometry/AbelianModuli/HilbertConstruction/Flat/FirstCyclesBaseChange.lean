import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesFree
import Mathlib.RingTheory.Flat.Equalizer

/-! # First Cycles Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.FirstCyclesBaseChange.LocalSectionLifting

noncomputable section

/-! A flat local scalar extension with zero first residue cohomology makes the original degree-zero cycle module finite free after scalar extension. -/
open _root_.CategoryTheory
open scoped TensorProduct
universe u

theorem firstCycles_finite_free_after_flat_local_baseChange
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing A] [Module.Flat R A]
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    (hS : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex A (IsLocalRing.ResidueField A)
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R A S)).Exact) :
    Module.Finite A (A ⊗[R] S.f.hom.ker) ∧ Module.Free A (A ⊗[R] S.f.hom.ker) := by
  let T := HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R A S
  have : Module.Finite A T.X₁ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₁))
  have : Module.Finite A T.X₂ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₂))
  have : Module.Finite A T.X₃ := inferInstanceAs (Module.Finite A (A ⊗[R] S.X₃))
  have : Module.Flat A T.X₁ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₁))
  have : Module.Flat A T.X₂ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₂))
  have : Module.Flat A T.X₃ := inferInstanceAs (Module.Flat A (A ⊗[R] S.X₃))
  have : Module.Free A T.X₁ := Module.free_of_flat_of_isLocalRing
  have : Module.Free A T.X₂ := Module.free_of_flat_of_isLocalRing
  have : Module.Free A T.X₃ := Module.free_of_flat_of_isLocalRing
  obtain ⟨hfinite, hfree⟩ := Local.FirstCyclesFree.LocalSectionLifting.firstCycles_finite_free_of_residue_exact T hS
  let e : A ⊗[R] S.f.hom.ker ≃ₗ[A] T.f.hom.ker := S.f.hom.tensorKerEquiv A A
  exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.FirstCyclesBaseChange.LocalSectionLifting
