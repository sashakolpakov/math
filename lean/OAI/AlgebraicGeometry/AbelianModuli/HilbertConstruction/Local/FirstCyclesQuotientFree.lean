import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesSplitting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SplitSubmoduleQuotientProjective

/-! # First Cycles Quotient Free -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesQuotientFree.LocalSectionLifting

noncomputable section

/-! First residue cohomology vanishing makes the quotient by degree-zero cycles finite free over a local ring. -/
open _root_.CategoryTheory
universe u

theorem firstCycles_quotient_finite_free_of_residue_exact
    {R : Type u} [CommRing R] [IsLocalRing R] (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    (hS : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).Exact) :
    Module.Finite R (S.X₁ ⧸ S.f.hom.ker) ∧ Module.Free R (S.X₁ ⧸ S.f.hom.ker) := by
  obtain ⟨r, hr⟩ := FirstCyclesSplitting.LocalSectionLifting.firstCycles_inclusion_split_of_residue_exact S hS
  have : Module.Projective R (S.X₁ ⧸ S.f.hom.ker) :=
    SplitSubmoduleQuotientProjective.quotient_projective_of_submodule_retraction S.f.hom.ker r hr
  exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesQuotientFree.LocalSectionLifting
