import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Residue.CycleLifting

/-! # First Cycles Free -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesFree.LocalSectionLifting

noncomputable section

/-! First residue cohomology vanishing makes the degree-zero cycle module finite free over a local ring. -/
open _root_.CategoryTheory
universe u

theorem firstCycles_finite_free_of_residue_exact
    {R : Type u} [CommRing R] [IsLocalRing R] (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    (hS : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).Exact) :
    Module.Finite R S.f.hom.ker ∧ Module.Free R S.f.hom.ker := by
  obtain ⟨P⟩ := MinimalShortComplex.LocalSectionLifting.exists_localMinimalShortComplex S
  have hf : P.complex.f.hom = 0 := P.first_zero_of_residue_cycles_lift
    (fun z hz => Residue.CycleLifting.lift_residue_cycle_of_exact S hS z hz)
  let e : P.complex.f.hom.ker ≃ₗ[R] P.complex.X₁ :=
    LinearEquiv.ofBijective P.complex.f.hom.ker.subtype
      ⟨Subtype.val_injective, fun x => ⟨⟨x, by
        change P.complex.f.hom x = 0
        rw [hf, LinearMap.zero_apply]⟩, rfl⟩⟩
  let c : S.f.hom.ker ≃ₗ[R] P.complex.X₁ :=
    (ShortComplexFirstCycles.LocalSectionLifting.shortComplexFirstCyclesEquiv P.equivalence P.hom_h₀ P.inv_h₀).trans e
  exact ⟨Module.Finite.equiv c.symm, Module.Free.of_equiv c.symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesFree.LocalSectionLifting
