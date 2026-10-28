import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesFree

/-! # First Cycles Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesSplitting.LocalSectionLifting

noncomputable section

/-! First residue cohomology vanishing splits the degree-zero kernel inclusion of a finite free complex over a local ring. -/
open _root_.CategoryTheory
universe u

theorem firstCycles_inclusion_split_of_residue_exact
    {R : Type u} [CommRing R] [IsLocalRing R] (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    (hS : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).Exact) :
    ∃ r : S.X₁ →ₗ[R] S.f.hom.ker, r.comp S.f.hom.ker.subtype = LinearMap.id := by
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
  refine ⟨c.symm.toLinearMap.comp P.equivalence.hom.τ₁.hom, ?_⟩
  apply LinearMap.ext
  intro x
  change c.symm (c x) = x
  exact c.symm_apply_apply x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FirstCyclesSplitting.LocalSectionLifting
