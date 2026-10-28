import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalCycleDetection

/-! # Residue Cycle Lifting -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ResidueCycleLifting

noncomputable section

/-! Vanishing of first residue-field cohomology lifts every degree-zero
residue cycle of a finite free complex over a local ring. -/

open _root_.CategoryTheory
open scoped TensorProduct
open OAI.AlgebraicGeometry.Quotients.FiniteDescent.LocalCycleDetection.Construction.LocalSectionLifting

universe u

theorem lift_residue_cycle_of_exact
    {R : Type u} [CommRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R S.X₁] [Module.Free R S.X₁]
    [Module.Finite R S.X₂] [Module.Free R S.X₂]
    [Module.Finite R S.X₃] [Module.Free R S.X₃]
    (hS : (Quotients.FiniteDescent.ModuleBaseChangeComplex.Construction.LocalSectionLifting.moduleBaseChangeComplex R (IsLocalRing.ResidueField R) S).Exact)
    (z : IsLocalRing.ResidueField R ⊗[R] S.X₁)
    (hz : S.f.hom.baseChange (IsLocalRing.ResidueField R) z = 0) :
    ∃ x : S.X₁, S.f x = 0 ∧ (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = z := by
  apply Quotients.FiniteDescent.LocalCycleDetection.Construction.LocalSectionLifting.lift_cycle S (ModuleCat.of R (Fin 0 → R)) 0 (by simp) _ z hz
  intro w hw _
  exact (ShortComplex.moduleCat_exact_iff_ker_sub_range _).mp hS hw

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ResidueCycleLifting
