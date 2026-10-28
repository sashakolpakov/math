import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Interface

/-! # Weak Admissibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibility

noncomputable section

/-! The complete repaired WeakAdmissibility proposition on its independently defined period objects. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.MaximalUnramified OAI.NumberTheory.PadicHodge.WeakAdmissibility.ValuationStructure
  WeakAdmissibility.DcrisD WeakAdmissibility.GeometricFiltration WeakAdmissibility.Interface

/-- Full weak admissibility, including all stable-subspace inequalities and native identifications. -/
def WeakAdmissibilityInput : Prop :=
  ∀
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [Module.Finite ℚ_[p] K]
    (ρ : WeakAdmissibility.Interface.FinitePadicGaloisRep p K)
    (_hρ : WeakAdmissibility.Interface.FinitePadicGaloisRep.IsCrystalline p K ρ),
    ∃ hfin : Module.Finite (WeakAdmissibility.MaximalUnramified.K0 p K) (WeakAdmissibility.DcrisD.Dcris p K ρ.rho),
      letI := hfin
      Function.Bijective (WeakAdmissibility.Interface.crystallineComparison p K ρ.rho) ∧
      ∃ D : WeakAdmissibility.FilteredRepresentations.Construction.FilteredFrobeniusModule (WeakAdmissibility.MaximalUnramified.K0 p K) K (WeakAdmissibility.DcrisD.Dcris p K ρ.rho),
        (∀ a : WeakAdmissibility.MaximalUnramified.K0 p K, D.frobenius.sigma a = WeakAdmissibility.ValuationStructure.k0Frobenius p K a) ∧
        D.frobenius.period = Module.finrank ℚ_[p] (WeakAdmissibility.MaximalUnramified.K0 p K) ∧
        (∀ x : WeakAdmissibility.DcrisD.Dcris p K ρ.rho, D.frobenius.phi x = WeakAdmissibility.DcrisD.dCrisFrobenius p K ρ.rho x) ∧
        (∀ i : ℤ, D.filtration.step i = WeakAdmissibility.GeometricFiltration.scalarStep p K ρ.rho i) ∧
        Function.Injective (WeakAdmissibility.GeometricFiltration.scalarComparison p K ρ.rho) ∧
        D.tH = D.frobenius.tN (WeakAdmissibility.ValuationStructure.k0Valuation p K) ∧
        ∀ (S : Submodule (WeakAdmissibility.MaximalUnramified.K0 p K) (WeakAdmissibility.DcrisD.Dcris p K ρ.rho)) (hS : D.frobenius.Stable S),
          D.subobjectTH S ≤ D.frobenius.subobjectTN (WeakAdmissibility.ValuationStructure.k0Valuation p K) S hS

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibility
