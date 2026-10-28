import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferentialCoefficientIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferentialIdealPointSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Minimal.ModelSectionBaseChange

/-! # First Differential Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The first differential of a local minimal complex has a canonical coefficient ideal contained in the maximal ideal. Its universal quotient makes the actual differential split regularly; a residue-field factorization of that quotient identifies the ideal with the maximal ideal. -/
open _root_.CategoryTheory
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : ShortComplex (ModuleCat.{u} R)} (Q : Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex S)

def Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.firstDifferentialIdeal : Ideal R :=
  DifferentialCoefficientIdeal.differentialCoefficientIdeal (Module.Free.chooseBasis R Q.complex.X₁)
    (Module.Free.chooseBasis R Q.complex.X₂) Q.complex.f.hom

theorem Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.firstDifferentialIdeal_baseChange_zero_iff
    (B : Type u) [CommRing B] [Algebra R B] :
    Q.complex.f.hom.baseChange B = 0 ↔
      Q.firstDifferentialIdeal ≤ RingHom.ker (algebraMap R B) :=
  DifferentialCoefficientIdeal.differential_baseChange_zero_iff_coefficients _ _ _ B

theorem Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.firstDifferentialIdeal_le_maximalIdeal :
    Q.firstDifferentialIdeal ≤ IsLocalRing.maximalIdeal R := by
  have h := (Q.firstDifferentialIdeal_baseChange_zero_iff (IsLocalRing.ResidueField R)).mp
    Q.incoming_residue_zero
  simpa only [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue] using h

theorem Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.firstDifferential_quotient_zero :
    Q.complex.f.hom.baseChange (R ⧸ Q.firstDifferentialIdeal) = 0 :=
  DifferentialCoefficientIdeal.differential_coefficient_quotient_zero _ _ _

theorem Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.firstDifferential_quotient_generalizedInverse :
    ∃ r : (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (R ⧸ Q.firstDifferentialIdeal) S).X₂ →ₗ[R ⧸ Q.firstDifferentialIdeal]
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (R ⧸ Q.firstDifferentialIdeal) S).X₁,
      (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (R ⧸ Q.firstDifferentialIdeal) S).f.hom.comp
        (r.comp (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (R ⧸ Q.firstDifferentialIdeal) S).f.hom) =
          (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R (R ⧸ Q.firstDifferentialIdeal) S).f.hom :=
  Minimal.ModelSectionBaseChange.LocalSectionLifting.minimal_baseChange_first_generalizedInverse Q Q.firstDifferential_quotient_zero

theorem Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.firstDifferential_quotient_subsingleton
    [Nontrivial Q.complex.X₁] (p₀ : PrimeSpectrum R)
    (h : ∀ p : PrimeSpectrum R, p ≠ p₀ →
      Subsingleton (LinearMap.ker (HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeComplex R p.asIdeal.ResidueField S).f.hom)) :
    Subsingleton (PrimeSpectrum (R ⧸ Q.firstDifferentialIdeal)) := by
  let i : Module.Free.ChooseBasisIndex R Q.complex.X₁ := Classical.choice inferInstance
  apply DifferentialIdealPointSupport.differential_coefficient_quotient_subsingleton_of_residue_support
    (Module.Free.chooseBasis R Q.complex.X₁) (Module.Free.chooseBasis R Q.complex.X₂)
    Q.complex.f.hom i p₀
  intro p hp
  let e := Q.baseChangeFirstCyclesEquiv p.asIdeal.ResidueField
  exact ⟨fun x y => e.symm.injective ((h p hp).elim (e.symm x) (e.symm y))⟩

theorem Local.MinimalShortComplex.LocalSectionLifting.LocalMinimalShortComplex.firstDifferentialIdeal_eq_maximal_of_residue_factor
    (φ : IsLocalRing.ResidueField R →+* (R ⧸ Q.firstDifferentialIdeal))
    (hφ : φ.comp (IsLocalRing.residue R) = Ideal.Quotient.mk Q.firstDifferentialIdeal) :
    Q.firstDifferentialIdeal = IsLocalRing.maximalIdeal R := by
  apply le_antisymm Q.firstDifferentialIdeal_le_maximalIdeal
  intro r hr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hz : IsLocalRing.residue R r = 0 := (IsLocalRing.residue_eq_zero_iff r).mpr hr
  exact (congrArg (fun ψ : R →+* (R ⧸ Q.firstDifferentialIdeal) => ψ r) hφ).symm.trans
    ((congrArg φ hz).trans (map_zero φ))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
