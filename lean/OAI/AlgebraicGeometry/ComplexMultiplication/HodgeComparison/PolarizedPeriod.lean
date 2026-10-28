import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizedPeriodDuality
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CanonicalHolomorphicCoordinates
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodLattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectiveTorusData

/-! # Polarized Period -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizedPeriod.CM.Construction

noncomputable section

/-! The generic polarized period torus agrees with the actual rational
H¹ period coordinates after choosing the polarization-dual rational basis. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (b : Module.Basis ι ℚ (V.rationalCohomology 1))
  (H : WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1))
  (hH : H.holomorphic = (V.pureBettiSubspace 1 0).comap
    (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1))
  (P : CM.Polarization.WeightOnePolarization H)

def polarizedPeriodComplexEquiv :
    HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.GenericPeriodSpace H ≃ₗ[ℂ] PeriodLattice.CM.Construction.RationalH1PeriodSpace V b :=
  (HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.periodComplexEquiv H).symm.trans
    ((PolarizedPeriodDuality.CM.Construction.polarizedHolomorphicDualEquiv P).trans
      ((CanonicalHolomorphicCoordinates.CM.Construction.canonicalHolomorphicCoordinateEquiv V b H hH).dualMap.trans
        (PeriodLattice.CM.Construction.rationalPeriodComplexEquiv V b)))

theorem polarizedPeriodComplexEquiv_basis (i : ι) :
    polarizedPeriodComplexEquiv V b H hH P
      (HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodBasis (PolarizedPeriodDuality.CM.Construction.polarizationDualRationalBasis P b) H i) =
      PeriodLattice.CM.Construction.rationalPeriodBasis V b i := by
  apply (PeriodLattice.CM.Construction.rationalPeriodComplexEquiv V b).symm.injective
  simp only [polarizedPeriodComplexEquiv, PeriodLattice.CM.Construction.rationalPeriodBasis, Module.Basis.map_apply,
    PeriodLattice.CM.Construction.rationalPeriodRealEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.symm_apply_apply]
  apply LinearMap.ext
  intro c
  change PolarizedPeriodDuality.CM.Construction.polarizedHolomorphicDualEquiv P
    ((HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.periodComplexEquiv H).symm
      (HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodBasis (PolarizedPeriodDuality.CM.Construction.polarizationDualRationalBasis P b) H i))
    (CanonicalHolomorphicCoordinates.CM.Construction.canonicalHolomorphicCoordinateEquiv V b H hH c) =
      PeriodCoordinateDuality.CM.Construction.realPeriodEvaluation (RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b) ((Pi.basisFun ℝ ι) i) c
  rw [PolarizedPeriodDuality.CM.Construction.polarizedHolomorphicDualEquiv_realVector, ← HodgeConjecture.CMVariety.PeriodSpace.CM.Abelian.periodRealEquiv_symm_coe,
    HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodBasis_realVector, PolarizedPeriodDuality.CM.Construction.polarizationDualRationalBasis_complex_pair,
    CanonicalHolomorphicCoordinates.CM.Construction.canonicalHolomorphicCoordinateEquiv_repr]
  simp [PeriodCoordinateDuality.CM.Construction.realPeriodEvaluation_apply, Pi.basisFun_apply, Pi.single_apply, apply_ite]

theorem polarizedPeriodComplexEquiv_lattice :
    (HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodLattice (PolarizedPeriodDuality.CM.Construction.polarizationDualRationalBasis P b) H).map
      ((polarizedPeriodComplexEquiv V b H hH P).restrictScalars ℤ).toLinearMap =
      PeriodLattice.CM.Construction.rationalPeriodLattice V b := by
  unfold HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodLattice PeriodLattice.CM.Construction.rationalPeriodLattice
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext i
  exact polarizedPeriodComplexEquiv_basis V b H hH P i

theorem polarizedPeriodComplexEquiv_symm_mem_lattice (v : PeriodLattice.CM.Construction.RationalH1PeriodSpace V b)
    (hv : v ∈ PeriodLattice.CM.Construction.rationalPeriodLattice V b) :
    (polarizedPeriodComplexEquiv V b H hH P).symm v ∈
      HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodLattice (PolarizedPeriodDuality.CM.Construction.polarizationDualRationalBasis P b) H := by
  have hm : v ∈ (HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodLattice (PolarizedPeriodDuality.CM.Construction.polarizationDualRationalBasis P b) H).map
      ((polarizedPeriodComplexEquiv V b H hH P).restrictScalars ℤ).toLinearMap := by
    rw [polarizedPeriodComplexEquiv_lattice]
    exact hv
  obtain ⟨u, hu, he⟩ := hm
  have hsymm : (polarizedPeriodComplexEquiv V b H hH P).symm v = u := by
    rw [← he]
    exact (polarizedPeriodComplexEquiv V b H hH P).symm_apply_apply u
  rw [hsymm]
  exact hu

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizedPeriod.CM.Construction
