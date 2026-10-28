import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizedPeriod
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectiveTorusData

/-! # Period Torus Projective -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodTorusProjective.CM.Construction

noncomputable section

/-! The actual rational H¹ period torus is projective: its Hermitian
form and integer periods are transported through the exact lattice isomorphism. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (b : Module.Basis ι ℚ (V.rationalCohomology 1))
  (H : WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1))
  (hH : H.holomorphic = (V.pureBettiSubspace 1 0).comap
    (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1))
  (P : CM.Polarization.WeightOnePolarization H)

include H hH P in
theorem rationalPeriodTorus_projective_of_polarization :
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.IsProjectiveComplexTorus (PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup := by
  let b' := PolarizedPeriodDuality.CM.Construction.polarizationDualRationalBasis P b
  obtain ⟨P', hint⟩ := HodgeConjecture.CMVariety.IntegralLattice.CM.Abelian.exists_integral_polarization P b'
  let L := PolarizedPeriod.CM.Construction.polarizedPeriodComplexEquiv V b H hH P
  let G : PeriodLattice.CM.Construction.RationalH1PeriodSpace V b →ₗ⋆[ℂ] PeriodLattice.CM.Construction.RationalH1PeriodSpace V b →ₗ[ℂ] ℂ :=
    ((HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodHermitian P').comp L.symm.toLinearMap).compl₂ L.symm.toLinearMap
  apply (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion (PeriodLattice.CM.Construction.RationalH1PeriodSpace V b)
    (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup).mpr
  refine ⟨G, ?_, ?_, ?_⟩
  · intro u v
    exact HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodHermitian_symm P' (L.symm u) (L.symm v)
  · intro u hu
    apply HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodHermitian_positive P' (L.symm u)
    intro hz
    apply hu
    have h := congrArg L hz
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using h
  · intro u hu v hv
    exact HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.genericPeriodHermitian_integral b' P' hint (L.symm u)
      (PolarizedPeriod.CM.Construction.polarizedPeriodComplexEquiv_symm_mem_lattice V b H hH P u hu) (L.symm v)
      (PolarizedPeriod.CM.Construction.polarizedPeriodComplexEquiv_symm_mem_lattice V b H hH P v hv)

def rationalH1ProjectivePeriodData : HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.ProjectivePeriodData where
  space := PeriodLattice.CM.Construction.RationalH1PeriodSpace V b
  periodIntegerLattice := PeriodLattice.CM.Construction.rationalPeriodLattice V b
  projective := rationalPeriodTorus_projective_of_polarization V b H hH P

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodTorusProjective.CM.Construction
