import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodTorusProjective
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.TorusRealManifold

/-! # Period Torus Manifold Agreement -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodTorusManifoldAgreement.CM.Construction

noncomputable section

/-! Both constructions use the same quotient charts. The projective
period data therefore retain the actual manifold used by the period map. -/

variable {Index : Type} [Fintype Index] [DecidableEq Index] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (b : Module.Basis Index ℚ (V.rationalCohomology 1))
  (H : WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1))
  (hH : H.holomorphic = (V.pureBettiSubspace 1 0).comap
    (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1))
  (P : CM.Polarization.WeightOnePolarization H)

theorem rationalH1ProjectivePeriodData_chartedSpace :
    HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.ProjectivePeriodData.periodTorus_chartedSpace (PeriodTorusProjective.CM.Construction.rationalH1ProjectivePeriodData V b H hH P) =
      QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotient_chartedSpace (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodTorusManifoldAgreement.CM.Construction
