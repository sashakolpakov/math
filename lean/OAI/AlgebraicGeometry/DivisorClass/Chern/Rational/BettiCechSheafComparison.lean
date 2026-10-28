import OAI.AlgebraicGeometry.DivisorClass.Chern.GammaSectionsComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiSheafComparison

/-! # Betti Cech Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiCechSheafComparison

noncomputable section

/-! The actual rational Betti-to-sheaf map expressed through the native Cech comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) [MetrizableSpace X] [StronglyLocallyContractibleSpace X]
  [LocallyPathConnectedSpace X]

def rationalBettiCechSheafIso (n : ℕ) :
    AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.obj (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X (n + 1)) ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) (n + 1)).obj
        (HolomorphicPeriod.rationalConstantAbelianSheaf X) := by
  let : MetricSpace X := metrizableSpaceMetric X
  exact AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapIso (AlgebraicTopology.Cohomology.Singular.ParacompactComparison.paracompactSingularCohomologySheafSectionsIso ℚ X (n + 1)) ≪≫
    AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSectionsForgetHomologyIso ⊤ (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) (n + 1) ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{0} (.up ℕ) (n + 1)).mapIso
      (GammaSectionsComparison.abelianGammaSectionsIso (BettiSheafComparison.rationalAbelianSingularResolution X)).symm ≪≫
    GammaSectionsComparison.nativeFlasqueCohomologyIsoOfZero (BettiSheafComparison.rationalAbelianSingularResolution X)
      (BettiSheafComparison.rationalAbelianSingularResolution_flasque X) (BettiSheafComparison.rationalAbelianSingularResolution_exact X)
      n (BettiSheafComparison.rationalConstantAbelianZeroIso X)

def rationalBettiCechSheafEquiv (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X (n + 1) ≃+
      CategoryTheory.Sheaf.H (HolomorphicPeriod.rationalConstantAbelianSheaf X) (n + 1) :=
  (rationalBettiCechSheafIso X n).addCommGroupIsoToAddEquiv

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiCechSheafComparison
