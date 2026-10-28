import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntegralSheafCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularCoefficientHomeomorphism
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HolomorphicChernComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Additive
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero

/-! # Integral Chern Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralChernVanishing

noncomputable section

/-! A homogeneous algebraic line bundle on the original native abelian
variety has zero integral exponential obstruction, and its holomorphic
class is the exponential of an actual holomorphic H¹ class. -/

open _root_.CategoryTheory _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Additive

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)

theorem nativeRationalModuloH1_surjective :
    Function.Surjective (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap TorusIntegralInjection.rationalModuloCoefficient (TopCat.of A.variety.analyticSpace) 1) := by
  let : Module.Free ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :=
    Module.Free.of_basis (Torsion.IntrinsicTorsion.periodBasis A)
  exact SingularCoefficientHomeomorphism.singular_coefficient_surjective_of_homeomorph TorusIntegralInjection.rationalModuloCoefficient
    (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph Torsion.IntrinsicTorsion.e06Input A) 1
    (SingularCoefficientLift.singularH1_coefficient_surjective TorusIntegralInjection.rationalModuloCoefficient TorusIntegralInjection.rationalModuloCoefficient_surjective
      (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A))

theorem nativeIntegralRationalSheaf_injective :
    Function.Injective (DivisorClass.Chern.Rational.HolomorphicPeriod.integralToRationalSheafCohomology A.variety.analyticSpace) := by
  let := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  let := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.locallyPathConnectedSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  exact IntegralSheafCoefficients.originalIntegralSheafH2_injective_of_singularModuloLift (TopCat.of A.variety.analyticSpace)
    (nativeRationalModuloH1_surjective A)

local instance nativeIntegralCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Holomorphic.Connecting.integralSheafCohomologyTwo A.variety.analyticSpace) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of A.variety.analyticSpace)
    (DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of A.variety.analyticSpace)) 2

local instance nativeRationalCohomologyGroup :
    AddCommGroup (DivisorClass.Chern.Rational.HolomorphicPeriod.rationalSheafCohomologyTwo A.variety.analyticSpace) :=
  Cech.Add.cechClassAddCommGroup (X := TopCat.of A.variety.analyticSpace)
    (DivisorClass.Chern.Rational.HolomorphicPeriod.rationalConstantAbelianSheaf (TopCat.of A.variety.analyticSpace)) 2

theorem homogeneousLineBundle_integralConnecting_eq_zero
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting A.variety.analyticModel A.variety.analyticSpace
      (HolomorphicLineClass.nativeHolomorphicLineClass A.variety L) = 0 := by
  let := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  let := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.locallyPathConnectedSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  have hc := DivisorClass.Chern.Holomorphic.Additive.holomorphicFirstChernClassQ_connecting A.variety.analyticModel A.variety.analyticSpace
    (HolomorphicLineClass.nativeHolomorphicLineClass A.variety L)
  have hq := congrArg (DivisorClass.Chern.Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of A.variety.analyticSpace) 1)
    (HolomorphicChernComparison.homogeneousLineBundle_holomorphicChern_eq_zero A L hL)
  have hz := hc.symm.trans (hq.trans
    (map_zero (DivisorClass.Chern.Rational.BettiCechSheafComparison.rationalBettiCechSheafIso (TopCat.of A.variety.analyticSpace) 1).hom.hom))
  apply nativeIntegralRationalSheaf_injective A
  exact hz.trans (map_zero (DivisorClass.Chern.Rational.HolomorphicPeriod.integralToRationalSheafCohomology A.variety.analyticSpace)).symm

theorem homogeneousLineBundle_holomorphicH1_lift
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (hL : HomogeneousLinePowers.IsHomogeneousLineClass (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety A) (HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    ∃ v : Sheaf.H (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf A.variety.analyticModel A.variety.analyticSpace) 1,
      RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.holomorphicExponentialH1 A.variety.analyticModel A.variety.analyticSpace v =
        HolomorphicLineClass.nativeHolomorphicLineClass A.variety L :=
  RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero.exists_holomorphicH1_of_connecting_zero A.variety.analyticModel A.variety.analyticSpace
    (HolomorphicLineClass.nativeHolomorphicLineClass A.variety L) (homogeneousLineBundle_integralConnecting_eq_zero A L hL)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralChernVanishing
