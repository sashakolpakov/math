import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.FlasqueResolution
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HolomorphicPeriod
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SheafZeroIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafZeroResolution
import OAI.AlgebraicTopology.Cohomology.Singular.SheafFlasque
import OAI.AlgebraicTopology.Cohomology.Singular.ParacompactComparison
import OAI.AlgebraicTopology.DeRham.Comparison.RationalSheafForget

/-! # Betti Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiSheafComparison

noncomputable section

/-! The actual rational singular cohomology compared with ordinary locally constant sheaf cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.RationalSheafForget OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0})

abbrev rationalAbelianSingularResolution := AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X)

def rationalConstantAbelianZeroIso [LocallyPathConnectedSpace X] :
    HolomorphicPeriod.rationalConstantAbelianSheaf X ≅ (rationalAbelianSingularResolution X).homology 0 :=
  (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget X).mapIso (SheafZeroIso.RationalCech.locallyConstantRationalSheafZeroIso X) ≪≫
    (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetHomologyIso (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) 0).symm

theorem rationalAbelianSingularResolution_flasque [MetrizableSpace X] (n : ℕ) :
    TopCat.Sheaf.IsFlasque ((rationalAbelianSingularResolution X).X n) := by
  have := AlgebraicTopology.Cohomology.Singular.SheafFlasque.sheafifiedSingularCochains_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ) X n
  exact AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForget_isFlasque ((HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X).X n)

theorem rationalAbelianSingularResolution_exact [StronglyLocallyContractibleSpace X] (n : ℕ) :
    (rationalAbelianSingularResolution X).ExactAt (n + 1) :=
  (AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSheafForgetComplex_exactAt_iff (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) (n + 1)).mpr
    (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheaf_positive_exact X n)

/-- The equivalence uses the actual singular sheafification map and an actual flasque-resolution lift. -/
def rationalBettiSheafCohomologyEquiv [MetrizableSpace X] [StronglyLocallyContractibleSpace X]
    [LocallyPathConnectedSpace X] (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X (n + 1) ≃+
      CategoryTheory.Sheaf.H (HolomorphicPeriod.rationalConstantAbelianSheaf X) (n + 1) := by
  let : MetricSpace X := metrizableSpaceMetric X
  exact ((AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget.mapIso (AlgebraicTopology.Cohomology.Singular.ParacompactComparison.paracompactSingularCohomologySheafSectionsIso ℚ X (n + 1))) ≪≫
    AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalSectionsForgetHomologyIso ⊤ (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X) (n + 1)).addCommGroupIsoToAddEquiv.trans
    (Abelian.FlasqueResolution.abelianFlasqueResolutionCohomologyEquivOfIso (rationalAbelianSingularResolution X)
      (rationalAbelianSingularResolution_flasque X) (rationalAbelianSingularResolution_exact X)
      n (rationalConstantAbelianZeroIso X))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiSheafComparison
