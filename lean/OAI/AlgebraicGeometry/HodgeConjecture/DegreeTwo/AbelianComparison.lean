import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod

/-! # Abelian Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions

noncomputable section

/-!
# DegreeTwo: the lattice-dual comparison for actual abelian varieties

The native uniformization and the proved singular period equivalence combine
to identify the abelian variety's actual rational H¹ with its rational period
lattice dual. The comparison does not assume an H¹ identification.
-/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LatticePeriod.Constructions.LatticeDual

/-- The actual rational H¹ of the native abelian variety is the dual of
the rational span of its constructed period lattice. -/
def rationalH1Equiv (hHolomorphicAlgebraicity : Transport.Constructions.HolomorphicAlgebraicityInput) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    A.variety.rationalCohomology 1 ≃ₗ[ℚ]
      Module.Dual ℚ (LatticePeriod.Constructions.LatticeDual.RationalSpan (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)) :=
  (AlgebraicTopology.Cohomology.Singular.Homotopy.singularCohomologyIsoOfHomotopyEquiv (ModuleCat.of ℚ ℚ)
      (AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph hHolomorphicAlgebraicity A).toHomotopyEquiv 1).toLinearEquiv.trans
    (LatticePeriod.Constructions.LatticeDual.singularH1LatticeDualEquiv (AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianComparison.Constructions
