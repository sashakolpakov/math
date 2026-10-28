import OAI.AlgebraicGeometry.AbelianVariety.GeometricCup
import OAI.AlgebraicGeometry.AbelianVariety.HodgeAssembly

/-! # Exterior Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomology.CM

/-!
# ExteriorCohomology: the cup-normalized exterior cohomology of an abelian variety

The rational cup map is bijective in every degree. Actual simplex integration
identifies wedge and cup products, and invariant forms identify the geometric
pure Betti subspaces. These comparisons give the prescribed Hodge compatibility
for the original degree-one Hodge structure, without additional assumptions.
-/

/-- ExteriorCohomology: cup product identifies abelian-variety cohomology with
its rational exterior algebra, with every actual Hodge type preserved. -/
theorem abelian_exterior_cohomology
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
    (h_holomorphic : H.holomorphic = A.h1Holomorphic)
    (h_antiholomorphic : H.antiholomorphic = A.h1Antiholomorphic) :
    Nonempty (ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison A H) := by
  exact HodgeAssembly.Constructions.ExteriorCohomology.comparison_of_geometric_cup A
    (GeometricCup.Constructions.ExteriorCohomology.geometricBettiWedge_eq_cup A) H h_holomorphic h_antiholomorphic

end OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomology.CM
