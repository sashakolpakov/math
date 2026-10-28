import OAI.Algebra.Modules.ElementaryDivisors
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality

/-! # Lattices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Lattices.Intrinsic

/-! Supply the lattice input from the proved ElementaryDivisors theorem. -/

theorem verifiedElementaryDivisors
    (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput R K := by
  intro n π hπ L M hL hM
  let : Submodule.IsLattice K L := hL
  let : Submodule.IsLattice K M := hM
  exact OAI.Algebra.Modules.ElementaryDivisors.lattices_elementary_divisors π hπ L M

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Lattices.Intrinsic
