import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryDivisors
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Duality

/-! # Elementary Divisors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ElementaryDivisors.CM

/-! Retain the complete four-clause ElementaryDivisors prerequisite at the final
endpoint and derive its local lattice clause for the Hecke construction. -/

theorem lattices (hElementaryDivisors : AbelianScheme.IsogenyQuotient.ElementaryDivisors.Construction.ElementaryDivisorsInput.{0})
    (q : ℕ) [Fact q.Prime] : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q] := by
  intro n π hπ L M hL hM
  let : Submodule.IsLattice ℚ_[q] L := hL
  let : Submodule.IsLattice ℚ_[q] M := hM
  exact (hElementaryDivisors (R := ℤ_[q]) (K := ℚ_[q])).1 π hπ L M

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ElementaryDivisors.CM
