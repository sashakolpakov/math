import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommutingFactorization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductRemainderProjection

/-! # Projected Commuting Remainder -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedCommutingRemainder.CM

/-! Identify the commuting remainder through exact active and rational
projection formulas, with no assumption about its lift to the cover. -/

variable {G A B M P : Type*} [Group G] [Group A] [Group B] [Group M] [Group P]
  (a : G →* A) (active : A →* M) (rho : G →* M) (p : M →* P)
  (s : A × B →* P) (b : G → B)
  (ha : ∀ u, p (active u) = s (u, 1))
  (hr : ∀ g, p (rho g) = s (a g, b g))

include ha hr in
theorem commutes (g : G) (u : A) :
    Commute (p (CommutingFactorization.CM.remainder a active rho g)) (p (active u)) := by
  change Commute (p ((active (a g))⁻¹ * rho g)) (p (active u))
  rw [map_mul, map_inv, ha, hr, ha]
  exact ProductRemainderProjection.CM.commutes s (a g) u (b g)

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedCommutingRemainder.CM
