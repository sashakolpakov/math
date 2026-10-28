import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommutingFactorization
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductRemainderProjection

/-! # Projected Coordinate Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedCoordinateSplitting.CM

noncomputable section

/-! Projection of a commuting factorization is determined by its
active and rational restrictions, retaining the actual away range. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommutingFactorization.CM

variable {G A B M N : Type*} [Group G] [Group A] [Group B] [Group M] [Group N]
  (a : G →* A) (active : A →* M) (rho : G →* M)
  (hc : ∀ g u, Commute (CommutingFactorization.CM.remainder a active rho g) (active u)) (b : G →* B)
  (p : M →* N) (s : A × B →* N)

theorem projection (ha : ∀ u, p (active u) = s (u, 1))
    (hr : ∀ g, p (rho g) = s (a g, b g))
    (u : A) (v : CommutingFactorization.CM.AwayWithCoordinates a active rho hc b) :
    p (CommutingFactorization.CM.coordinateSplitting a active rho hc b (u, v)) = s (u, v.val.1) := by
  rcases v with ⟨v, g, rfl⟩
  change p (active u * ((active (a g))⁻¹ * rho g)) = s (u, b g)
  rw [map_mul, map_mul, map_inv, ha, ha, hr,
    ProductRemainderProjection.CM.remainder, ← map_mul]
  congr 1
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectedCoordinateSplitting.CM
