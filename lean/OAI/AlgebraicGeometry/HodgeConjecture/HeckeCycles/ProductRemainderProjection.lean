import Mathlib

/-! # Product Remainder Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductRemainderProjection.CM

/-! In a homomorphic image of a direct product, removing the active
coordinate leaves an element commuting with every active element. -/

variable {A B P : Type*} [Group A] [Group B] [Group P]
  (s : A × B →* P)

theorem remainder (a : A) (b : B) : (s (a, 1))⁻¹ * s (a, b) = s (1, b) := by
  rw [← map_inv, ← map_mul]
  congr 1
  exact Prod.ext (inv_mul_cancel a) (by simp)

theorem commutes (a u : A) (b : B) : Commute ((s (a, 1))⁻¹ * s (a, b)) (s (u, 1)) := by
  rw [remainder]
  apply Commute.map _ s
  show (1, b) * (u, 1) = (u, 1) * (1, b)
  simp

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProductRemainderProjection.CM
