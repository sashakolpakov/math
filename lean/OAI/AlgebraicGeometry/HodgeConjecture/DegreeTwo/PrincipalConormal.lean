import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Span.Basic

/-! # Principal Conormal -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrincipalConormal.Constructions

noncomputable section

/-!
# DegreeTwo: the actual coefficient functional of a principal conormal class

For a nonzero parameter, division by that parameter identifies its principal
ideal with the ambient domain. Reducing the coefficient modulo the ideal
annihilates its square and sends the parameter's conormal class to one.
-/

variable {R : Type*} [CommRing R] [IsDomain R] (p : R) (hp : p ≠ 0)

def principalIdealCoefficient : Ideal.span ({p} : Set R) →ₗ[R] R ⧸ Ideal.span ({p} : Set R) :=
  (Ideal.Quotient.mkₐ R (Ideal.span {p})).toLinearMap.comp
    (LinearEquiv.coord R R p hp).toLinearMap

theorem principalIdealCoefficient_self :
    principalIdealCoefficient p hp ⟨p, Ideal.subset_span (Set.mem_singleton p)⟩ = 1 := by
  change Ideal.Quotient.mk (Ideal.span {p})
    (LinearEquiv.coord R R p hp ⟨p, Ideal.subset_span (Set.mem_singleton p)⟩) = 1
  rw [LinearEquiv.coord_self, map_one]

theorem principalIdealCoefficient_mul (x y : Ideal.span ({p} : Set R)) :
    principalIdealCoefficient p hp (x * y) = 0 := by
  have hxy : x * y = (x : R) • y := rfl
  rw [hxy, map_smul]
  change Ideal.Quotient.mk (Ideal.span {p}) (x : R) * principalIdealCoefficient p hp y = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul]

/-- The actual conormal quotient has a coefficient map normalized on the
given regular parameter, independent of any analytic normal comparison. -/
def principalConormalCoefficient : (Ideal.span ({p} : Set R)).Cotangent →ₗ[R]
    R ⧸ Ideal.span ({p} : Set R) :=
  Ideal.Cotangent.lift (principalIdealCoefficient p hp) (principalIdealCoefficient_mul p hp)

theorem principalConormalCoefficient_self :
    principalConormalCoefficient p hp
      ((Ideal.span ({p} : Set R)).toCotangent ⟨p, Ideal.subset_span (Set.mem_singleton p)⟩) = 1 := by
  rw [principalConormalCoefficient, Ideal.Cotangent.lift_toCotangent, principalIdealCoefficient_self]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PrincipalConormal.Constructions
