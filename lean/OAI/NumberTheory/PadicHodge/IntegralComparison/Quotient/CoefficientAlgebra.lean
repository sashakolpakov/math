import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Tower

/-! # Coefficient Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientAlgebra

noncomputable section

/-! The actual coefficient algebra inherits the normal quotient action
from the literal vanishing of the normal ideal in the intermediate ring. -/
universe u
variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  (I : Ideal A) (hI : I ≤ RingHom.ker (algebraMap A B))

def map : (A ⧸ I) →ₐ[A] C := Ideal.Quotient.liftₐ I (Algebra.ofId A C) (by
  intro x hx
  change algebraMap A C x = 0
  rw [IsScalarTower.algebraMap_apply A B C]
  rw [show algebraMap A B x = 0 from hI hx, map_zero])

@[instance_reducible]
def algebra : Algebra (A ⧸ I) C := (map A B C I hI).toRingHom.toAlgebra

theorem tower : letI := algebra A B C I hI; IsScalarTower A (A ⧸ I) C := by
  let := algebra A B C I hI
  exact IsScalarTower.of_algebraMap_eq' (map A B C I hI).comp_algebraMap.symm

theorem algebraMap_mk (x : A) : letI := algebra A B C I hI
    algebraMap (A ⧸ I) C (Ideal.Quotient.mk I x) = algebraMap A C x := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientAlgebra
