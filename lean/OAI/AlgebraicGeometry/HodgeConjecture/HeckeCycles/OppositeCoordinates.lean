import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource

/-! # Opposite Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OppositeCoordinates.CM

noncomputable section

/-! An auxiliary opposite polarization of the source's actual vector
space. Negating the multiplicity coefficient and exchanging the two
rational blocks preserves the exact trace-coordinate identity. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def coordinates : GeometricSource.CM.SymplecticCoordinates E B places where
  a := -C.a
  a_ne_zero := neg_ne_zero.mpr C.a_ne_zero
  a_real := by rw [map_neg, C.a_real]
  delta := C.delta
  delta_ne_zero := C.delta_ne_zero
  delta_imaginary := C.delta_imaginary
  rational := C.rational.trans (LinearEquiv.prodComm ℚ _ _)
  complex := C.complex.trans (LinearEquiv.prodComm ℂ _ _)
  extends_rational := by
    intro x
    change Prod.swap (C.complex (GeometricSource.CM.embeddingCoordinates E x)) = _
    rw [C.extends_rational]
    rfl
  symplectic := by
    intro x y
    have ha : C.delta * -C.a * GeometricSource.CM.hermitian E B.b x y = -(C.delta * C.a * GeometricSource.CM.hermitian E B.b x y) := by ring
    rw [ha, map_neg, C.symplectic, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change -((C.rational x).1 i * (C.rational y).2 i - (C.rational y).1 i * (C.rational x).2 i) =
      (C.rational x).2 i * (C.rational y).1 i - (C.rational y).2 i * (C.rational x).1 i
    ring

theorem coefficient : (coordinates E C).a = -C.a := rfl

theorem rational (x : GeometricSource.CM.Vec E) : (coordinates E C).rational x = ((C.rational x).2, (C.rational x).1) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OppositeCoordinates.CM
