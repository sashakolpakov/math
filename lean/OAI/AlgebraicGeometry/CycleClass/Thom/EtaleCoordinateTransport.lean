import Mathlib.RingTheory.Etale.StandardEtale

/-! # Etale Coordinate Transport -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateTransport.Constructions

noncomputable section

/-! Transfer actual etale polynomial-coordinate algebra structures
across an equivalence which preserves the original coefficient algebra. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k P A B : Type*} [CommRing k] [CommRing P] [CommRing A] [CommRing B]
  [Algebra k P] [Algebra k A] [Algebra k B] [Algebra P A] [IsScalarTower k P A]

@[instance_reducible]
def coordinateAlgebra (e : A ≃ₐ[k] B) : Algebra P B :=
  (e.toRingHom.comp (algebraMap P A)).toAlgebra

def coordinateEquiv (e : A ≃ₐ[k] B) :
    letI := coordinateAlgebra (P := P) e
    A ≃ₐ[P] B := by
  letI := coordinateAlgebra (P := P) e
  exact { e.toRingEquiv with commutes' := fun _ => rfl }

theorem coordinateTower (e : A ≃ₐ[k] B) :
    letI := coordinateAlgebra (P := P) e
    IsScalarTower k P B := by
  let := coordinateAlgebra (P := P) e
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap k B r = e (algebraMap P A (algebraMap k P r))
  rw [← IsScalarTower.algebraMap_apply k P A, e.commutes]

theorem exists_standardEtale_coordinates (e : A ≃ₐ[k] B) [Algebra.IsStandardEtale P A] :
    ∃ a : Algebra P B, letI := a
      IsScalarTower k P B ∧ Algebra.IsStandardEtale P B := by
  refine ⟨coordinateAlgebra (P := P) e, ?_⟩
  let := coordinateAlgebra (P := P) e
  exact ⟨coordinateTower (P := P) e, Algebra.IsStandardEtale.of_equiv (coordinateEquiv (P := P) e)⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateTransport.Constructions
