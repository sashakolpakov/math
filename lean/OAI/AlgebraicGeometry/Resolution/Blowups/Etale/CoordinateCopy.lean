import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Algebra.Algebra.Equiv

/-! # Coordinate Copy -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateCopy.Construction

noncomputable section

/-! Keep two coordinate algebra structures separate without changing the ambient ring. -/

universe u

variable {k P R : Type u} [CommRing k] [CommRing P] [CommRing R]
  [Algebra k P] [Algebra k R]

/-- Any specified étale coordinate map can be placed on an isomorphic copy of
the ambient ring. This keeps it distinct from a second coordinate algebra
structure on the original ring. -/
theorem exists_isomorphic_etale_coordinate_copy (β : P →ₐ[k] R) (hβ : β.toRingHom.Etale) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra P S),
      IsScalarTower k P S ∧ Algebra.Etale P S ∧
      ∃ e : R ≃ₐ[k] S, ∀ p : P, algebraMap P S p = e (β p) := by
  let : Algebra P R := β.toRingHom.toAlgebra
  let : Algebra.Etale P R := hβ
  let : IsScalarTower k P R := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap k R a = β (algebraMap k P a)
    exact (β.commutes a).symm)
  let S := ULift.{0} R
  let e : R ≃ₐ[k] S := ULift.algEquiv.symm
  let eP : R ≃ₐ[P] S := ULift.algEquiv.symm
  have hS : Algebra.Etale P S := Algebra.Etale.of_equiv eP
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, hS, e, ?_⟩
  intro p
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateCopy.Construction
