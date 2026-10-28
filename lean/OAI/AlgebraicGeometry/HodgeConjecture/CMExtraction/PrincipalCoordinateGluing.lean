import Mathlib.Logic.Function.Basic

/-! # Principal Coordinate Gluing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalCoordinateGluing.TestTransport

/-! The three principal-level conditions split into their common
away conditions and the single local preservation condition. -/

theorem principal_coordinate_conditions {J : Type*}
    (P Q R A B C : J → Prop)
    (hB : (∀ j, A j) → ∀ j, B j) (hC : (∀ j, A j) → ∀ j, C j) :
    ((∀ j, P j ∧ A j) ∧ (∀ j, Q j ∧ B j) ∧ ∀ j, R j ∧ C j) ↔
      ((∀ j, P j) ∧ (∀ j, Q j) ∧ ∀ j, R j) ∧ ∀ j, A j := by
  constructor
  · rintro ⟨hP, hQ, hR⟩
    exact ⟨⟨fun j => (hP j).1, fun j => (hQ j).1, fun j => (hR j).1⟩,
      fun j => (hP j).2⟩
  · rintro ⟨⟨hP, hQ, hR⟩, hA⟩
    exact ⟨fun j => ⟨hP j, hA j⟩, fun j => ⟨hQ j, hB hA j⟩,
      fun j => ⟨hR j, hC hA j⟩⟩

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalCoordinateGluing.TestTransport
