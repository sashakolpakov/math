import OAI.AlgebraicGeometry.ComplexMultiplication.FieldProductComponents

/-! # Coordinate Sum -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CoordinateSum

noncomputable section

/-! # The internal direct sum of the actual field coordinates -/

open scoped DirectSum

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {n : ℕ} (K : Fin n → Type) [∀ i, Field (K i)] [∀ i, Algebra ℚ (K i)]
  (e : U ≃ₗ[ℚ] ((i : Fin n) → K i))

theorem cmCoordinateSubspace_eq_map (i : Fin n) :
    FieldProductComponents.cmCoordinateSubspace K e i =
      (LinearMap.range (LinearMap.single ℚ K i)).map e.symm.toLinearMap := by
  exact LinearMap.range_comp _ _

theorem cmCoordinateSubspaces_independent : iSupIndep (FieldProductComponents.cmCoordinateSubspace K e) := by
  have h : iSupIndep (fun i : Fin n => LinearMap.range (LinearMap.single ℚ K i)) := by
    intro i
    have hd : Disjoint ({i} : Set (Fin n)) {j | j ≠ i} := by
      simp
    simpa using LinearMap.disjoint_single_single ℚ K {i} {j | j ≠ i} hd
  simpa only [← cmCoordinateSubspace_eq_map] using
    LinearMap.iSupIndep_map e.symm.toLinearMap e.symm.injective h

theorem cmCoordinateSubspaces_span : (⨆ i, FieldProductComponents.cmCoordinateSubspace K e i) = ⊤ := by
  simp_rw [cmCoordinateSubspace_eq_map]
  rw [← Submodule.map_iSup, LinearMap.iSup_range_single, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.symm.surjective

theorem cmCoordinateSubspaces_internal : DirectSum.IsInternal (FieldProductComponents.cmCoordinateSubspace K e) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (cmCoordinateSubspaces_independent K e) (cmCoordinateSubspaces_span K e)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CoordinateSum
