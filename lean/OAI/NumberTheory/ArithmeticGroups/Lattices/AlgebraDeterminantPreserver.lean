import OAI.NumberTheory.ArithmeticGroups.Lattices.ScalarLinearPreserver

/-! # Algebra Determinant Preserver -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraDeterminantPreserver.Construction

noncomputable section

/-! A coefficient-algebra linear map preserves its determinant tensor
exactly when its representing matrix has determinant one. -/

open scoped Classical

theorem determinant_rows_specialLinear
    {S : Type*} [CommRing S] {n : ℕ}
    (g : Matrix.SpecialLinearGroup (Fin n) S) (v : Fin n → Fin n → S) :
    Matrix.det (Matrix.of (fun i => Matrix.SpecialLinearGroup.toLin' g (v i))) =
      Matrix.det (Matrix.of v) := by
  have he : Matrix.of (fun i => Matrix.SpecialLinearGroup.toLin' g (v i)) =
      Matrix.of v * (g : Matrix (Fin n) (Fin n) S).transpose := by
    ext i j : 1
    change (∑ l, g j l * v i l) = ∑ l, v i l * g j l
    apply Finset.sum_congr rfl
    intro l _
    exact mul_comm _ _
  rw [he, Matrix.det_mul, Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe, mul_one]

theorem specialLinear_exists_of_scalar_and_determinant_preserved
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}
    (f : (Fin n → S) ≃ₗ[R] (Fin n → S))
    (hscalar : ∀ (a : S) x, f (a • x) = a • f x)
    (hdet : ∀ v : Fin n → Fin n → S,
      Matrix.det (Matrix.of (fun i => f (v i))) = Matrix.det (Matrix.of v)) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) S,
      (Matrix.SpecialLinearGroup.toLin' g).restrictScalars R = f := by
  let F := ScalarLinearPreserver.Construction.scalarLinearEquivOfCommutes f hscalar
  let B := LinearMap.toMatrix' F.toLinearMap
  have hB : Matrix.of (fun i => f (Pi.basisFun S (Fin n) i)) = B.transpose := by
    ext i j : 1
    simp only [Matrix.of_apply, Matrix.transpose_apply, B, LinearMap.toMatrix'_apply,
      Pi.basisFun_apply]
    rfl
  have hI : Matrix.of (Pi.basisFun S (Fin n)) = 1 := by
    ext i j : 1
    simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
  have hd : B.det = 1 := by
    have hv := hdet (Pi.basisFun S (Fin n))
    rwa [hB, hI, Matrix.det_transpose, Matrix.det_one] at hv
  let g : Matrix.SpecialLinearGroup (Fin n) S := ⟨B, hd⟩
  refine ⟨g, ?_⟩
  have he : Matrix.SpecialLinearGroup.toLin' g = F := by
    apply LinearEquiv.toLinearMap_injective
    change Matrix.toLin' (LinearMap.toMatrix' F.toLinearMap) = F.toLinearMap
    exact Matrix.toLin'_toMatrix' _
  rw [he]
  exact ScalarLinearPreserver.Construction.scalarLinearEquivOfCommutes_restrictScalars f hscalar

theorem specialLinear_exists_iff_preserves_scalar_and_determinant
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}
    (f : (Fin n → S) ≃ₗ[R] (Fin n → S)) :
    (∃ g : Matrix.SpecialLinearGroup (Fin n) S,
      (Matrix.SpecialLinearGroup.toLin' g).restrictScalars R = f) ↔
    (∀ (a : S) x, f (a • x) = a • f x) ∧
    (∀ v : Fin n → Fin n → S,
      Matrix.det (Matrix.of (fun i => f (v i))) = Matrix.det (Matrix.of v)) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨fun a x => (Matrix.SpecialLinearGroup.toLin' g).map_smul a x,
      determinant_rows_specialLinear g⟩
  · rintro ⟨hs, hd⟩
    exact specialLinear_exists_of_scalar_and_determinant_preserved f hs hd

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraDeterminantPreserver.Construction
