import Mathlib

/-! # Matrix Power Coordinates -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.MatrixPowerCoordinates.Realization

noncomputable section

/-! A nonexpanding action in finite-dimensional coordinates has bounded matrix powers. -/

open scoped Classical _root_.Matrix

theorem matrix_powers_bounded_of_coordinates
    {K I V : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Fintype I] [DecidableEq I] [NormedAddCommGroup V] [NormedSpace K V]
    (A : Matrix I I K) (F : (I → K) ≃ₗ[K] V)
    (hF : ∀ x : I → K, ‖F (A *ᵥ x)‖ ≤ ‖F x‖) :
    ∃ R : ℝ, ∀ (N : ℕ) i j, ‖(A ^ N) i j‖ ≤ R := by
  let : FiniteDimensional K V := F.finiteDimensional
  let C := F.toContinuousLinearEquiv
  have hp (N : ℕ) (x : I → K) : ‖F ((A ^ N) *ᵥ x)‖ ≤ ‖F x‖ := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec]
        exact (hF _).trans ih
  refine ⟨‖C.symm.toContinuousLinearMap‖ * ‖C.toContinuousLinearMap‖, ?_⟩
  intro N i j
  let x : I → K := Pi.single j 1
  have hx : ‖x‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    by_cases hk : k = j <;> simp [x, hk]
  have hc : ‖C ((A ^ N) *ᵥ x)‖ ≤ ‖C.toContinuousLinearMap‖ :=
    (hp N x).trans (C.toContinuousLinearMap.unit_le_opNorm x hx)
  calc
    ‖(A ^ N) i j‖ = ‖((A ^ N) *ᵥ x) i‖ := by simp [x, Matrix.mulVec_single]
    _ ≤ ‖(A ^ N) *ᵥ x‖ := norm_le_pi_norm _ _
    _ = ‖C.symm (C ((A ^ N) *ᵥ x))‖ := by rw [C.symm_apply_apply]
    _ ≤ ‖C.symm.toContinuousLinearMap‖ * ‖C ((A ^ N) *ᵥ x)‖ :=
      C.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (norm_nonneg _)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.MatrixPowerCoordinates.Realization
