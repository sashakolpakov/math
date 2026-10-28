import OAI.RepresentationTheory.Hecke.RadialDilation.MatrixPowerCoordinates
import OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates

/-! # Split Scalar Power Bounds -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarPowerBounds.Realization

noncomputable section

/-! Unit conjugates imply bounded powers of the actual rational scalar matrix after base change. -/

open scoped Classical _root_.Matrix

variable (E K : Type*) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
  [NontriviallyNormedField K] [CompleteSpace K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]

omit [IsGalois ℚ E] [CompleteSpace K] [Algebra E K] [IsScalarTower ℚ E K] in
theorem splitScalarEnd_norm_le (r : E) (hr : ∀ σ : E →ₐ[ℚ] K, ‖σ r‖ ≤ 1)
    (x : (E →ₐ[ℚ] K) → Fin 3 → K) : ‖SplitScalarCoordinates.Realization.splitScalarEnd E K r x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro σ
  change ‖σ r • x σ‖ ≤ ‖x‖
  rw [norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hr σ)).trans (norm_le_pi_norm x σ)

theorem rational_scalar_split_power_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (e : (Fin 3 → E) ≃ₗ[ℚ] (I → ℚ)) (r : E)
    (hr : ∀ σ : E →ₐ[ℚ] K, ‖σ r‖ ≤ 1) :
    ∃ R : ℝ, ∀ (N : ℕ) i j,
      ‖((RationalCoordinates.Realization.rationalScalarMatrix E e r).map (algebraMap ℚ K) ^ N) i j‖ ≤ R := by
  apply MatrixPowerCoordinates.Realization.matrix_powers_bounded_of_coordinates _ (SplitScalarCoordinates.Realization.splitRationalCoordinates E K e).symm
  intro x
  obtain ⟨y, rfl⟩ := (SplitScalarCoordinates.Realization.splitRationalCoordinates E K e).surjective x
  rw [← SplitScalarCoordinates.Realization.rational_matrix_realizes_split_scalar, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]
  exact splitScalarEnd_norm_le E K r hr y

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarPowerBounds.Realization
