import OAI.Analysis.PDE.Dirichlet.Boundary.Tangential

open scoped InnerProductSpace Matrix.Norms.Elementwise

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem hessian_norm_of_normal_components {n s : ℕ} {ψ : CoordinateSpace n s → ℝ}
    {x ν : CoordinateSpace n s} (hψ : ContDiffAt ℝ 2 ψ x) (hν : ‖ν‖ = 1)
    {T M C : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (ht : ∀ v w, ⟪ν, v⟫_ℝ = 0 → ⟪ν, w⟫_ℝ = 0 →
      |fderiv ℝ (fderiv ℝ ψ) x v w| ≤ T * ‖v‖ * ‖w‖)
    (hm : ∀ v, ⟪ν, v⟫_ℝ = 0 → |fderiv ℝ (fderiv ℝ ψ) x ν v| ≤ M * ‖v‖)
    (hn : |fderiv ℝ (fderiv ℝ ψ) x ν ν| ≤ C) :
    ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤
      (Fintype.card (Fin n × Fin s) : ℝ) ^ 2 * (4 * T + 4 * M + C) := by
  apply hessian_norm_le_of_entry_bound ψ x (by positivity)
  intro i j
  have hv : |ν i| ≤ 1 := by
    simpa only [inner_coordinateVector, hν, norm_coordinateVector, mul_one] using
      abs_real_inner_le_norm ν (coordinateVector i)
  have hw : |ν j| ≤ 1 := by
    simpa only [inner_coordinateVector, hν, norm_coordinateVector, mul_one] using
      abs_real_inner_le_norm ν (coordinateVector j)
  have hrem := normal_remainder_abs_bound (fderiv ℝ (fderiv ℝ ψ) x) hν
    (le_of_eq (norm_coordinateVector i)) (le_of_eq (norm_coordinateVector j))
    (hψ.isSymmSndFDerivAt (by norm_num)).eq hT hM ht hm
  simp only [inner_coordinateVector] at hrem
  have hprod : |fderiv ℝ (fderiv ℝ ψ) x ν ν * ν i * ν j| ≤ C := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (C * 1) * 1 := mul_le_mul (mul_le_mul hn hv (abs_nonneg _) hC) hw
        (abs_nonneg _) (mul_nonneg hC zero_le_one)
      _ = C := by ring
  calc
    |realHessian ψ x i j| = |(fderiv ℝ (fderiv ℝ ψ) x (coordinateVector i) (coordinateVector j) -
        fderiv ℝ (fderiv ℝ ψ) x ν ν * ν i * ν j) +
        fderiv ℝ (fderiv ℝ ψ) x ν ν * ν i * ν j| := by rw [sub_add_cancel]; rfl
    _ ≤ |fderiv ℝ (fderiv ℝ ψ) x (coordinateVector i) (coordinateVector j) -
        fderiv ℝ (fderiv ℝ ψ) x ν ν * ν i * ν j| +
        |fderiv ℝ (fderiv ℝ ψ) x ν ν * ν i * ν j| := abs_add_le _ _
    _ ≤ 4 * T + 4 * M + C := add_le_add hrem hprod

theorem full_hessian_bound_of_tangential_data (n : ℕ) (T M c F : ℝ)
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : CoordinateSpace (n + 1) 4 → ℝ)
      (x ν : CoordinateSpace (n + 1) 4),
      ContDiffAt ℝ 2 ψ x → ‖ν‖ = 1 →
      (∀ v w, ⟪ν, v⟫_ℝ = 0 → ⟪ν, w⟫_ℝ = 0 →
        |fderiv ℝ (fderiv ℝ ψ) x v w| ≤ T * ‖v‖ * ‖w‖) →
      (∀ v, ⟪ν, v⟫_ℝ = 0 → |fderiv ℝ (fderiv ℝ ψ) x ν v| ≤ M * ‖v‖) →
      (∀ z, quaternionPairing (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots ν) z = 0 →
        c * (quaternionForm 1 z).re ≤ (quaternionForm (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) z).re) →
      |OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)| ≤ F →
      ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ C := by
  obtain ⟨N, hN, hn⟩ := pure_normal_hessian_bound n T M c F hT hM hc
  let C := (Fintype.card (Fin (n + 1) × Fin 4) : ℝ) ^ 2 * (4 * T + 4 * M + N)
  refine ⟨C + 1, by dsimp [C]; positivity, ?_⟩
  intro ψ x ν hψ hν ht hm hq hdet
  exact (hessian_norm_of_normal_components hψ hν hT hM hN.le ht hm
    (hn ψ x ν hψ hν ht hm hq hdet)).trans (by dsimp [C]; linarith)

end OAI.Analysis.PDE.Dirichlet
