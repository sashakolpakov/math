import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Truncation

/-! Scale-uniform first derivative estimates for the far-field kernel. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem radialCutoff_fderiv_weighted_bound :
    ∃ C > 0, ∀ (r : ℝ), 0 < r → ∀ y : E, y ≠ 0 → ‖fderiv ℝ (radialCutoff r) y‖ ≤ C / ‖y‖ := by
  obtain ⟨C, hC, hbound⟩ := radialCutoff_fderiv_bound (E := E)
  refine ⟨2 * C, by positivity, ?_⟩
  intro r hr y hy
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  by_cases hh : ‖y‖ ≤ 2 * r
  · exact (hbound r hr y).trans ((div_le_div_iff₀ hr hn).mpr (by nlinarith))
  · rw [radialCutoff_fderiv_zero_outside hr (lt_of_not_ge hh), norm_zero]
    positivity

omit [MeasurableSpace E] [BorelSpace E] in
theorem truncatedNewtonianEntry_fderiv_bound (m : ℕ) (v w : E) :
    ∃ C > 0, ∀ (r : ℝ), 0 < r → ∀ y : E, y ≠ 0 →
      ‖fderiv ℝ (truncatedNewtonianEntry m v w r) y‖ ≤ C * ‖y‖ ^ (-(m : ℝ) - 1) := by
  obtain ⟨C, hC, hK⟩ := newtonianEntry_fderiv_decay m v w
  obtain ⟨B, hB, hcut⟩ := radialCutoff_fderiv_weighted_bound (E := E)
  let A : ℝ := newtonianSizeConstant m * ‖v‖ * ‖w‖
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (newtonianSizeConstant_nonneg m) (norm_nonneg _)) (norm_nonneg _)
  refine ⟨C + A * B, by positivity, ?_⟩
  intro r hr y hy
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hφ := (contDiff_radialCutoff (E := E) r).differentiable (by simp) y
  have h1φ : DifferentiableAt ℝ (fun z : E => 1 - radialCutoff r z) y := by
    simpa using! (differentiableAt_const (1 : ℝ)).sub hφ
  have hk := (contDiffAt_newtonianEntry m v w hy).differentiableAt (by simp)
  have hentry : ‖newtonianEntry m v w y‖ ≤ A * ‖y‖ ^ (-(m : ℝ)) := by
    have h := newtonianEntry_bound m hy v w
    simpa only [newtonianEntry, Real.norm_eq_abs, A, mul_assoc, mul_left_comm, mul_comm] using h
  have hφsize : ‖1 - radialCutoff r y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (radialCutoff_le_one r y))]
    linarith [radialCutoff_nonneg r y]
  change ‖fderiv ℝ (fun z => (1 - radialCutoff r z) * newtonianEntry m v w z) y‖ ≤ _
  rw [fderiv_fun_mul h1φ hk, fderiv_const_sub]
  calc
    _ ≤ ‖(1 - radialCutoff r y) • fderiv ℝ (newtonianEntry m v w) y‖ +
        ‖newtonianEntry m v w y • -fderiv ℝ (radialCutoff r) y‖ := norm_add_le _ _
    _ = ‖1 - radialCutoff r y‖ * ‖fderiv ℝ (newtonianEntry m v w) y‖ +
        ‖newtonianEntry m v w y‖ * ‖fderiv ℝ (radialCutoff r) y‖ := by rw [norm_smul, norm_smul, norm_neg]
    _ ≤ 1 * (C * ‖y‖ ^ (-(m : ℝ) - 1)) + (A * ‖y‖ ^ (-(m : ℝ))) * (B / ‖y‖) :=
      add_le_add (mul_le_mul hφsize (hK y hy) (norm_nonneg _) zero_le_one)
        (mul_le_mul hentry (hcut r hr y hy) (norm_nonneg _) (by positivity))
    _ = _ := by rw [Real.rpow_sub hn, Real.rpow_one]; ring

end OAI.Analysis.PDE.Schauder
