import OAI.Analysis.Calculus.Current.Wave

/-! Phase-independent Gaussian amplitude bounds for the actual wave current. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open scoped Matrix Matrix.Norms.Elementwise

theorem complexK_norm (z : ℂ) : ‖complexK z‖ = ‖z‖ := by
  have hsq : Quaternion.normSq (complexK z) = Complex.normSq z := by
    simp [Quaternion.normSq_def', complexK, Complex.normSq_apply, pow_two]
  rw [Quaternion.normSq_eq_norm_mul_self, Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (complexK z), norm_nonneg z]

theorem movingEmbed_norm (e c : ℂ) (he : Complex.normSq e = 1) :
    ‖movingEmbed e c‖ = ‖c‖ := by
  have hsq : Quaternion.normSq (movingEmbed e c) = Complex.normSq c := by
    have he' : complexK e = ⟨e.re, 0, 0, e.im⟩ := rfl
    simp [Quaternion.normSq_def', movingEmbed, he', qi]
    simp only [Complex.normSq_apply] at he ⊢
    nlinarith [sq_nonneg c.im, congrArg (fun t : ℝ => t * c.im ^ 2) he]
  rw [Quaternion.normSq_eq_norm_mul_self, Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (movingEmbed e c), norm_nonneg c]

theorem phaseComplex_norm {d : ℕ} (cR cI : ℝ) (L x : Index d → ℝ) :
    ‖phaseComplex cR cI L x‖ = ‖(⟨cR, cI⟩ : ℂ)‖ := by
  have hsq : Complex.normSq (phaseComplex cR cI L x) = Complex.normSq (⟨cR, cI⟩ : ℂ) := by
    simp only [Complex.normSq_apply, phaseComplex, phaseF, phaseG]
    nlinarith [Real.sin_sq_add_cos_sq (phaseArgument L x),
      congrArg (fun t : ℝ => t * cR ^ 2) (Real.sin_sq_add_cos_sq (phaseArgument L x)),
      congrArg (fun t : ℝ => t * cI ^ 2) (Real.sin_sq_add_cos_sq (phaseArgument L x))]
  simp only [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (phaseComplex cR cI L x), norm_nonneg (⟨cR, cI⟩ : ℂ)]

theorem normalizedModeAmplitude_norm {d : ℕ} (κ cR cI : ℝ) (hκ : 0 < κ)
    (v : Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    ‖normalizedModeAmplitude κ cR cI v x z‖ =
      ((κ / ‖z none‖) ^ ((d : ℝ) / 2) *
        Real.exp (-κ * ‖z none‖ / 2 * squaredDistance (ratio z) v)) * ‖(⟨cR, cI⟩ : ℂ)‖ := by
  rw [normalizedModeAmplitude_formula κ cR cI hκ v x z hY,
    movingEmbed_norm _ _ (movingUnit_normSq z hY), norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), phaseComplex_norm]

theorem normalizedModeAmplitude_norm_le {d : ℕ} (κ cR cI : ℝ) (hκ : 0 < κ)
    (v : Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    ‖normalizedModeAmplitude κ cR cI v x z‖ ≤
      (κ / ‖z none‖) ^ ((d : ℝ) / 2) * ‖(⟨cR, cI⟩ : ℂ)‖ := by
  rw [normalizedModeAmplitude_norm κ cR cI hκ v x z hY]
  have hdist : 0 ≤ squaredDistance (ratio z) v := by
    unfold squaredDistance
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have he : Real.exp (-κ * ‖z none‖ / 2 * squaredDistance (ratio z) v) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hp : 0 ≤ κ * ‖z none‖ / 2 * squaredDistance (ratio z) v := by positivity
    nlinarith
  calc
    _ ≤ ((κ / ‖z none‖) ^ ((d : ℝ) / 2) * 1) * ‖(⟨cR, cI⟩ : ℂ)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (norm_nonneg _)
    _ = _ := by ring

end OAI.Analysis.Calculus.Current
