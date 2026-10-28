import OAI.Analysis.Calculus.Current.BoundaryGaussian

/-! Dimension-explicit size estimates for finite positive-frequency currents. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

theorem tangentVector_norm_le {d : ℕ} (v W : Fin d → ℂ)
    (hv : ∀ i, ‖v i‖ ≤ 1) (hW : ∀ i, ‖W i‖ ≤ 1) :
    ‖tangentVector v W‖ ≤ (d : ℝ) + 1 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  cases a with
  | none => simp [tangentVector]
  | some a =>
    cases a with
    | none =>
      have hs : ‖∑ i, W i * v i‖ ≤ d := by
        calc
          _ ≤ ∑ i, ‖W i * v i‖ := norm_sum_le _ _
          _ ≤ ∑ i : Fin d, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            rw [norm_mul]
            exact (mul_le_mul (hW i) (hv i) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
          _ = _ := by simp
      simp only [tangentVector, norm_div, norm_neg]
      norm_num
      linarith [Nat.cast_nonneg (α := ℝ) d]
    | some i =>
      calc
        _ = ‖v i + W i‖ / 2 := by simp [tangentVector]
        _ ≤ (‖v i‖ + ‖W i‖) / 2 := div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
        _ ≤ (d : ℝ) + 1 := by linarith [hv i, hW i, Nat.cast_nonneg (α := ℝ) d]

theorem normalizedModeAmplitude_norm_le_parameters {d : ℕ}
    (κ cR cI R C L : ℝ) (hκ : 0 < κ) (v : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0)
    (hR : κ / ‖z none‖ ≤ R) (hC : ‖(⟨cR, cI⟩ : ℂ)‖ ≤ C)
    (hL : L ≤ κ * ‖z none‖ / 2 * squaredDistance (ratio z) v) :
    ‖normalizedModeAmplitude κ cR cI v x z‖ ≤
      (R ^ ((d : ℝ) / 2) * Real.exp (-L)) * C := by
  rw [normalizedModeAmplitude_norm κ cR cI hκ v x z hY]
  have hr : 0 ≤ κ / ‖z none‖ := by positivity
  have hRp : (κ / ‖z none‖) ^ ((d : ℝ) / 2) ≤ R ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow hr hR (by positivity)
  have he : Real.exp (-κ * ‖z none‖ / 2 * squaredDistance (ratio z) v) ≤ Real.exp (-L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact mul_le_mul (mul_le_mul hRp he (Real.exp_pos _).le
    (Real.rpow_nonneg (hr.trans hR) _)) hC (norm_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (hr.trans hR) _) (Real.exp_pos _).le)

theorem currentMatrix_norm_le_uniform {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (a : ι → OAI.Analysis.Calculus.Quaternion.Q)
    (B M : ℝ) (hB : 0 ≤ B) (_ : 0 ≤ M)
    (hv : ∀ j, ‖tangentVector (v j) W‖ ≤ B) (ha : ∀ j, ‖a j‖ ≤ M) :
    ‖currentMatrix W v a‖ ≤ ((Fintype.card ι : ℝ) * B * M) ^ 2 := by
  apply (currentMatrix_norm_le W v a).trans
  apply pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    (∑ j, ‖tangentVector (v j) W‖ * ‖a j‖) ≤ ∑ j : ι, B * M :=
      Finset.sum_le_sum fun j _ => mul_le_mul (hv j) (ha j) (norm_nonneg _) hB
    _ = _ := by simp [mul_assoc]

theorem waveCurrent_norm_le_parameters {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (R C L : ℝ)
    (hκ : ∀ j, 0 < κ j) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0)
    (hR : ∀ j, κ j / ‖z none‖ ≤ R) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j i, |v j i| ≤ 1) (hW : ∀ i, ‖ratio z i‖ ≤ 1)
    (hL : ∀ j, L ≤ κ j * ‖z none‖ / 2 * squaredDistance (ratio z) (v j)) :
    ‖waveCurrent κ cR cI v x z‖ ≤
      ((Fintype.card ι : ℝ) * ((d : ℝ) + 1) * (R ^ ((d : ℝ) / 2) * Real.exp (-L) * C)) ^ 2 := by
  apply currentMatrix_norm_le_uniform _ _ _ _ _ (by positivity) (by positivity)
  · intro j
    apply tangentVector_norm_le _ _ _ hW
    intro i
    simpa using hv j i
  · intro j
    exact normalizedModeAmplitude_norm_le_parameters _ _ _ R C L (hκ j) _ x z hY
      (hR j) (hC j) (hL j)

end OAI.Analysis.Calculus.Current
