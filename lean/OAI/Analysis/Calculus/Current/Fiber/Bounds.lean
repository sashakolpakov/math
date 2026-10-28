import OAI.Analysis.Calculus.Current.BoundaryDecay
import OAI.LinearAlgebra.Moore.CalculusCofactorBounds

/-! Bounds for the actual fiber Hessian and its regularizing cofactor. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

theorem phaseRow_norm_le {d : ℕ} (W : Fin d → ℂ) (hW : ∀ i, ‖W i‖ ≤ 1) :
    ‖phaseRow W‖ ≤ (d : ℝ) + 1 := by
  have ht := tangentVector_norm_le W W hW hW
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  cases b with
  | none => exact (norm_le_pi_norm (tangentVector W W) (some none)).trans ht
  | some b =>
    cases b with
    | none => exact (norm_le_pi_norm (tangentVector W W) none).trans ht
    | some i =>
      change ‖W i‖ ≤ _
      exact (hW i).trans (by simp)

theorem ratioRow_norm_le {d : ℕ} (z : Index d → ℂ) (hW : ∀ i, ‖ratio z i‖ ≤ 1)
    (i : Fin d) : ‖ratioRow z i‖ ≤ ‖z none‖⁻¹ := by
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (norm_nonneg _))).mpr
  intro b
  cases b with
  | none =>
    change ‖-ratio z i / z none‖ ≤ _
    rw [norm_div, norm_neg, ← one_div]
    exact div_le_div_of_nonneg_right (hW i) (norm_nonneg _)
  | some b =>
    cases b with
    | none => simp [ratioRow]
    | some j => by_cases hji : j = i <;> simp [ratioRow, hji]

theorem fiberJacobian_norm_le {d : ℕ} (a : ℝ) (ha : 0 < a)
    (z : Index d → ℂ) (hay : a ≤ ‖z none‖)
    (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖fiberJacobian (1 / 10) a z‖ ≤ 10 * ((d : ℝ) + 1) / a := by
  have hW := fiber_ratio_coordinate_le_one a z hr
  have hinv : ‖z none‖⁻¹ ≤ a⁻¹ := inv_anti₀ ha hay
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  cases i with
  | none =>
    have hp := (norm_le_pi_norm (phaseRow (ratio z)) b).trans (phaseRow_norm_le _ hW)
    change ‖(10 / (a : ℂ)) * phaseRow (ratio z) b‖ ≤ _
    simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    norm_num
    exact (mul_le_mul_of_nonneg_left hp (show 0 ≤ 10 / a by positivity)).trans_eq (by ring)
  | some i =>
    have hp := ((norm_le_pi_norm (ratioRow z i) b).trans (ratioRow_norm_le z hW i)).trans hinv
    change ‖(1 / ((1 / 10 : ℝ) : ℂ)) * ratioRow z i b‖ ≤ _
    norm_num
    have hd : (1 : ℝ) ≤ (d : ℝ) + 1 := by simp
    calc
      _ ≤ 10 * a⁻¹ := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ ≤ (10 / a) * ((d : ℝ) + 1) := by
        simpa only [mul_one, div_eq_mul_inv] using
          mul_le_mul_of_nonneg_left hd (show 0 ≤ 10 / a by positivity)
      _ = _ := by ring

theorem quaternionFiberJacobian_norm_le {d : ℕ} (a : ℝ) (ha : 0 < a)
    (z : Index d → ℂ) (hay : a ≤ ‖z none‖)
    (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖quaternionFiberJacobian (1 / 10) a z‖ ≤ 10 * ((d : ℝ) + 1) / a := by
  have hJ := fiberJacobian_norm_le a ha z hay hr
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  change ‖complexK (fiberJacobian (1 / 10) a z i b)‖ ≤ _
  rw [complexK_norm]
  exact (norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ i).trans hJ)

theorem quaternionGram_norm_le {ι ν : Type*} [Fintype ι] [Fintype ν]
    (J : Matrix ι ν OAI.Analysis.Calculus.Quaternion.Q) : ‖Jᴴ * J‖ ≤ (Fintype.card ι : ℝ) * ‖J‖ ^ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro a
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  calc
    _ ≤ ∑ i, ‖star (J i a) * J i b‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖J‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, norm_star, pow_two]
      exact mul_le_mul ((norm_le_pi_norm _ a).trans (norm_le_pi_norm _ i))
        ((norm_le_pi_norm _ b).trans (norm_le_pi_norm _ i)) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp

theorem fiberHessian_norm_le {d : ℕ} (a : ℝ) (ha : 0 < a)
    (z : Index d → ℂ) (hay : a ≤ ‖z none‖)
    (hr : fiberDefining (1 / 10) a z ≤ 0) :
    ‖fiberHessian (1 / 10) a z‖ ≤ 400 * ((d : ℝ) + 1) ^ 3 / a ^ 2 := by
  have hY : z none ≠ 0 := norm_pos_iff.mp (ha.trans_le hay)
  rw [fiberHessian_factorization _ _ _ hY, norm_smul]
  have hG := quaternionGram_norm_le (quaternionFiberJacobian (1 / 10) a z)
  have hJ := pow_le_pow_left₀ (norm_nonneg _) (quaternionFiberJacobian_norm_le a ha z hay hr) 2
  have hg : ‖(quaternionFiberJacobian (1 / 10) a z)ᴴ * quaternionFiberJacobian (1 / 10) a z‖ ≤
      ((d : ℝ) + 1) * (10 * ((d : ℝ) + 1) / a) ^ 2 := by
    apply hG.trans
    simpa [Fintype.card_option] using mul_le_mul_of_nonneg_left hJ (show 0 ≤ (d : ℝ) + 1 by positivity)
  norm_num
  calc
    _ ≤ 4 * (((d : ℝ) + 1) * (10 * ((d : ℝ) + 1) / a) ^ 2) := by linarith
    _ = _ := by ring

theorem fiberCofactor_norm_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (z : Index d → ℂ), 0 < a → a ≤ ‖z none‖ →
      fiberDefining (1 / 10) a z ≤ 0 →
      ‖fiberCofactor (1 / 10) a z‖ ≤ C / a ^ (2 * (d + 1)) := by
  obtain ⟨C, hC, hbound⟩ := OAI.Analysis.Calculus.Quaternion.indexedCofactor_norm_bound (Index d)
  refine ⟨C * (400 * ((d : ℝ) + 1) ^ 3) ^ (d + 1), by positivity, ?_⟩
  intro a z ha hay hr
  have hcf : ‖fiberCofactor (1 / 10) a z‖ ≤
      C * ‖fiberHessian (1 / 10) a z‖ ^ (d + 1) := by
    simpa [fiberCofactor, Index] using hbound (fiberHessian (1 / 10) a z)
  calc
    _ ≤ C * (400 * ((d : ℝ) + 1) ^ 3 / a ^ 2) ^ (d + 1) := hcf.trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (fiberHessian_norm_le a ha z hay hr) _) hC.le)
    _ = _ := by rw [div_pow, ← pow_mul]; ring

/-- The added cofactor is uniformly tiny once the fiber scale exceeds `h`. -/
theorem regularizingCofactor_norm_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h a : ℝ) (z : Index d → ℂ), 0 < h → h ≤ a →
      a ≤ ‖z none‖ → fiberDefining (1 / 10) a z ≤ 0 →
      ‖h ^ (50 * (d + 1)) • fiberCofactor (1 / 10) a z‖ ≤ C * h ^ (48 * (d + 1)) := by
  obtain ⟨C, hC, hbound⟩ := fiberCofactor_norm_bound d
  refine ⟨C, hC, ?_⟩
  intro h a z hh hha hay hr
  have hcf := hbound a z (hh.trans_le hha) hay hr
  have hcf' : ‖fiberCofactor (1 / 10) a z‖ ≤ C / h ^ (2 * (d + 1)) :=
    hcf.trans (div_le_div_of_nonneg_left hC.le (pow_pos hh _)
      (pow_le_pow_left₀ hh.le hha _))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hh.le _)]
  calc
    _ ≤ h ^ (50 * (d + 1)) * (C / h ^ (2 * (d + 1))) :=
      mul_le_mul_of_nonneg_left hcf' (pow_nonneg hh.le _)
    _ = _ := by
      rw [show 50 * (d + 1) = 48 * (d + 1) + 2 * (d + 1) by omega, pow_add]
      field_simp

end OAI.Analysis.Calculus.Current
