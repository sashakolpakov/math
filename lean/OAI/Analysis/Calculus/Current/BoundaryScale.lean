import OAI.Analysis.Calculus.Current.Crude

/-! Logarithmic fiber scales produce arbitrary-power lateral decay. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

theorem constant_le_negative_rpow (h P : ℝ) (hh : 0 < h) (hP : 0 ≤ P)
    (hL : 1 ≤ Real.log h⁻¹) : P ≤ h ^ (-P) := by
  rw [Real.rpow_def_of_pos hh]
  have hle : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  apply hle.trans (Real.exp_le_exp.mpr ?_)
  rw [Real.log_inv] at hL
  nlinarith

theorem scaled_mode_majorant_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (h N K C : ℝ) (hh : 0 < h) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hcount : (Fintype.card ι : ℝ) ≤ N / h ^ (d + 1)) :
    (Fintype.card ι : ℝ) * ((d : ℝ) + 1) * ((K / h ^ 2) ^ ((d : ℝ) / 2) * C) ≤
      (N * ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) * C)) / h ^ (2 * d + 1) := by
  rw [scale_rpow_half h K d hh hK]
  have hp := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) / h ^ d * C) by positivity)
  convert hp using 1
  · ring
  · rw [show 2 * d + 1 = (d + 1) + d by omega, pow_add]
    ring

theorem polynomial_loss_absorbed (h P : ℝ) (e : ℕ) (hh : 0 < h)
    (hP : 0 ≤ P) (hL : 1 ≤ Real.log h⁻¹) :
    P / h ^ e ≤ h ^ (-(P + e)) := by
  calc
    _ ≤ h ^ (-P) / h ^ e := div_le_div_of_nonneg_right
      (constant_le_negative_rpow h P hh hP hL) (pow_nonneg hh.le _)
    _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_sub hh]; congr 1; ring

/-- A dimension-and-data-dependent logarithmic fiber width suffices for every
specified power of lateral decay; no Gaussian or norm estimate is a premise. -/
theorem exists_logarithmic_scale_lateral_decay (d : ℕ) (N K C c M : ℝ)
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hC0 : 0 ≤ C) (hc : 0 < c) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {ι : Type} [Fintype ι]
      (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
      (x : Index d → ℝ) (z : Index d → ℂ),
      0 < h → 1 ≤ Real.log h⁻¹ → L * h * Real.log h⁻¹ ≤ a → a ≤ ‖z none‖ →
      (Fintype.card ι : ℝ) ≤ N / h ^ (d + 1) →
      (∀ j, c / h ≤ κ j) → (∀ j, κ j ≤ K / h) →
      (∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C) →
      (∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600) →
      fiberDefining (1 / 10) a z = 0 →
      ‖sourceWavePart h a κ cR cI v x z‖ ≤ h ^ M := by
  let P := N * ((d : ℝ) + 1) * (K ^ ((d : ℝ) / 2) * C)
  let b := P + (2 * d + 1 : ℕ)
  let L := max 1 (3200 * (b + M / 2) / c)
  have hL₁ : 1 ≤ L := le_max_left _ _
  refine ⟨L, hL₁, ?_⟩
  intro ι inst h a κ cR cI v x z hh hlog hscale hay hcount hlow hupp hcoeff hv hr
  have hlog0 : 0 ≤ Real.log h⁻¹ := le_trans zero_le_one hlog
  have hha : h ≤ a := by
    apply le_trans ?_ hscale
    calc
      h ≤ L * h := by nlinarith
      _ ≤ L * h * Real.log h⁻¹ := le_mul_of_one_le_right (by positivity) hlog
  have hY : z none ≠ 0 := norm_pos_iff.mp ((hh.trans_le hha).trans_le hay)
  have hκ : ∀ j, 0 < κ j := fun j => (div_pos hc hh).trans_le (hlow j)
  apply sourceWavePart_lateral_power_bound h a (K / h ^ 2) C (c / h) b M hh
    (by positivity) hC0 κ cR cI v hκ hlow x z hY
    (fun j => frequency_over_height_bound h K (κ j) _ hh (hκ j).le (hupp j) (hha.trans hay))
    hcoeff hv hr
  · exact (scaled_mode_majorant_bound h N K C hh hK hC0 hcount).trans
      (polynomial_loss_absorbed h P (2 * d + 1) hh (by dsimp [P]; positivity) hlog)
  · have hcoef : b + M / 2 ≤ c * L / 3200 := by
      have he := (div_le_iff₀ hc).mp (le_max_right 1 (3200 * (b + M / 2) / c))
      dsimp [L]
      nlinarith
    have h₁ := mul_le_mul_of_nonneg_right hcoef hlog0
    have h₂ := mul_le_mul_of_nonneg_left (hscale.trans hay) (show 0 ≤ (c / h) / 3200 by positivity)
    have heq : ((c / h) / 3200) * (L * h * Real.log h⁻¹) =
        (c * L / 3200) * Real.log h⁻¹ := by field_simp
    rw [heq] at h₂
    convert h₁.trans h₂ using 1 ; ring

end OAI.Analysis.Calculus.Current
