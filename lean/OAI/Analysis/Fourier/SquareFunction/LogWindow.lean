import OAI.Analysis.Fourier.SquareFunction.ScaleSums

/-! Choosing the logarithmic width in the combining-dilates argument. -/

namespace OAI.Analysis.Fourier.SquareFunction

/-- A positive integer window whose geometric error absorbs the polynomial
kernel loss, while its number of middle scales is logarithmic in `1/δ`. -/
theorem exists_logarithmic_window {N δ : ℝ} (hN : 0 ≤ N)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ L : ℤ, 0 < L ∧ (2 : ℝ) ^ (-L) ≤ δ ^ (N + 1) ∧
      ((2 * L).toNat : ℝ) ≤
        (2 * (N + 1) / Real.log 2 + 4) * (1 + Real.log (1 / δ)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogδ : 0 ≤ Real.log (1 / δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by simpa using hδ1))
  let x := (N + 1) * Real.log (1 / δ) / Real.log 2
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  let L : ℤ := ⌈x⌉ + 1
  have hL : 0 < L := by
    have hc : (0 : ℤ) ≤ ⌈x⌉ := Int.ceil_nonneg hx
    dsimp only [L]
    omega
  have hxL : x ≤ (L : ℝ) := by
    have hc := Int.le_ceil x
    dsimp only [L]
    push_cast
    linarith
  have hLx : (L : ℝ) ≤ x + 2 := by
    have hc := Int.ceil_lt_add_one x
    dsimp only [L]
    push_cast
    linarith
  refine ⟨L, hL, ?_, ?_⟩
  · have hmul := (div_le_iff₀ hlog).mp hxL
    change (N + 1) * Real.log (1 / δ) ≤ (L : ℝ) * Real.log 2 at hmul
    rw [one_div, Real.log_inv] at hmul
    have he : Real.log 2 * (-(L : ℝ)) ≤ Real.log δ * (N + 1) := by nlinarith
    calc
      (2 : ℝ) ^ (-L) = Real.exp (Real.log 2 * (-(L : ℝ))) := by
        rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        push_cast
        rfl
      _ ≤ Real.exp (Real.log δ * (N + 1)) := Real.exp_le_exp.mpr he
      _ = δ ^ (N + 1) := (Real.rpow_def_of_pos hδ (N + 1)).symm
  · have hcast : ((2 * L).toNat : ℝ) = 2 * (L : ℝ) := by
      have he : ((2 * L).toNat : ℤ) = 2 * L := Int.toNat_of_nonneg (by omega)
      exact_mod_cast he
    rw [hcast]
    have hc : 0 ≤ 2 * (N + 1) / Real.log 2 := by positivity
    have hh := mul_nonneg hc hlogδ
    have h₂ := mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hlogδ
    dsimp only [x] at hLx
    ring_nf at hLx hc hh h₂ ⊢
    nlinarith

end OAI.Analysis.Fourier.SquareFunction
