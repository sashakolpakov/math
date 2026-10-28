import OAI.Analysis.Fourier.SquareFunction.CombiningConstants

/-! The frequency-shell kernel may have different spatial-decay and
small-parameter exponents. A power reparametrization preserves the
logarithmic combining loss. -/

namespace OAI.Analysis.Fourier.SquareFunction

open scoped ENNReal

theorem power_window_le {δ Q : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hQ : 0 ≤ Q) :
    δ ^ (Q + 1) ≤ δ :=
  Real.rpow_le_self_of_le_one hδ.le hδone (by linarith)

theorem power_window_decay {δ Q q : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hQ : 0 ≤ Q) (hq : 1 ≤ q) :
    δ ^ (-Q) ≤ (δ ^ (Q + 1)) ^ (-q) := by
  rw [← Real.rpow_mul hδ.le]
  apply Real.rpow_le_rpow_of_exponent_ge hδ hδone
  nlinarith [mul_nonneg hQ (sub_nonneg.mpr hq)]

theorem power_window_log {δ Q : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q) :
    1 + Real.log (1 / δ ^ (Q + 1)) ≤
      (Q + 1) * (1 + Real.log (1 / δ)) := by
  rw [one_div, one_div, Real.log_inv, Real.log_rpow hδ, Real.log_inv]
  nlinarith

theorem power_window_log_rpow {δ Q θ : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (1 + Real.log (1 / δ ^ (Q + 1))) ^ θ ≤
      ENNReal.ofReal (Q + 1) ^ θ * ENNReal.ofReal (1 + Real.log (1 / δ)) ^ θ := by
  have h := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (power_window_log hδ hQ)) hθ
  rwa [ENNReal.ofReal_mul (by linarith : 0 ≤ Q + 1), ENNReal.mul_rpow_of_nonneg _ _ hθ] at h

theorem power_window_decay_nat {δ q : ℝ} {Q : ℕ} (hδ : 0 < δ)
    (hδone : δ ≤ 1) (hq : 1 ≤ q) :
    (δ⁻¹) ^ Q ≤ (δ ^ ((Q : ℝ) + 1)) ^ (-q) := by
  have he : (δ⁻¹) ^ Q = δ ^ (-(Q : ℝ)) := by
    rw [← Real.rpow_natCast, Real.inv_rpow hδ.le, Real.rpow_neg hδ.le]
  rw [he]
  exact power_window_decay hδ hδone (Nat.cast_nonneg Q) hq

theorem shell_combining_coefficient_le {δ Q C σ θ : ℝ}
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (hσ : 0 ≤ σ) (hθ : 0 ≤ θ) (P B : ℝ≥0∞) :
    ENNReal.ofReal (C * δ ^ (Q + 1)) +
        ENNReal.ofReal (1 + Real.log (1 / δ ^ (Q + 1))) ^ θ *
          (P * ENNReal.ofReal (δ ^ (1 / 2 - σ))) +
        ENNReal.ofReal δ ^ (1 / 2 : ℝ) * B ≤
      (ENNReal.ofReal C + ENNReal.ofReal (Q + 1) ^ θ * P + B) *
        (ENNReal.ofReal (1 + Real.log (1 / δ)) ^ θ *
          ENNReal.ofReal (δ ^ (1 / 2 - σ))) := by
  let w := ENNReal.ofReal (1 + Real.log (1 / δ)) ^ θ
  let d := ENNReal.ofReal (δ ^ (1 / 2 - σ))
  have hw : 1 ≤ w := by
    have hl : (1 : ℝ) ≤ 1 + Real.log (1 / δ) := by
      have := Real.log_nonneg ((one_le_div hδ).mpr hδone)
      linarith
    simpa [w] using ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hl) hθ
  have hd : d ≤ w * d := by simpa using mul_le_mul' hw (le_refl d)
  have he : ENNReal.ofReal (δ ^ (Q + 1)) ≤ d := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδone
    linarith
  have he₂ : ENNReal.ofReal δ ^ (1 / 2 : ℝ) ≤ d := by
    rw [ENNReal.ofReal_rpow_of_pos hδ]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_ge hδ hδone
    linarith
  have h₁ : ENNReal.ofReal (C * δ ^ (Q + 1)) ≤ ENNReal.ofReal C * (w * d) := by
    rw [ENNReal.ofReal_mul hC]
    exact mul_le_mul' le_rfl (he.trans hd)
  have h₂ : ENNReal.ofReal (1 + Real.log (1 / δ ^ (Q + 1))) ^ θ * (P * d) ≤
      (ENNReal.ofReal (Q + 1) ^ θ * P) * (w * d) := by
    calc
      _ ≤ (ENNReal.ofReal (Q + 1) ^ θ * w) * (P * d) :=
        mul_le_mul' (power_window_log_rpow hδ hQ hθ) le_rfl
      _ = _ := by ring
  have h₃ : ENNReal.ofReal δ ^ (1 / 2 : ℝ) * B ≤ B * (w * d) := by
    exact (mul_le_mul' (he₂.trans hd) le_rfl).trans_eq (mul_comm _ _)
  exact (add_le_add (add_le_add h₁ h₂) h₃).trans_eq (by ring)

end OAI.Analysis.Fourier.SquareFunction
