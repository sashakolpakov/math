import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticResidual

namespace OAI.Algorithms

/-! The support cutoff uses residual spectral parameters and original
ambient precision. This numerical bound keeps the two dimensions distinct. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_ambient_support_scale_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * w n / Real.sqrt (L n : ℝ) := by
  filter_upwards [eventually_L_power_le_n 1 (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop 1] with n hLn hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hL1 : (1 : ℝ) ≤ L n := by exact_mod_cast L_pos n
  have hw : (1 : ℝ) ≤ w n := by exact_mod_cast w_pos n
  have hr : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hroot : Real.sqrt (L n : ℝ) ≤ n :=
    (show Real.sqrt (L n : ℝ) ≤ (L n : ℝ) from
      (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩).trans (by simpa using hLn)
  apply (le_div_iff₀ hr).2
  nlinarith

/-- Uniform in the residual, occurrence bound, and ambient precision
envelope. This is the numerical input to the separate support-entropy proof. -/
theorem eventually_residual_jet_bound (k a q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m b T : ℕ,
      m ≤ n → n ≤ 2 * m → b ≤ L m ^ q → T ≤ a * n →
      ((k * layoutCutoff m b * T / layoutQ m + 1 : ℕ) : ℝ) ≤
        ((k * a * (256 * (28 * q + 312)) : ℕ) + 1) *
          (n : ℝ) * w n / Real.sqrt (L n : ℝ) := by
  filter_upwards [eventually_residual_cutoff_ratio q,
    eventually_ambient_support_scale_ge_one] with n hn hone m b T hmn hnm hb hT
  have hratio := hn m b hmn hnm hb
  have hT' : (T : ℝ) ≤ (a : ℝ) * n := by exact_mod_cast hT
  have hdiv := Nat.cast_div_le (m := k * layoutCutoff m b * T) (n := layoutQ m) (α := ℝ)
  have hjet : ((k * layoutCutoff m b * T / layoutQ m + 1 : ℕ) : ℝ) ≤
      (k : ℝ) * ((layoutCutoff m b : ℝ) / layoutQ m) * T + 1 := by
    push_cast at hdiv ⊢
    calc
      _ ≤ (k : ℝ) * layoutCutoff m b * T / layoutQ m + 1 := by linarith
      _ = _ := by ring
  calc
    _ ≤ (k : ℝ) * ((layoutCutoff m b : ℝ) / layoutQ m) * T + 1 := hjet
    _ ≤ (k : ℝ) * ((256 * (28 * q + 312) : ℕ) * (w n : ℝ) /
        Real.sqrt (L n : ℝ)) * ((a : ℝ) * n) +
        (n : ℝ) * w n / Real.sqrt (L n : ℝ) := by gcongr
    _ = _ := by push_cast; ring

/-- A function-valued wrapper convenient for composing an actual runtime
parameter producer with the entropy theorem. -/
theorem eventually_residual_jet_functions (m b T : ℕ → ℕ) (k a q : ℕ)
    (hm : ∀ᶠ n : ℕ in atTop, m n ≤ n ∧ n ≤ 2 * m n)
    (hb : ∀ᶠ n : ℕ in atTop, b n ≤ L (m n) ^ q)
    (hT : ∀ᶠ n : ℕ in atTop, T n ≤ a * n) :
    ∀ᶠ n : ℕ in atTop,
      ((k * layoutCutoff (m n) (b n) * T n / layoutQ (m n) + 1 : ℕ) : ℝ) ≤
        ((k * a * (256 * (28 * q + 312)) : ℕ) + 1) *
          (n : ℝ) * w n / Real.sqrt (L n : ℝ) := by
  filter_upwards [eventually_residual_jet_bound k a q, hm, hb, hT] with n hn hmn hbn hTn
  exact hn (m n) (b n) (T n) hmn.1 hmn.2 hbn hTn

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
