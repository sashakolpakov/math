import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticTarget

namespace OAI.Algorithms

/-! Integer layout parameters agreed with the layout and spectral components.
The occurrence bound `b` is an explicit argument. Positivity assumptions are
kept on theorems rather than built into an opaque choice. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

def layoutR (n : ℕ) : ℕ := max 2 (s n)
def layoutDen (n : ℕ) : ℕ := 64 * (Nat.log2 (layoutR n) + 1)
def layoutQ (n : ℕ) : ℕ := L n / layoutDen n
def layoutEnergy (n b : ℕ) : ℕ := Nat.log2 (64 * b * layoutR n * L n ^ 2) + 1
def layoutCutoff (n b : ℕ) : ℕ := Nat.sqrt (128 * layoutQ n * layoutEnergy n b) + 4
def layoutEpsilon (n b : ℕ) : ℚ := 1 / (32 * b * layoutR n * L n ^ 2 : ℕ)

theorem layoutR_ge_two (n : ℕ) : 2 ≤ layoutR n := le_max_left _ _
theorem layoutDen_pos (n : ℕ) : 0 < layoutDen n := by
  unfold layoutDen
  positivity
theorem layoutCutoff_ge_four (n b : ℕ) : 4 ≤ layoutCutoff n b := by
  unfold layoutCutoff
  omega
theorem layoutEnergy_pos (n b : ℕ) : 0 < layoutEnergy n b := by
  unfold layoutEnergy
  omega
theorem layoutEpsilon_pos (n : ℕ) {b : ℕ} (hb : 0 < b) : 0 < layoutEpsilon n b := by
  have hr := layoutR_ge_two n
  have hL := L_pos n
  unfold layoutEpsilon
  positivity

theorem eventually_layoutR_eq_s : ∀ᶠ n : ℕ in Filter.atTop, layoutR n = s n := by
  filter_upwards [eventually_le_s 2] with n hn
  exact max_eq_right hn

theorem layoutCutoff_square (n b : ℕ) :
    128 * layoutQ n * layoutEnergy n b ≤ layoutCutoff n b ^ 2 := by
  have h := Nat.lt_succ_sqrt' (128 * layoutQ n * layoutEnergy n b)
  simp only [Nat.succ_eq_add_one] at h
  unfold layoutCutoff
  exact h.le.trans (Nat.pow_le_pow_left (by omega) 2)

theorem layout_log_epsilon_le (n : ℕ) {b : ℕ} (hb : 0 < b) :
    Real.log (2 / (layoutEpsilon n b : ℝ)) ≤ layoutEnergy n b := by
  have hr : 0 < layoutR n := by have := layoutR_ge_two n; omega
  have hL := L_pos n
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hr' : (0 : ℝ) < layoutR n := by exact_mod_cast hr
  have hL' : (0 : ℝ) < L n := by exact_mod_cast hL
  have he : (layoutEpsilon n b : ℝ) = 1 / (32 * (b : ℝ) * layoutR n * (L n : ℝ) ^ 2) := by
    norm_num [layoutEpsilon]
  have hid : 2 / (layoutEpsilon n b : ℝ) = (64 * b * layoutR n * L n ^ 2 : ℕ) := by
    rw [he]
    push_cast
    field_simp
    ; ring
  rw [hid]
  have hx : 1 ≤ (64 * b * layoutR n * L n ^ 2 : ℕ) := by
    have : 0 < 64 * b * layoutR n * L n ^ 2 := by positivity
    omega
  have hx' : (1 : ℝ) ≤ (64 * b * layoutR n * L n ^ 2 : ℕ) := by exact_mod_cast hx
  have hlog := Real.log_nonneg hx'
  have htwo := log_two_bounds
  have hl : Real.log (64 * b * layoutR n * L n ^ 2 : ℕ) ≤
      Real.logb 2 (64 * b * layoutR n * L n ^ 2 : ℕ) := by
    unfold Real.logb
    apply (le_div_iff₀ (show 0 < Real.log (2 : ℝ) by linarith)).2
    nlinarith
  apply hl.trans
  have hh := (SubexpExponentArithmetic.logb_lt_natLog2_add_one
    (64 * b * layoutR n * L n ^ 2)).le
  push_cast at hh
  dsimp only [layoutEnergy]
  push_cast
  exact hh

theorem layout_spectral_square (n : ℕ) {b : ℕ} (hb : 0 < b) :
    32 * ((layoutQ n - 1 : ℕ) : ℝ) * Real.log (2 / (layoutEpsilon n b : ℝ)) ≤
      (layoutCutoff n b : ℝ) ^ 2 := by
  have hlog := layout_log_epsilon_le n hb
  have hQ : ((layoutQ n - 1 : ℕ) : ℝ) ≤ layoutQ n := by exact_mod_cast Nat.sub_le (layoutQ n) 1
  have hsq : (128 : ℝ) * layoutQ n * layoutEnergy n b ≤ (layoutCutoff n b : ℝ) ^ 2 := by
    exact_mod_cast layoutCutoff_square n b
  calc
    32 * ((layoutQ n - 1 : ℕ) : ℝ) * Real.log (2 / (layoutEpsilon n b : ℝ)) ≤
        32 * ((layoutQ n - 1 : ℕ) : ℝ) * layoutEnergy n b :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ 32 * (layoutQ n : ℝ) * layoutEnergy n b := by gcongr
    _ ≤ 128 * (layoutQ n : ℝ) * layoutEnergy n b := by gcongr ; norm_num
    _ ≤ _ := hsq

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
