import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticLayoutCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticMonotone

namespace OAI.Algorithms

/-! Uniform transport from the original dimension to a residual dimension
between one half and all of it. No lower bound on arbitrary residuals is
assumed: callers must supply the displayed half-dimension condition. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem L_mono : Monotone L := by
  intro a b hab
  unfold L
  simp only [Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.add_le_add_right hab 16)) 1

theorem w_mono : Monotone w := by
  intro a b hab
  unfold w
  simp only [Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (L_mono hab)) 1

theorem L_le_succ_of_half {n m : ℕ} (hnm : n ≤ 2 * m) : L n ≤ L m + 1 := by
  have harg : n + 16 ≤ (m + 16) * 2 := by omega
  have h := Nat.log_mono_right (b := 2) harg
  rw [Nat.log_mul_base (by norm_num : 1 < (2 : ℕ)) (by omega : m + 16 ≠ 0)] at h
  simpa [L, Nat.log2_eq_log_two, Nat.add_assoc] using Nat.add_le_add_right h 1

theorem L_le_twice_of_half {n m : ℕ} (hnm : n ≤ 2 * m) : L n ≤ 2 * L m := by
  have := L_le_succ_of_half hnm
  have := L_pos m
  omega

theorem sqrt_L_le_twice_of_half {n m : ℕ} (hnm : n ≤ 2 * m) :
    Real.sqrt (L n : ℝ) ≤ 2 * Real.sqrt (L m : ℝ) := by
  have h : (L n : ℝ) ≤ 2 * (L m : ℝ) := by exact_mod_cast L_le_twice_of_half hnm
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ L m by positivity)
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith

theorem residual_log_ratio_le {n m : ℕ} (hmn : m ≤ n) (hnm : n ≤ 2 * m) :
    (w m : ℝ) / Real.sqrt (L m : ℝ) ≤
      2 * (w n : ℝ) / Real.sqrt (L n : ℝ) := by
  have hm : 0 < Real.sqrt (L m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast L_pos m)
  have hn : 0 < Real.sqrt (L n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast L_pos n)
  have hw : (w m : ℝ) ≤ w n := by exact_mod_cast w_mono hmn
  have hs := sqrt_L_le_twice_of_half hnm
  apply (div_le_div_iff₀ hm hn).2
  calc
    (w m : ℝ) * Real.sqrt (L n : ℝ) ≤ (w n : ℝ) * (2 * Real.sqrt (L m : ℝ)) := by gcongr
    _ = _ := by ring

/-- Eventual assertions are uniform over every residual dimension in the
half interval; in particular the residual may depend on a branch. -/
theorem eventually_uniform_half {P : ℕ → Prop} (hP : ∀ᶠ m in atTop, P m) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ 2 * m → P m := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hP
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn m hnm
  exact hN m (by omega)

theorem residual_tendsto (f : ℕ → ℕ)
    (hf : ∀ᶠ n in atTop, n ≤ 2 * f n) : Tendsto f atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [hf, eventually_ge_atTop (2 * N)] with n hn hN
  omega

theorem half_of_small_removal {n m : ℕ} (hL : 4 ≤ L n)
    (hrem : (n : ℝ) - (n : ℝ) / Real.sqrt (L n : ℝ) ≤ m) : n ≤ 2 * m := by
  have hs : (2 : ℝ) ≤ Real.sqrt (L n : ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    exact_mod_cast hL
  have hd : (n : ℝ) / Real.sqrt (L n : ℝ) ≤ (n : ℝ) / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hs
  have hh : (n : ℝ) ≤ 2 * (m : ℝ) := by linarith
  exact_mod_cast hh

theorem eventually_half_of_small_removal :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (n : ℝ) - (n : ℝ) / Real.sqrt (L n : ℝ) ≤ m → n ≤ 2 * m := by
  filter_upwards [eventually_L_ge 4] with n hn m hm
  exact half_of_small_removal hn hm

/-- A fixed polynomial bound in the original logarithm is still a fixed
polynomial bound in every half-size residual logarithm. -/
theorem eventually_residual_polynomial (C q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m b : ℕ, n ≤ 2 * m →
      b ≤ C * L n ^ q → b ≤ L m ^ (q + 1) := by
  filter_upwards [eventually_uniform_half (eventually_L_ge (C * 2 ^ q))] with n hn m b hnm hb
  have hC := hn m hnm
  calc
    b ≤ C * L n ^ q := hb
    _ ≤ C * (2 * L m) ^ q := by gcongr; exact L_le_twice_of_half hnm
    _ = (C * 2 ^ q) * L m ^ q := by rw [mul_pow]; ring
    _ ≤ L m * L m ^ q := Nat.mul_le_mul_right _ hC
    _ = _ := by rw [pow_succ]; ring

theorem layoutCutoff_mono (n : ℕ) : Monotone (layoutCutoff n) := by
  intro a b hab
  have he : layoutEnergy n a ≤ layoutEnergy n b := by
    unfold layoutEnergy
    simp only [Nat.log2_eq_log_two]
    apply Nat.add_le_add_right
    apply Nat.log_mono_right
    gcongr
  unfold layoutCutoff
  apply Nat.add_le_add_right
  apply Nat.sqrt_le_sqrt
  exact Nat.mul_le_mul_left _ he

theorem eventually_uniform_cutoff_ratio (q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ b : ℕ, b ≤ L m ^ q →
      (layoutCutoff m b : ℝ) / layoutQ m ≤
        (128 * (28 * q + 312) : ℕ) * (w m : ℝ) / Real.sqrt (L m : ℝ) := by
  have hh := eventually_cutoff_ratio (fun m => L m ^ q) q (Eventually.of_forall (fun _ => le_rfl))
  filter_upwards [hh] with m hm b hb
  exact (div_le_div_of_nonneg_right (by exact_mod_cast layoutCutoff_mono m hb) (by positivity)).trans hm

theorem eventually_residual_cutoff_ratio (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m b : ℕ, m ≤ n → n ≤ 2 * m → b ≤ L m ^ q →
      (layoutCutoff m b : ℝ) / layoutQ m ≤
        (256 * (28 * q + 312) : ℕ) * (w n : ℝ) / Real.sqrt (L n : ℝ) := by
  filter_upwards [eventually_uniform_half (eventually_uniform_cutoff_ratio q)] with n hn m b hmn hnm hb
  have hlocal := hn m hnm b hb
  have hratio := residual_log_ratio_le hmn hnm
  calc
    _ ≤ (128 * (28 * q + 312) : ℕ) * ((w m : ℝ) / Real.sqrt (L m : ℝ)) := by simpa [mul_div_assoc] using hlocal
    _ ≤ (128 * (28 * q + 312) : ℕ) * (2 * (w n : ℝ) / Real.sqrt (L n : ℝ)) := by gcongr
    _ = _ := by push_cast; ring

theorem eventually_residual_inverse_target :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, m ≤ n → n ≤ 2 * m →
      (n : ℝ) / layoutR m ≤ 256 * Statement.runtimeScale n := by
  filter_upwards [eventually_uniform_half eventually_layout_inverse_target] with n hn m hmn hnm
  have hlocal := hn m hnm
  have hnm' : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hnm
  have hh := div_le_div_of_nonneg_right hnm' (show (0 : ℝ) ≤ layoutR m by positivity)
  have ht := runtimeScale_mono hmn
  calc
    _ ≤ 2 * ((m : ℝ) / layoutR m) := by simpa [mul_div_assoc] using hh
    _ ≤ 2 * (128 * Statement.runtimeScale m) := by gcongr
    _ ≤ 256 * Statement.runtimeScale n := by nlinarith

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
