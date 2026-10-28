import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open Set Filter _root_.MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

theorem exists_power_strict_lower {M t : ℝ} (hM : 1 < M) (ht : 1 < t) :
    ∃ k : ℕ, M ^ k < t ∧ t ≤ M ^ (k + 1) := by
  have hex : ∃ n : ℕ, t ≤ M ^ n := by
    obtain ⟨n, _, hn⟩ := exists_nat_pow_near ht.le hM
    exact ⟨n + 1, hn.le⟩
  have hn0 : Nat.find hex ≠ 0 := by
    intro hn
    have hs := Nat.find_spec hex
    rw [hn, pow_zero] at hs
    exact not_le_of_gt ht hs
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨k, lt_of_not_ge (Nat.find_min hex (by omega)), ?_⟩
  simpa only [hk] using Nat.find_spec hex

/-- A small positive moment exponent can be chosen so that the
growth in the level grid is dominated by geometric measure decay. -/
theorem exists_moment_exponent {M theta : ℝ} (hM : 1 < M) (htheta : theta < 1) :
    ∃ p : ℝ, 0 < p ∧ theta * M ^ p < 1 := by
  have hM0 : 0 < M := zero_lt_one.trans hM
  have hc : ContinuousAt (fun p : ℝ ↦ theta * M ^ p) 0 :=
    continuousAt_const.mul (Real.continuousAt_const_rpow hM0.ne')
  have he : ∀ᶠ p : ℝ in 𝓝 0, theta * M ^ p < 1 :=
    hc.eventually (gt_mem_nhds (by simpa only [Real.rpow_zero, mul_one] using htheta))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r / 2, by positivity, hball ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 2)]
  linarith

theorem rpow_le_geometric_indicators {M p : ℝ} (hM : 1 < M) (hp : 0 ≤ p) (t : ℝ) :
    ENNReal.ofReal t ^ p ≤ 1 + ∑' k : ℕ,
      if M ^ k < t then (ENNReal.ofReal M ^ p) ^ (k + 1) else 0 := by
  by_cases ht : t ≤ 1
  · have h := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_one.mpr ht) hp
    have h' : ENNReal.ofReal t ^ p ≤ 1 := by simpa only [ENNReal.one_rpow] using h
    exact h'.trans le_self_add
  · obtain ⟨k, hk, hk'⟩ := exists_power_strict_lower hM (lt_of_not_ge ht)
    have hM0 : 0 ≤ M := (zero_lt_one.trans hM).le
    have h := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hk') hp
    have hb : ENNReal.ofReal t ^ p ≤ (ENNReal.ofReal M ^ p) ^ (k + 1) := by
      simpa only [ENNReal.ofReal_pow hM0, ← ENNReal.rpow_natCast_mul,
        mul_comm (↑(k + 1) : ℝ) p, ENNReal.rpow_mul_natCast] using h
    calc
      ENNReal.ofReal t ^ p ≤ (ENNReal.ofReal M ^ p) ^ (k + 1) := hb
      _ = (if M ^ k < t then (ENNReal.ofReal M ^ p) ^ (k + 1) else 0) := by rw [ite_eq_left hk]
      _ ≤ ∑' j : ℕ, if M ^ j < t then (ENNReal.ofReal M ^ p) ^ (j + 1) else 0 :=
        ENNReal.le_tsum (f := fun j : ℕ ↦
          if M ^ j < t then (ENNReal.ofReal M ^ p) ^ (j + 1) else 0) k
      _ ≤ 1 + ∑' j : ℕ, if M ^ j < t then (ENNReal.ofReal M ^ p) ^ (j + 1) else 0 := le_add_self

end OAI.Analysis.PDE.Elliptic
