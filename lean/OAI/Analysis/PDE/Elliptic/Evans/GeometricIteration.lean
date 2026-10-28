import OAI.Analysis.PDE.Elliptic.TailPointwise

open Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

theorem exists_oscillation_exponent {ρ θ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hθ1 : θ < 1) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ max ρ θ < ρ ^ α := by
  have hc : ContinuousAt (fun α : ℝ ↦ ρ ^ α) 0 :=
    Real.continuousAt_const_rpow hρ.ne'
  have he : ∀ᶠ α : ℝ in 𝓝 0, max ρ θ < ρ ^ α :=
    hc.eventually (lt_mem_nhds (by simpa only [Real.rpow_zero] using max_lt hρ1 hθ1))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  let α := min (r / 2) (1 / 2)
  have hα : 0 < α := lt_min (by positivity) (by norm_num)
  refine ⟨α, hα, lt_of_le_of_lt (min_le_right _ _) (by norm_num), hball ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hα]
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

theorem geometric_inhomogeneous_bound {ρ θ q B C : ℝ}
    (hρ : 0 ≤ ρ) (hρq : ρ ≤ q) (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hsize : θ * C + B ≤ C * q) (ω : ℕ → ℝ) (hstart : ω 0 ≤ C)
    (hstep : ∀ k, ω (k + 1) ≤ θ * ω k + B * ρ ^ k) :
    ∀ k, ω k ≤ C * q ^ k := by
  intro k
  induction k with
  | zero => simpa using hstart
  | succ k ih =>
      calc
        ω (k + 1) ≤ θ * ω k + B * ρ ^ k := hstep k
        _ ≤ θ * (C * q ^ k) + B * q ^ k := add_le_add
          (mul_le_mul_of_nonneg_left ih hθ)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ hρq k) hB)
        _ = (θ * C + B) * q ^ k := by ring
        _ ≤ (C * q) * q ^ k := mul_le_mul_of_nonneg_right hsize (pow_nonneg (hρ.trans hρq) k)
        _ = C * q ^ (k + 1) := by rw [pow_succ]; ring

theorem exists_geometric_radius {ρ r : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ k : ℕ, ρ ^ (k + 1) < r ∧ r ≤ ρ ^ k := by
  have ht : Tendsto (fun k : ℕ ↦ ρ ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ.le hρ1
  have hex : ∃ k : ℕ, ρ ^ k < r := (ht.eventually (gt_mem_nhds hr)).exists
  have hn : Nat.find hex ≠ 0 := by
    intro hn
    have hs := Nat.find_spec hex
    rw [hn, pow_zero] at hs
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine ⟨k, ?_, ?_⟩
  · simpa only [hk, Nat.succ_eq_add_one] using Nat.find_spec hex
  · exact le_of_not_gt (Nat.find_min hex (by omega))

end OAI.Analysis.PDE.Elliptic
