import OAI.Analysis.PDE.Energy.Comparison

/-! Smooth defining-function cutoffs, including a uniformly bounded scaled
normal derivative. These are used for tangential-flux integration by parts. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

def transitionSlope (t : ℝ) : ℝ := t * deriv Real.smoothTransition t

theorem transition_deriv_zero_left {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 t] (fun _ ↦ (0 : ℝ)) := by
    filter_upwards [gt_mem_nhds ht] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [he.deriv_eq, deriv_const]

theorem transition_deriv_zero_right {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 t] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [lt_mem_nhds ht] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [he.deriv_eq, deriv_const]

theorem transitionSlope_zero_nonpos {t : ℝ} (ht : t ≤ 0) : transitionSlope t = 0 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [transitionSlope]
  · simp [transitionSlope, transition_deriv_zero_left ht]

theorem transitionSlope_zero_right {t : ℝ} (ht : 1 < t) : transitionSlope t = 0 := by
  simp [transitionSlope, transition_deriv_zero_right ht]

theorem continuous_transitionSlope : Continuous transitionSlope := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by norm_num)
  exact continuous_id.mul hd

theorem exists_transitionSlope_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖transitionSlope t‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.image continuous_transitionSlope).isBounded.exists_norm_le
  have h0 : 0 ≤ C := by
    have h := hC _ (mem_image_of_mem transitionSlope (show (0 : ℝ) ∈ Icc 0 1 by norm_num))
    simpa [transitionSlope] using h
  refine ⟨C,h0,?_⟩
  intro t
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact hC _ (mem_image_of_mem transitionSlope ht)
  · rcases not_and_or.mp ht with hleft | hright
    · rw [transitionSlope_zero_nonpos (le_of_lt (lt_of_not_ge hleft)), norm_zero]
      exact h0
    · rw [transitionSlope_zero_right (lt_of_not_ge hright), norm_zero]
      exact h0

def boundaryCutoff (r : ℝ) (k : ℕ) : ℝ := Real.smoothTransition (-((k : ℝ) + 1) * r)

theorem eventually_cutoff_argument_gt_one {r : ℝ} (hr : r < 0) :
    ∀ᶠ k : ℕ in atTop, 1 < -((k : ℝ) + 1) * r := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1 / (-r))
  have hn : 1 < (N : ℝ) * (-r) := (div_lt_iff₀ (neg_pos.mpr hr)).mp hN
  filter_upwards [eventually_ge_atTop N] with k hk
  have hmul := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (neg_nonneg.mpr hr.le)
  nlinarith

theorem boundaryCutoff_tendsto {r : ℝ} (hr : r < 0) :
    Tendsto (boundaryCutoff r) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_cutoff_argument_gt_one hr] with k hk
  exact (Real.smoothTransition.one_of_one_le hk.le).symm

theorem transitionSlope_cutoff_tendsto (r : ℝ) :
    Tendsto (fun k : ℕ ↦ transitionSlope (-((k : ℝ) + 1) * r)) atTop (𝓝 0) := by
  by_cases hr : r < 0
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_cutoff_argument_gt_one hr] with k hk
    exact (transitionSlope_zero_right hk).symm
  · have hz (k : ℕ) : transitionSlope (-((k : ℝ) + 1) * r) = 0 := by
      apply transitionSlope_zero_nonpos
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (le_of_not_gt hr)
    simp only [hz]
    exact tendsto_const_nhds

theorem boundaryCutoff_zero {r : ℝ} (hr : 0 ≤ r) (k : ℕ) : boundaryCutoff r k = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hr

end OAI.Analysis.PDE.Green
