import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.Profile

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Metric Filter _root_.MeasureTheory
open scoped Topology ContDiff

def radialBump : ContDiffBump (3/2 : ℝ) where
  rIn := 1/8
  rOut := 1/4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem radialBump_support : tsupport (radialBump : ℝ → ℝ) ⊆ Icc 1 2 := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hn
  have hd : (1/4:ℝ) ≤ dist x (3/2) := by
    rw [Real.dist_eq]
    have hn' : x < 1 ∨ 2 < x := by simpa only [mem_Icc,not_and_or,not_le] using hn
    rcases hn' with h | h
    · have := neg_le_abs (x-3/2)
      linarith
    · have := le_abs_self (x-3/2)
      linarith
  exact hx (radialBump.zero_of_le_dist hd)

theorem radialBump_zero_notMem : (0:ℝ) ∉ tsupport (radialBump : ℝ → ℝ) := by
  intro h
  have := (radialBump_support h).1
  norm_num at this

def weightedRadialBump (m : ℝ) (x : ℝ) : ℝ := x^m * radialBump x

theorem weightedRadialBump_support (m : ℝ) :
    tsupport (weightedRadialBump m) ⊆ Icc 1 2 :=
  tsupport_mul_subset_right.trans radialBump_support

theorem weightedRadialBump_contDiff (m : ℝ) : ContDiff ℝ ∞ (weightedRadialBump m) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp radialBump_zero_notMem] with y hy
    simp only [weightedRadialBump,hy,Pi.zero_apply,mul_zero]
  · exact (contDiffAt_id.rpow_const_of_ne hx).mul radialBump.contDiff.contDiffAt

theorem weightedRadialBump_hasCompactSupport (m : ℝ) :
    HasCompactSupport (weightedRadialBump m) := radialBump.hasCompactSupport.mul_left

theorem weightedRadialBump_integrable (m : ℝ) : Integrable (weightedRadialBump m) :=
  (weightedRadialBump_contDiff m).continuous.integrable_of_hasCompactSupport
    (weightedRadialBump_hasCompactSupport m)

theorem weightedRadialBump_integral_pos (m : ℝ) : 0 < ∫ x, weightedRadialBump m x := by
  apply (weightedRadialBump_contDiff m).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := (3/2:ℝ)) (weightedRadialBump_hasCompactSupport m)
  · intro x
    by_cases hx : 0 ≤ x
    · exact mul_nonneg (Real.rpow_nonneg hx _) radialBump.nonneg
    · have hb : radialBump x = 0 := image_eq_zero_of_notMem_tsupport (by
        intro hh
        have := (radialBump_support hh).1
        linarith)
      change 0 ≤ x ^ m * radialBump x
      simp only [hb,mul_zero,le_refl]
  · have hb : radialBump (3/2) = 1 := radialBump.one_of_mem_closedBall (by
      simp only [mem_closedBall,dist_self,radialBump]
      norm_num)
    simp only [weightedRadialBump,hb,mul_one]
    positivity

theorem weightedRadialBump_profile (m : ℝ) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧
      (∀ v, |v| ≤ η → c ≤ ‖radialProfile (weightedRadialBump m) v‖) ∧
      Tendsto (fun s => radialProfile (weightedRadialBump m) (-s)) atTop (𝓝 0) := by
  obtain ⟨η,c,hη,hc,hnear⟩ := radialProfile_lower_near_zero
    (weightedRadialBump_integrable m) (weightedRadialBump_integral_pos m)
  exact ⟨η,c,hη,hc,hnear,radialProfile_negative_tendsto _⟩

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
