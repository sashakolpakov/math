import OAI.Analysis.PDE.Green.Cutoff
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

open OAI.Analysis.PDE.Green

def halfspaceGapCutoff (n : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition (((n:ℝ)+1)*t-1)

def halfspaceGapSlope (n : ℕ) (t : ℝ) : ℝ :=
  ((n:ℝ)+1)*deriv Real.smoothTransition (((n:ℝ)+1)*t-1)

theorem contDiff_halfspaceGapCutoff (n : ℕ) : ContDiff ℝ ∞ (halfspaceGapCutoff n) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem hasDerivAt_halfspaceGapCutoff (n : ℕ) (t : ℝ) :
    HasDerivAt (halfspaceGapCutoff n) (halfspaceGapSlope n t) t := by
  have h := (((Real.smoothTransition.contDiff (n:=1)).differentiable one_ne_zero
    (((n:ℝ)+1)*t-1)).hasDerivAt).comp t
      (((hasDerivAt_id t).const_mul ((n:ℝ)+1)).sub_const 1)
  convert h using 1 <;> (try funext x) <;>
    simp [halfspaceGapCutoff,halfspaceGapSlope,mul_comm]

theorem halfspaceGapCutoff_nonneg (n : ℕ) (t : ℝ) : 0≤halfspaceGapCutoff n t :=
  Real.smoothTransition.nonneg _

theorem halfspaceGapCutoff_le_one (n : ℕ) (t : ℝ) : halfspaceGapCutoff n t≤1 :=
  Real.smoothTransition.le_one _

theorem halfspaceGapCutoff_zero {n : ℕ} {t : ℝ} (ht : ((n:ℝ)+1)*t≤1) :
    halfspaceGapCutoff n t=0 := Real.smoothTransition.zero_of_nonpos (by linarith)

theorem eventually_gap_argument_gt_one {t : ℝ} (ht : 0<t) :
    ∀ᶠ n:ℕ in atTop, 1<((n:ℝ)+1)*t-1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (2/t)
  have hNt : 2<(N:ℝ)*t := (div_lt_iff₀ ht).mp hN
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N:ℝ)≤n := by exact_mod_cast hn
  nlinarith

theorem halfspaceGapCutoff_tendsto (t : ℝ) :
    Tendsto (fun n ↦ halfspaceGapCutoff n t) atTop (𝓝 (if 0<t then (1:ℝ) else 0)) := by
  split_ifs with ht
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gap_argument_gt_one ht] with n hn
    exact (Real.smoothTransition.one_of_one_le hn.le).symm
  · have hz n : halfspaceGapCutoff n t=0 := halfspaceGapCutoff_zero (by
      have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0≤(n:ℝ)+1) (le_of_not_gt ht)
      linarith)
    simp only [hz]
    exact tendsto_const_nhds

theorem halfspaceGapSlope_eventually_zero (t : ℝ) :
    ∀ᶠ n:ℕ in atTop, halfspaceGapSlope n t=0 := by
  by_cases ht : 0<t
  · filter_upwards [eventually_gap_argument_gt_one ht] with n hn
    simp [halfspaceGapSlope,OAI.Analysis.PDE.Green.transition_deriv_zero_right hn]
  · apply Eventually.of_forall
    intro n
    have hn : ((n:ℝ)+1)*t-1<0 := by
      have := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0≤(n:ℝ)+1) (le_of_not_gt ht)
      linarith
    simp [halfspaceGapSlope,OAI.Analysis.PDE.Green.transition_deriv_zero_left hn]

theorem exists_transition_derivative_bound :
    ∃ D:ℝ,0≤D ∧ ∀t,|deriv Real.smoothTransition t|≤D := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n:=1)).continuous_deriv le_rfl
  obtain ⟨D,hD⟩ := (isCompact_Icc.image hd).isBounded.exists_norm_le
  have hD0 : 0≤D := (norm_nonneg _).trans (hD _ (mem_image_of_mem _ (show (0:ℝ)∈Icc 0 1 by norm_num)))
  refine ⟨D,hD0,fun t ↦ ?_⟩
  by_cases ht : t∈Icc (0:ℝ) 1
  · exact hD _ (mem_image_of_mem _ ht)
  · rcases not_and_or.mp ht with hl|hr
    · rw [OAI.Analysis.PDE.Green.transition_deriv_zero_left (lt_of_not_ge hl),abs_zero]
      exact hD0
    · rw [OAI.Analysis.PDE.Green.transition_deriv_zero_right (lt_of_not_ge hr),abs_zero]
      exact hD0

theorem halfspaceGapSlope_mul_bound {D L : ℝ} (hD : 0≤D) (hL : 0≤L)
    (hder : ∀t,|deriv Real.smoothTransition t|≤D)
    (n : ℕ) (t z : ℝ) (hz : |z|≤L*|t|) :
    |halfspaceGapSlope n t*z|≤2*D*L := by
  have hn : 0<(n:ℝ)+1 := by positivity
  by_cases ht : ((n:ℝ)+1)*t-1∈Icc (0:ℝ) 1
  · have ht0 : 0<t := by nlinarith [ht.1]
    have ht2 : ((n:ℝ)+1)*t≤2 := by linarith [ht.2]
    rw [halfspaceGapSlope,abs_mul,abs_mul,abs_of_pos hn]
    calc
      _ ≤ ((n:ℝ)+1)*D*(L*|t|) := by gcongr; exact hder _
      _ = (((n:ℝ)+1)*t)*(D*L) := by rw [abs_of_pos ht0]; ring
      _ ≤ 2*(D*L) := mul_le_mul_of_nonneg_right ht2 (mul_nonneg hD hL)
      _ = _ := by ring
  · rcases not_and_or.mp ht with hl|hr
    · simp only [halfspaceGapSlope,OAI.Analysis.PDE.Green.transition_deriv_zero_left (lt_of_not_ge hl),mul_zero,zero_mul,abs_zero]
      positivity
    · simp only [halfspaceGapSlope,OAI.Analysis.PDE.Green.transition_deriv_zero_right (lt_of_not_ge hr),mul_zero,zero_mul,abs_zero]
      positivity

end OAI.Analysis.Normed.Function.Sobolev
