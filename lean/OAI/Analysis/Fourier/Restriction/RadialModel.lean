import OAI.Analysis.Fourier.Restriction.FarField
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open _root_.MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem exists_rpow_local_lipschitz (β : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s ∈ Icc (1 / 2 : ℝ) (3 / 2),
      |s ^ β - 1| ≤ L * |s - 1| ∧ |s ^ β| ≤ 1 + L := by
  have hd : ContDiffOn ℝ 1 (fun s : ℝ ↦ s ^ β) (Icc (1 / 2 : ℝ) (3 / 2)) := by
    apply contDiffOn_id.rpow_const_of_ne
    intro s hs
    change s ≠ 0
    linarith [hs.1]
  obtain ⟨L, hL⟩ := hd.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  refine ⟨L, L.coe_nonneg, ?_⟩
  intro s hs
  have H : |s ^ β - 1| ≤ (L : ℝ) * |s - 1| := by
    simpa only [Real.dist_eq, Real.one_rpow] using hL.dist_le_mul s hs 1 (by norm_num)
  refine ⟨H, ?_⟩
  have J : |s - 1| ≤ 1 := abs_le.mpr (by constructor <;> linarith [hs.1, hs.2])
  have K := abs_add_le (s ^ β - 1) (1 : ℝ)
  have H' := H.trans (mul_le_mul_of_nonneg_left J L.coe_nonneg)
  simp only [sub_add_cancel, abs_one] at K
  linarith

def radialOscillation (A B t : ℝ) : ℝ := A * Real.cos t + B * Real.sin t

theorem abs_radialOscillation_le (A B t : ℝ) :
    |radialOscillation A B t| ≤ |A| + |B| := by
  unfold radialOscillation
  calc
    _ ≤ |A * Real.cos t| + |B * Real.sin t| := abs_add_le _ _
    _ = |A| * |Real.cos t| + |B| * |Real.sin t| := by simp only [abs_mul]
    _ ≤ |A| * 1 + |B| * 1 := add_le_add
      (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _))
    _ = _ := by ring

theorem radialOscillation_lipschitz (A B s t : ℝ) :
    |radialOscillation A B s - radialOscillation A B t| ≤
      (|A| + |B|) * |s - t| := by
  have he : radialOscillation A B s - radialOscillation A B t =
      A * (Real.cos s - Real.cos t) + B * (Real.sin s - Real.sin t) := by
    unfold radialOscillation
    ring
  rw [he]
  calc
    _ ≤ |A * (Real.cos s - Real.cos t)| + |B * (Real.sin s - Real.sin t)| := abs_add_le _ _
    _ = |A| * |Real.cos s - Real.cos t| + |B| * |Real.sin s - Real.sin t| := by
      simp only [abs_mul]
    _ ≤ |A| * |s - t| + |B| * |s - t| := add_le_add
      (mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le _ _) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) (abs_nonneg _))
    _ = _ := by ring

end OAI.Analysis.Fourier.Restriction
