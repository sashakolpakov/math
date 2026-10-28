import OAI.Analysis.PDE.Concentration.RadialComparison

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set
open scoped ContDiff

/-- A fixed annular radial integral controls the inner trace of every
nonnegative supersolution. This removes the lower-dimensional trace from
the outer-cylinder mixing problem. -/
theorem exists_radial_trace_integral_constant : ∃ c : ℝ, 0 < c ∧
    ∀ H : ℝ → ℝ, ContinuousOn H (Icc 1 3) → ContDiffOn ℝ 2 H (Ioo 1 3) →
      (∀ r ∈ Ioo 1 3, radialHelmholtz H r ≤ 0) → 0 ≤ H 1 → 0 ≤ H 3 →
      c * H 1 ≤ ∫ r in (1 : ℝ)..2, H r := by
  have hRct : ContinuousOn cylinderRadialBarrier (Icc 1 2) :=
    contDiffOn_cylinderRadialBarrier.continuousOn.mono (fun r hr => by
      change 0 < r
      linarith [hr.1])
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨1, by constructor <;> norm_num⟩ hRct
  have hRz : 0 < cylinderRadialBarrier z := cylinderRadialBarrier_pos (by linarith [hz.1])
    (by linarith [hz.2])
  have hR1 : 0 < cylinderRadialBarrier 1 := cylinderRadialBarrier_pos (by norm_num) (by norm_num)
  refine ⟨cylinderRadialBarrier z / cylinderRadialBarrier 1, div_pos hRz hR1, ?_⟩
  intro H hct hH hL h1 h3
  have hbound := radialHelmholtz_logarithmic_lower (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 3) hct hH hL h1 h3
  have hle (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 2) :
      cylinderRadialBarrier z / cylinderRadialBarrier 1 * H 1 ≤ H r := by
    calc
      _ = H 1 / cylinderRadialBarrier 1 * cylinderRadialBarrier z := by ring
      _ ≤ H 1 / cylinderRadialBarrier 1 * cylinderRadialBarrier r :=
        mul_le_mul_of_nonneg_left (hmin hr) (div_nonneg h1 hR1.le)
      _ ≤ H r := hbound r ⟨hr.1, by linarith [hr.2]⟩
  have hi : IntervalIntegrable H volume 1 2 :=
    (hct.mono (by intro r hr; exact ⟨hr.1, by linarith [hr.2]⟩)).intervalIntegrable_of_Icc (by norm_num)
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 : ℝ) ≤ 2)
    intervalIntegrable_const hi hle
  simpa only [intervalIntegral.integral_const, sub_self, sub_zero, show (2 : ℝ) - 1 = 1 by norm_num,
    one_smul] using hh

end OAI.Analysis.PDE.Concentration
