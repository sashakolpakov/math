import OAI.Analysis.PDE.Concentration.Cylinder.Average
import OAI.Analysis.PDE.Concentration.Cylinder.Volume
import OAI.Analysis.PDE.Concentration.SmoothExtension

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Filter
open scoped ContDiff Topology

theorem cylinderTimeWeight_half_le {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    (1 / 2 : ℝ) ≤ cylinderTimeWeight t := by
  have h := Real.one_sub_sq_div_two_le_cos (x := t / 10)
  have ht2 : t ^ 2 ≤ 4 := by nlinarith [ht.1, ht.2]
  dsimp [cylinderTimeWeight]
  nlinarith

theorem time_integral_le_weighted_integral {g : ℝ → ℝ} (hg : Continuous g)
    (hn : ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd, 0 ≤ g t) :
    (∫ t in (1 : ℝ)..2, g t) ≤
      2 * ∫ t in (-cylinderTimeEnd)..cylinderTimeEnd, cylinderTimeWeight t * g t := by
  have hleft : -cylinderTimeEnd ≤ (1 : ℝ) := by
    dsimp [cylinderTimeEnd]; nlinarith [Real.pi_pos]
  have hright : (2 : ℝ) ≤ cylinderTimeEnd := by
    dsimp [cylinderTimeEnd]; nlinarith [Real.pi_gt_three]
  have hwg : Continuous (fun t => cylinderTimeWeight t * g t) :=
    contDiff_cylinderTimeWeight.continuous.mul hg
  have hsmall : (∫ t in (1 : ℝ)..2, g t) ≤
      ∫ t in (1 : ℝ)..2, 2 * (cylinderTimeWeight t * g t) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hg.intervalIntegrable _ _)
      ((continuous_const.mul hwg).intervalIntegrable _ _)
    intro t ht
    change g t ≤ 2 * (cylinderTimeWeight t * g t)
    have hgt := hn t ⟨hleft.trans ht.1, ht.2.trans hright⟩
    have hw := cylinderTimeWeight_half_le ht
    nlinarith [mul_le_mul_of_nonneg_right hw hgt]
  rw [intervalIntegral.integral_const_mul] at hsmall
  have hlarge : (∫ t in (1 : ℝ)..2, cylinderTimeWeight t * g t) ≤
      ∫ t in (-cylinderTimeEnd)..cylinderTimeEnd, cylinderTimeWeight t * g t := by
    apply intervalIntegral.integral_mono_interval hleft (by norm_num) hright _
      (hwg.intervalIntegrable _ _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (cylinderTimeWeight_nonneg ⟨ht.1.le, ht.2⟩) (hn t ⟨ht.1.le, ht.2⟩)
  linarith

theorem cylinderTimeTrace_le_average {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f) (ρ : ℝ)
    (hn : ∀ t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd,
      ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), 0 ≤ f (cylinderPoint t ρ θ)) :
    (∫ t in (1 : ℝ)..2, cylinderAngularAverage f t ρ) ≤ 2 * cylinderAverage f ρ := by
  have hg : Continuous (fun t => cylinderAngularAverage f t ρ) :=
    (contDiff_cylinderAngularAverage hf).continuous.comp (continuous_id.prodMk continuous_const)
  exact time_integral_le_weighted_integral hg
    (fun t ht => cylinderAngularAverage_nonneg (hn t ht))

theorem cylinderTimeTrace_le_average_on {f : CylinderSpace → ℝ} {U : Set CylinderSpace}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hKU : cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ ρ ⊆ U)
    (hn : ∀ x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ ρ, 0 ≤ f x) :
    (∫ t in (1 : ℝ)..2, cylinderAngularAverage f t ρ) ≤ 2 * cylinderAverage f ρ := by
  let K := cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ ρ
  obtain ⟨F, hF, he⟩ := exists_global_smooth_eq_near_closed
    (isCompact_cylinderShell (-cylinderTimeEnd) cylinderTimeEnd ρ ρ).isClosed hU hKU hf
  have hpoint {t θ : ℝ} (ht : t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd) :
      F (cylinderPoint t ρ θ) = f (cylinderPoint t ρ θ) :=
    (he _ (cylinderPoint_mem_shell ht ⟨le_rfl, le_rfl⟩ hρ)).self_of_nhds
  have hbound := cylinderTimeTrace_le_average hF ρ (fun t ht θ hθ => by
    rw [hpoint ht]
    exact hn _ (cylinderPoint_mem_shell ht ⟨le_rfl, le_rfl⟩ hρ))
  have hmean : cylinderAverage F ρ = cylinderAverage f ρ :=
    cylinderAverage_congr (fun t ht θ hθ => hpoint ht)
  have htrace : (∫ t in (1 : ℝ)..2, cylinderAngularAverage F t ρ) =
      ∫ t in (1 : ℝ)..2, cylinderAngularAverage f t ρ := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (1 : ℝ) 2 := by simpa using ht
    have htL : t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd := by
      dsimp [cylinderTimeEnd]
      constructor <;> nlinarith [Real.pi_gt_three, ht'.1, ht'.2]
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact hpoint htL
  rwa [hmean, htrace] at hbound

end OAI.Analysis.PDE.Concentration
