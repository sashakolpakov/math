import OAI.Analysis.PDE.Concentration.Cylinder.Volume
import OAI.Analysis.PDE.Concentration.Cylinder.Average
import OAI.Analysis.PDE.Concentration.RadialVolume

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Laplacian InnerProductSpace
open scoped ContDiff

theorem integral_cylinderAverage_le_volume {f : CylinderSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (hn : ∀ x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2, 0 ≤ f x) :
    (∫ r in (1 : ℝ)..2, cylinderAverage f r) ≤
      ∫ x in cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2, f x := by
  have htime : -cylinderTimeEnd ≤ cylinderTimeEnd := by linarith [cylinderTimeEnd_pos]
  have hA := contDiff_cylinderAngularAverage hf
  have hW : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cylinderTimeWeight p.1 * cylinderAngularAverage f p.1 p.2) :=
    (contDiff_cylinderTimeWeight.comp contDiff_fst).mul hA
  have hR : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2 * cylinderAngularAverage f p.1 p.2) :=
    contDiff_snd.mul hA
  have hWi := (contDiff_intervalAverage hW (show (1 : ℝ) ≤ 2 by norm_num)).continuous
  have hRi := (contDiff_intervalAverage hR (show (1 : ℝ) ≤ 2 by norm_num)).continuous
  have hswap : (∫ r in (1 : ℝ)..2, cylinderAverage f r) =
      ∫ t in (-cylinderTimeEnd)..cylinderTimeEnd,
        ∫ r in (1 : ℝ)..2, cylinderTimeWeight t * cylinderAngularAverage f t r := by
    apply intervalIntegral_intervalIntegral_swap
    exact ((hW.comp (contDiff_snd.prodMk contDiff_fst)).continuous.continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  rw [hswap, cylinderShell_integral hf.continuous htime (by norm_num) (by norm_num)]
  apply intervalIntegral.integral_mono_on htime
    (hWi.intervalIntegrable _ _) (hRi.intervalIntegrable _ _)
  intro t ht
  dsimp only
  have hAslice : Continuous (fun r => cylinderAngularAverage f t r) :=
    hA.continuous.comp (continuous_const.prodMk continuous_id)
  have hWslice : Continuous (fun r => cylinderTimeWeight t * cylinderAngularAverage f t r) :=
    continuous_const.mul hAslice
  have hRslice : Continuous (fun r => r * cylinderAngularAverage f t r) := continuous_id.mul hAslice
  apply intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 : ℝ) ≤ 2)
    (hWslice.intervalIntegrable _ _) (hRslice.intervalIntegrable _ _)
  intro r hr
  have hnonneg : 0 ≤ cylinderAngularAverage f t r := by
    apply cylinderAngularAverage_nonneg
    intro θ _
    apply hn
    change cylinderComplexEquiv (cylinderPoint t r θ) ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd ×ˢ
      {z : ℂ | ‖z‖ ∈ Icc 1 2}
    rw [cylinderComplexEquiv_point]
    exact ⟨ht, by simpa only [Set.mem_ofPred_eq, Complex.norm_polarCoord_symm,
      abs_of_nonneg (by linarith [hr.1] : 0 ≤ r)] using hr⟩
  apply mul_le_mul_of_nonneg_right _ hnonneg
  exact (Real.cos_le_one (t / 10)).trans hr.1

theorem exists_cylinder_trace_volume_constant : ∃ C : ℝ, 0 < C ∧
    ∀ f : CylinderSpace → ℝ, ContDiff ℝ ∞ f →
      (∀ x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 3, 0 ≤ f x) →
      (∀ x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 3, Δ f x ≤ 0) →
      cylinderAverage f 1 ≤ C * ∫ x in cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2, f x := by
  obtain ⟨c, hc, htrace⟩ := exists_radial_trace_integral_constant
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro f hf hn hΔ
  have htime : -cylinderTimeEnd ≤ cylinderTimeEnd := by linarith [cylinderTimeEnd_pos]
  have hH := contDiff_cylinderAverage hf
  have hnonneg (r : ℝ) (hr : r ∈ Icc (1 : ℝ) 3) : 0 ≤ cylinderAverage f r := by
    apply cylinderAverage_nonneg
    intro t ht θ _
    exact hn _ (cylinderPoint_mem_shell ht hr (by linarith [hr.1]))
  have hradial (r : ℝ) (hr : r ∈ Ioo (1 : ℝ) 3) : radialHelmholtz (cylinderAverage f) r ≤ 0 := by
    apply cylinderAverage_radialHelmholtz_nonpos hf (by linarith [hr.1] : r ≠ 0)
    · intro t ht θ _
      exact hΔ _ (cylinderPoint_mem_shell ht (Ioo_subset_Icc_self hr) (by linarith [hr.1]))
    · intro θ _
      exact hn _ (cylinderPoint_mem_shell ⟨le_rfl, htime⟩ (Ioo_subset_Icc_self hr) (by linarith [hr.1]))
    · intro θ _
      exact hn _ (cylinderPoint_mem_shell ⟨htime, le_rfl⟩ (Ioo_subset_Icc_self hr) (by linarith [hr.1]))
  have ht := htrace (cylinderAverage f) hH.continuous.continuousOn (hH.of_le (by simp)).contDiffOn
    hradial (hnonneg 1 ⟨le_rfl, by norm_num⟩) (hnonneg 3 ⟨by norm_num, le_rfl⟩)
  have hv := integral_cylinderAverage_le_volume hf (fun x hx => hn x
    ⟨hx.1, hx.2.1, by linarith [hx.2.2]⟩)
  have hh := mul_le_mul_of_nonneg_left (ht.trans hv) (inv_nonneg.mpr hc.le)
  simpa only [inv_mul_cancel_left₀ hc.ne'] using hh

end OAI.Analysis.PDE.Concentration
