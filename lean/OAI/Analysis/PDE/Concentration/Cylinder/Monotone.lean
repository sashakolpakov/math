import OAI.Analysis.PDE.Concentration.Cylinder.Estimate

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Filter
open scoped ContDiff Topology

theorem cylinderTimeTrace_mono {f g : CylinderSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (ρ : ℝ)
    (hfg : ∀ t ∈ Icc (1 : ℝ) 2, ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      f (cylinderPoint t ρ θ) ≤ g (cylinderPoint t ρ θ)) :
    (∫ t in (1 : ℝ)..2, cylinderAngularAverage f t ρ) ≤
      ∫ t in (1 : ℝ)..2, cylinderAngularAverage g t ρ := by
  have hF : Continuous (fun t => cylinderAngularAverage f t ρ) :=
    (contDiff_cylinderAngularAverage hf).continuous.comp (continuous_id.prodMk continuous_const)
  have hG : Continuous (fun t => cylinderAngularAverage g t ρ) :=
    (contDiff_cylinderAngularAverage hg).continuous.comp (continuous_id.prodMk continuous_const)
  apply intervalIntegral.integral_mono_on (by norm_num)
    (hF.intervalIntegrable _ _) (hG.intervalIntegrable _ _)
  intro t ht
  have hFt : Continuous (fun θ => f (cylinderPoint t ρ θ)) :=
    (contDiff_cylinder_time_angle hf ρ).continuous.comp (continuous_const.prodMk continuous_id)
  have hGt : Continuous (fun θ => g (cylinderPoint t ρ θ)) :=
    (contDiff_cylinder_time_angle hg ρ).continuous.comp (continuous_const.prodMk continuous_id)
  exact intervalIntegral.integral_mono_on (by positivity)
    (hFt.intervalIntegrable _ _) (hGt.intervalIntegrable _ _) (hfg t ht)

theorem cylinderTimeTrace_mono_on {f g : CylinderSpace → ℝ} {U : Set CylinderSpace}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hKU : cylinderShell 1 2 ρ ρ ⊆ U)
    (hfg : ∀ x ∈ cylinderShell 1 2 ρ ρ, f x ≤ g x) :
    (∫ t in (1 : ℝ)..2, cylinderAngularAverage f t ρ) ≤
      ∫ t in (1 : ℝ)..2, cylinderAngularAverage g t ρ := by
  obtain ⟨F, hF, heF⟩ := exists_global_smooth_eq_near_closed
    (isCompact_cylinderShell 1 2 ρ ρ).isClosed hU hKU hf
  obtain ⟨G, hG, heG⟩ := exists_global_smooth_eq_near_closed
    (isCompact_cylinderShell 1 2 ρ ρ).isClosed hU hKU hg
  have heq {p q : CylinderSpace → ℝ}
      (he : ∀ x ∈ cylinderShell 1 2 ρ ρ, p x = q x) :
      (∫ t in (1 : ℝ)..2, cylinderAngularAverage p t ρ) =
        ∫ t in (1 : ℝ)..2, cylinderAngularAverage q t ρ := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (1 : ℝ) 2 := by simpa using ht
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact he _ (cylinderPoint_mem_shell ht' ⟨le_rfl, le_rfl⟩ hρ)
  have hbound := cylinderTimeTrace_mono hF hG ρ (fun t ht θ hθ => by
    have hp := cylinderPoint_mem_shell (θ := θ) ht ⟨le_rfl, le_rfl⟩ hρ
    rw [(heF _ hp).self_of_nhds, (heG _ hp).self_of_nhds]
    exact hfg _ hp)
  rwa [heq (fun x hx => (heF x hx).self_of_nhds),
    heq (fun x hx => (heG x hx).self_of_nhds)] at hbound

end OAI.Analysis.PDE.Concentration
