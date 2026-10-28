import OAI.Analysis.PDE.Concentration.OuterRegion
import OAI.Analysis.PDE.Concentration.Cylinder.Trace

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian Filter
open scoped ContDiff Topology

/-- Every point of the fixed outer annulus controls the weighted radius-one
cylinder trace of a nonnegative superharmonic function. -/
theorem exists_outer_trace_constant : ∃ D : ℝ, 0 < D ∧
    ∀ f : CylinderSpace → ℝ, ContDiffOn ℝ ∞ f outerAnnulus →
      (∀ x ∈ outerAnnulus, 0 ≤ f x) → (∀ x ∈ outerAnnulus, Δ f x ≤ 0) →
      ∀ x ∈ cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2,
        cylinderAverage f 1 ≤ D * f x := by
  obtain ⟨C, hC, htrace⟩ := exists_cylinder_trace_volume_constant
  obtain ⟨M, hM, hmix⟩ := exists_outerShell_mixing_constant (-cylinderTimeEnd) cylinderTimeEnd
  refine ⟨C * M, mul_pos hC hM, ?_⟩
  intro f hf hn hΔ
  let K := cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 3
  have hK : IsCompact K := isCompact_cylinderShell _ _ _ _
  have hKU : K ⊆ outerAnnulus := by
    intro x hx
    have hlo := hx.2.1
    have hhi := hx.2.2
    change 1 / 2 < ‖(cylinderComplexEquiv x).2‖ ∧ ‖(cylinderComplexEquiv x).2‖ < 4
    constructor <;> linarith
  obtain ⟨F, hF, he⟩ := exists_global_smooth_eq_near_closed hK.isClosed isOpen_outerAnnulus hKU hf
  have hpoint {t r θ : ℝ} (ht : t ∈ Icc (-cylinderTimeEnd) cylinderTimeEnd) (hr : r ∈ Icc (1 : ℝ) 3) :
      F (cylinderPoint t r θ) = f (cylinderPoint t r θ) :=
    (he _ (cylinderPoint_mem_shell ht hr (by linarith [hr.1]))).self_of_nhds
  have havg : cylinderAverage F 1 = cylinderAverage f 1 :=
    cylinderAverage_congr (fun t ht θ _ => hpoint ht ⟨le_rfl, by norm_num⟩)
  have hsmall : cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2 ⊆ K := by
    intro x hx
    exact ⟨hx.1, hx.2.1, by linarith [hx.2.2]⟩
  have hint : (∫ x in cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2, F x) =
      ∫ x in cylinderShell (-cylinderTimeEnd) cylinderTimeEnd 1 2, f x :=
    setIntegral_congr_fun (isCompact_cylinderShell _ _ _ _).measurableSet
      (fun x hx => (he x (hsmall hx)).self_of_nhds)
  have hbound := htrace F hF
    (fun x hx => by rw [(he x hx).self_of_nhds]; exact hn x (hKU hx))
    (fun x hx => by
      rw [(laplacian_congr_nhds (he x hx)).self_of_nhds]
      exact hΔ x (hKU hx))
  rw [havg, hint] at hbound
  intro x hx
  exact hbound.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hmix f hf hn hΔ x hx) hC.le)

end OAI.Analysis.PDE.Concentration
