import OAI.Analysis.PDE.Weak.Boundary.H1Chart
import OAI.Analysis.PDE.Weak.Boundary.Chart.Measure

/-! Bounded smooth coordinate neighborhoods give a genuine bounded H¹
pullback without any supplied Jacobian or gradient-transport estimates. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem exists_chartH1Pullback
    {U V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    {G P : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellCoordinates m}
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (hGU : MapsTo G U V) (hPV : MapsTo P V U)
    (hPG : ∀ x ∈ U, P (G x) = x) (hGP : ∀ x ∈ V, G (P x) = x) :
    ∃ T : H1Pair m →L[ℝ] H1Pair m,
      (∀ p, (T p).1 =ᵐ[volume] U.indicator (fun y => p.1 (G y))) ∧
      (∀ p, (T p).2 =ᵐ[volume]
        U.indicator (fun y => chartGradientMap G y (p.2 (G y)))) ∧
      (∀ Ω ⊆ V, ∀ p ∈ H1Zero Ω, T p ∈ H1Zero (U ∩ G ⁻¹' Ω)) := by
  have hUc : IsCompact (closure U) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hUb.closure
  have hVc : IsCompact (closure V) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hVb.closure
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by simp)
  have hP1 : ContDiff ℝ 1 P := hP.of_le (by simp)
  have hd : Continuous (fun y => (fderiv ℝ P y).det) :=
    ContinuousLinearMap.continuous_det.comp (hP1.continuous_fderiv (by norm_num))
  obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuousOn hd.continuousOn
  obtain ⟨M, hM⟩ := hUc.exists_bound_of_continuousOn
    (continuous_chartGradientMap hG1).continuousOn
  have hmap : Measure.map G (volume.restrict U) ≤ ENNReal.ofReal C • volume := by
    apply chart_map_measure_le_of_fderiv volume hU hV hG.continuous
      (hP.differentiable (by simp)) hGU hPV hPG hGP
    intro y hy
    simpa only [Real.norm_eq_abs] using hC y (subset_closure hy)
  have hb : ∀ y ∈ U, ‖chartGradientMap G y‖ ≤ M :=
    fun y hy => hM y (subset_closure hy)
  refine ⟨chartH1Pair U hU.measurableSet G hG1 ENNReal.ofReal_ne_top hmap hb,
    ?_, ?_, ?_⟩
  · exact chartH1Pair_value_ae U hU.measurableSet G hG1 ENNReal.ofReal_ne_top hmap hb
  · exact chartH1Pair_gradient_ae U hU.measurableSet G hG1 ENNReal.ofReal_ne_top hmap hb
  · intro Ω hΩ p hp
    exact OAI.Analysis.PDE.Weak.H1Zero.chart_pullback hU hV hUb hΩ hG hP hGU hPV hPG hGP
      ENNReal.ofReal_ne_top hmap hb hp

end OAI.Analysis.PDE.Weak
