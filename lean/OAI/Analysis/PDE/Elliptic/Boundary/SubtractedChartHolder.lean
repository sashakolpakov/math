import OAI.Analysis.PDE.Elliptic.Boundary.Third.ChartHolder
import OAI.Analysis.PDE.Elliptic.Boundary.Third.Subtract

/-! The third-jet norm after flattening and subtraction of fixed boundary
data. Only the original third-jet norm remains as an absorbable error. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I
local instance subChartFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance subChartFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance subChartSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance subChartSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance subChartThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance subChartThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem exists_uniform_subtracted_chart_third_holder
    {Ω K S : Set E} (hΩK : Ω ⊆ K) (hS : IsOpen S) (hSc : Convex ℝ S)
    (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    {G : E → E} (hG : ContDiff ℝ 4 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 4 B₀)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ∀ u : E → ℝ, ContDiff ℝ 3 u →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) →
      ∃ P : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
        (∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x =
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y)-B₀ (G y)))) x) ∧
        ‖P‖ ≤ C*(1+‖U‖+‖T‖) := by
  obtain ⟨C₀, hC₀, hchart⟩ := exists_uniform_chart_third_holder hΩK hS hSc
    hcompact hdiam hG hGK hGΩ hα hα1
  have hb : ContDiff ℝ 4 (fun y => B₀ (G y)) := hB₀.comp hG
  obtain ⟨Q, hQ⟩ := exists_fixed_third_holder hcompact _ hb hα hα1
  refine ⟨C₀+‖Q‖+1, by positivity, ?_⟩
  intro U u hu hU₁ hU₂ T hT
  obtain ⟨P, hP, hPn⟩ := hchart U u hu hU₁ hU₂ T hT
  obtain ⟨V, hv, hn⟩ := exists_subtracted_third_holder
    (hu.comp (hG.of_le (by norm_num))) (hb.of_le (by norm_num)) P Q hP hQ
  exact ⟨V, hv, hn.trans (third_background_bound hC₀.le
    (norm_nonneg Q) (norm_nonneg U) (norm_nonneg T) hPn)⟩

end OAI.Analysis.PDE.Elliptic
