import OAI.Analysis.PDE.Elliptic.Boundary.InverseFourthHolder
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Subtract

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I
local instance inverseSubFourth1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance inverseSubFourth1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance inverseSubFourth2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseSubFourth2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseSubFourth3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseSubFourth3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseSubFourth4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseSubFourth4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [DecidableEq I] in
/-- Restore a fixed smooth boundary datum after returning the fourth-order
estimate from coordinates. Only the fixed datum and chart require C⁵. -/
theorem exists_inverse_subtracted_fourth_holder {S : Set E} (hS : IsCompact S)
    {P : E → E} (hP : ContDiff ℝ 5 P) (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 5 B₀)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ K : Set E, MapsTo P S K → ∀ v u : E → ℝ,
      ContDiff ℝ 4 v → ContDiff ℝ 4 u →
      (∀ x ∈ S, (fun y => v (P y)) =ᶠ[𝓝 x] (fun y => u y-B₀ y)) →
      ∀ N M : ℝ, 0 ≤ N → 0 ≤ M → OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn v K α N →
      (∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ ≤ N) →
      (∀ x ∈ K, ∀ y ∈ K,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ v)) y‖ ≤
          N*‖x-y‖^α) →
      HasFourthHolderBound K α v M → HasFourthHolderBound S α u (C*(1+N+M)) := by
  obtain ⟨C₀,hC₀,hreturn⟩ := exists_inverse_chart_fourth_holder hS hP hα hα1
  obtain ⟨Q,hQ⟩ := exists_fixed_fourth_holder hS B₀ hB₀ hα hα1
  refine ⟨C₀+‖Q‖+1,by positivity,?_⟩
  intro K hPK v u hv hu heq N M hN hM hvb hvn hvh hvfour
  have hreturned := hreturn K hPK v (fun y => u y-B₀ y) hv heq N M hN hM hvb hvn hvh hvfour
  exact (restored_fourth_holder hu (hB₀.of_le (by norm_num)) hreturned Q hQ).mono
    (third_background_bound hC₀.le (norm_nonneg Q) hN hM le_rfl)

end OAI.Analysis.PDE.Elliptic
