import OAI.Analysis.PDE.Elliptic.Boundary.InverseThirdHolder
import OAI.Analysis.PDE.Elliptic.Boundary.Third.Subtract

/-! Restoring the fixed boundary datum after returning a local estimate
through the inverse chart. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I
local instance inverseSubFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance inverseSubFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance inverseSubSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseSubSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseSubThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseSubThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem exists_inverse_subtracted_third_holder {S : Set E} (hS : IsCompact S)
    {P : E → E} (hP : ContDiff ℝ 4 P) (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 4 B₀)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, ∀ K : Set E, MapsTo P S K → ∀ v u : E → ℝ,
      ContDiff ℝ 3 v → ContDiff ℝ 3 u →
      (∀ x ∈ S, (fun y => v (P y)) =ᶠ[𝓝 x] (fun y => u y-B₀ y)) →
      ∀ N M : ℝ, 0 ≤ N → 0 ≤ M → OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn v K α N →
      (∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x‖ ≤ M) →
      (∀ x ∈ K, ∀ y ∈ K,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ v)) y‖ ≤
          M*‖x-y‖^α) →
      ∃ U : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
        (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) ∧
        ‖U‖ ≤ C*(1+N+M) := by
  obtain ⟨C₀, hC₀, hreturn⟩ := exists_inverse_chart_third_holder hS hP hα hα1
  obtain ⟨Q, hQ⟩ := exists_fixed_third_holder hS B₀ hB₀ hα hα1
  refine ⟨C₀+‖Q‖+1, by positivity, ?_⟩
  intro K hPK v u hv hu heq N M hN hM hvb hvn hvh
  obtain ⟨T, hT, hTn⟩ := hreturn K hPK v (fun y => u y-B₀ y) hv heq N M hN hM hvb hvn hvh
  obtain ⟨V, hV, hn⟩ := exists_restored_third_holder hu (hB₀.of_le (by norm_num)) T Q hT hQ
  exact ⟨V, hV, hn.trans (third_background_bound hC₀.le (norm_nonneg Q) hN hM hTn)⟩

end OAI.Analysis.PDE.Elliptic
