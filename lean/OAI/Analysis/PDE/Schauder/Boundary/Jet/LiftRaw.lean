import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftData
import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftFirst

noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder
variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance rawFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance rawFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance rawSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance rawSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem boundaryLiftRegularization_value_eq (e : E) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α)
    (a : BoundaryLiftRegularization (innerSL ℝ e) α)
    (ha : a.s = fun x ↦ regularizedTrace (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) (inner ℝ e x) (normalProjection e x)) :
    a.value = regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) := by
  ext x
  simp only [OAI.Analysis.PDE.Schauder.BoundaryLiftRegularization.value, regularizedBoundaryLift, ha]
  rfl

theorem contDiff_regularizedBoundaryLift (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) :
    ContDiff ℝ 2 (regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h)) := by
  obtain ⟨a, ha, _⟩ := exists_boundaryLiftRegularization hα.le e he h
  have hℓ : ‖innerSL ℝ e‖ ≤ 1 := by rw [innerSL_apply_norm, he]
  rw [← boundaryLiftRegularization_value_eq e h a ha]
  exact a.contDiff_value hℓ hα hαone

theorem exists_regularizedBoundaryLift_hessian_holder (hα : 0 < α) (hαone : α < 1)
    (e : E) (he : ‖e‖ = 1) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) :
    ∃ C ≥ 0, ∀ x y,
      ‖fderiv ℝ (fderiv ℝ (regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h))) x -
        fderiv ℝ (fderiv ℝ (regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h))) y‖ ≤
        C * ‖x - y‖ ^ α := by
  obtain ⟨a, ha, _⟩ := exists_boundaryLiftRegularization hα.le e he h
  have hℓ : ‖innerSL ℝ e‖ ≤ 1 := by rw [innerSL_apply_norm, he]
  have hn : 0 ≤ a.holderConstant := by
    dsimp only [OAI.Analysis.PDE.Schauder.BoundaryLiftRegularization.holderConstant]
    have h0 := a.nonneg_C0
    have h1 := a.nonneg_C1
    have h2 := a.nonneg_C2
    have h3 := a.nonneg_C3
    have hH := a.nonneg_H
    positivity
  refine ⟨a.holderConstant, hn, ?_⟩
  rw [← boundaryLiftRegularization_value_eq e h a ha, a.fderiv_fderiv_value hℓ hα]
  exact a.second_holder hℓ hα hαone

theorem fderiv_fderiv_regularizedBoundaryLift_boundary (hα : 0 < α)
    (e : E) (he : ‖e‖ = 1) (h : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) (x : E)
    (hx : inner ℝ e x = 0) :
    fderiv ℝ (fderiv ℝ (regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h))) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value h x • (innerSL ℝ e).smulRight (innerSL ℝ e) := by
  obtain ⟨a, ha, hb⟩ := exists_boundaryLiftRegularization hα.le e he h
  have hℓ : ‖innerSL ℝ e‖ ≤ 1 := by rw [innerSL_apply_norm, he]
  rw [← boundaryLiftRegularization_value_eq e h a ha, a.fderiv_fderiv_value hℓ hα]
  change liftSecondJet (innerSL ℝ e) a.s a.D a.DD x = _
  rw [liftSecondJet_boundary _ _ _ _ hx]
  have hs := eq_boundary_of_scale_error (innerSL ℝ e) a.s a.b hα a.error hx
  rw [hs, hb]
  simp only [normalProjection, hx, zero_smul, sub_zero]

end OAI.Analysis.PDE.Schauder
