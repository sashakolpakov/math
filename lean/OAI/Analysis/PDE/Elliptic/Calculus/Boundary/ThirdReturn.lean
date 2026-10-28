import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.ThirdEstimate
import OAI.Analysis.PDE.Schauder.Calculus.ThirdHolderTransport

noncomputable section
open Set Metric
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)
local instance thirdReturnFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdReturnFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdReturnSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdReturnSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdReturnThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdReturnThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Returning the flat estimate through the indexing isometry loses no
constant, either in the third derivative or its Hölder seminorm. -/
theorem third_halfball_estimate_isometry_return
    (e : X ≃ₗᵢ[ℝ] E) (k : Fin m) (u : E → ℝ) (hu : ContDiff ℝ 3 u)
    {δ C α : ℝ}
    (hn : ∀ x ∈ ball 0 δ, 0 ≤ x k → ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x‖ ≤ C)
    (hh : ∀ x ∈ ball 0 δ, 0 ≤ x k → ∀ y ∈ ball 0 δ, 0 ≤ y k →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) x-
        fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e))) y‖ ≤ C*‖x-y‖^α) :
    (∀ x ∈ ball 0 δ, 0 ≤ e.symm x k → ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C) ∧
    ∀ x ∈ ball 0 δ, 0 ≤ e.symm x k → ∀ y ∈ ball 0 δ, 0 ≤ e.symm y k →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤ C*‖x-y‖^α := by
  have hi (x : E) (hx : x ∈ ball 0 δ) : e.symm x ∈ ball 0 δ := by
    simpa only [mem_ball,dist_zero_right,e.symm.norm_map] using hx
  constructor
  · intro x hx hxk
    have h := hn (e.symm x) (hi x hx) hxk
    simpa only [OAI.Analysis.PDE.Schauder.norm_third_isometry_comp e u hu,e.apply_symm_apply] using h
  · intro x hx hxk y hy hyk
    have h := hh (e.symm x) (hi x hx) hxk (e.symm y) (hi y hy) hyk
    simpa only [OAI.Analysis.PDE.Schauder.norm_third_sub_isometry_comp e u hu,e.apply_symm_apply,← map_sub,e.symm.norm_map] using h

end OAI.Analysis.PDE.Elliptic
