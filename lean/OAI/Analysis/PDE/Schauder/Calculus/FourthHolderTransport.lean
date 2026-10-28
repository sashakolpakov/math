import OAI.Analysis.PDE.Schauder.Calculus.FourthIsometry
import OAI.Analysis.Normed.Function.Holder.Boundary.LowerJetHolder

noncomputable section
open Set
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Elliptic

local instance fourthTransport1Group (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthTransport1Space (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthTransport2Group (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTransport2Space (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTransport3Group (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTransport3Space (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTransport4Group (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthTransport4Space (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The full fourth-order Hölder estimate is unchanged by an isometry.
No fifth derivative is required. -/
theorem fourth_holder_isometry (e : E ≃ₗᵢ[ℝ] F) {K : Set F} {α M : ℝ}
    (hα : 0 ≤ α) (u : F → ℝ) (hu : ContDiff ℝ 4 u)
    (h : OAI.Analysis.PDE.Elliptic.HasFourthHolderBound K α u M) :
    OAI.Analysis.PDE.Elliptic.HasFourthHolderBound (e ⁻¹' K) α (u ∘ e) M := by
  obtain ⟨T,hT,hTn⟩ := h
  have hM : 0 ≤ M := (norm_nonneg T).trans hTn
  have hu₁ : ContDiff ℝ 3 (fderiv ℝ (u ∘ e)) := (hu.comp e.contDiff).fderiv_right (by norm_num)
  have hu₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ (u ∘ e))) := hu₁.fderiv_right (by norm_num)
  have hu₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ e)))) := hu₂.fderiv_right (by norm_num)
  apply OAI.Analysis.Normed.Function.Holder.exists_holder_field_of_bounds hα hM _
    (hu₃.continuous_fderiv one_ne_zero).continuousOn
  · intro x hx
    rw [norm_fourth_isometry_comp e u hu,← hT ⟨e x,hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le T _).trans hTn
  · intro x hx y hy
    rw [norm_fourth_sub_isometry_comp e u hu,← hT ⟨e x,hx⟩,← hT ⟨e y,hy⟩]
    have hh := (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le T ⟨e x,hx⟩ ⟨e y,hy⟩).trans
      (mul_le_mul_of_nonneg_right hTn (Real.rpow_nonneg dist_nonneg _))
    simpa only [Subtype.dist_eq,e.isometry.dist_eq,dist_eq_norm] using hh

end OAI.Analysis.PDE.Schauder
