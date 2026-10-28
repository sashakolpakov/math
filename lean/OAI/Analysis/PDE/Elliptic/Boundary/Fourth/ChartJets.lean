import OAI.Analysis.Normed.Function.Holder.Boundary.LowerJetHolder

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

local instance fourthFixed1Group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance fourthFixed1Space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance fourthFixed2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthFixed2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthFixed3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthFixed3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthFixed4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthFixed4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- The fixed smooth coordinate map supplies all four Hölder coefficient
fields on an arbitrary compact patch, with no convexity requirement. -/
theorem exists_fixed_compact_fourth_chart_jets {S : Set E} (hS : IsCompact S)
    {P : E → E} (hP : ContDiff ℝ 5 P) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
      (K : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
      (L : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
      (V : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α),
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ P x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value K x = fderiv ℝ (fderiv ℝ P) x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value L x = fderiv ℝ (fderiv ℝ (fderiv ℝ P)) x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ P))) x) := by
  have h₁ : ContDiff ℝ 4 (fderiv ℝ P) := hP.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 3 (fderiv ℝ (fderiv ℝ P)) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ (fderiv ℝ P))) := h₂.fderiv_right (by norm_num)
  have h₄ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ P)))) := h₃.fderiv_right (by norm_num)
  obtain ⟨J,hJ⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact hS _ (h₁.of_le (by norm_num)) hα hα1
  obtain ⟨K,hK⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact hS _ (h₂.of_le (by norm_num)) hα hα1
  obtain ⟨L,hL⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact hS _ (h₃.of_le (by norm_num)) hα hα1
  obtain ⟨V,hV⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact hS _ h₄ hα hα1
  exact ⟨J,K,L,V,hJ,hK,hL,hV⟩

end OAI.Analysis.PDE.Elliptic
