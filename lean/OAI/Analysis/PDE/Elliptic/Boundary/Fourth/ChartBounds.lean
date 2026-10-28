import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.ChartJets

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
local instance fourthBound1Group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance fourthBound1Space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance fourthBound2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthBound2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthBound3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthBound3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthBound4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthBound4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem exists_bounded_fourth_chart_jets {S : Set E} (hS : IsCompact S)
    {P : E → E} (hP : ContDiff ℝ 5 P) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
      (K : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
      (L : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
      (V : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α),
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ P x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value K x = fderiv ℝ (fderiv ℝ P) x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value L x = fderiv ℝ (fderiv ℝ (fderiv ℝ P)) x) ∧
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ P))) x) ∧
      ‖J‖ ≤ A ∧ ‖K‖ ≤ A ∧ ‖L‖ ≤ A ∧ ‖V‖ ≤ A := by
  obtain ⟨J,K,L,V,hJ,hK,hL,hV⟩ := exists_fixed_compact_fourth_chart_jets hS hP hα hα1
  let A := 1+‖J‖+‖K‖+‖L‖+‖V‖
  have hA : 1 ≤ A := by dsimp only [A]; linarith [norm_nonneg J,norm_nonneg K,norm_nonneg L,norm_nonneg V]
  refine ⟨A,hA,J,K,L,V,hJ,hK,hL,hV,?_,?_,?_,?_⟩
  · dsimp only [A]; linarith [norm_nonneg K,norm_nonneg L,norm_nonneg V]
  · dsimp only [A]; linarith [norm_nonneg J,norm_nonneg L,norm_nonneg V]
  · dsimp only [A]; linarith [norm_nonneg J,norm_nonneg K,norm_nonneg V]
  · dsimp only [A]; linarith [norm_nonneg J,norm_nonneg K,norm_nonneg L]

end OAI.Analysis.PDE.Elliptic
