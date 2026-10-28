import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Germ
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderPullback

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance fourthRestriction1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthRestriction1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthRestriction2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthRestriction2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthRestriction3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthRestriction3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthRestriction4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthRestriction4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem HasFourthHolderBound.restrict {S K : Set E} {α M : ℝ} {u : E → ℝ}
    (h : HasFourthHolderBound K α u M) (hSK : S ⊆ K) (hα : 0 ≤ α) :
    HasFourthHolderBound S α u M := by
  obtain ⟨T,hT,hTn⟩ := h
  let g : S → K := fun x => ⟨x,hSK x.property⟩
  have hg : Isometry g := fun x y => rfl
  exact ⟨OAI.Analysis.PDE.Schauder.holderIsometricPullback hα g hg T,fun x => hT (g x),
    (OAI.Analysis.PDE.Schauder.norm_holderIsometricPullback_le hα g hg T).trans hTn⟩

end OAI.Analysis.PDE.Elliptic
