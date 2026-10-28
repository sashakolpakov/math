import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Tensor

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance fourthGerm1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthGerm1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthGerm2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthGerm2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthGerm3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthGerm3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthGerm4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthGerm4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem HasFourthHolderBound.congr_germ {S : Set E} {α M : ℝ} {u v : E → ℝ}
    (h : HasFourthHolderBound S α u M) (heq : ∀ x ∈ S, u =ᶠ[𝓝 x] v) :
    HasFourthHolderBound S α v M := by
  obtain ⟨T,hT,hTn⟩ := h
  refine ⟨T,?_,hTn⟩
  intro x
  exact (hT x).trans (heq x x.property).fderiv.fderiv.fderiv.fderiv_eq

end OAI.Analysis.PDE.Elliptic
