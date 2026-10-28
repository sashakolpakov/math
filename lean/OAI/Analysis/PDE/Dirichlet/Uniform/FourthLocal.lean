import OAI.Analysis.PDE.Dirichlet.Uniform.LocalHolder
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Tensor

open Set Metric Module
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Elliptic

variable {E P V ι A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance fourthLocal1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthLocal1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthLocal2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthLocal2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthLocal3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthLocal3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthLocal4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthLocal4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Complete globalization of uniform local fourth-order estimates. C⁴,
not C⁵, suffices for the varying solutions. -/
theorem uniform_fourth_holder_of_local
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (u : A → E → ℝ) (hu : ∀ a, ContDiff ℝ 4 (u a)) (hup : ∀ a, LatticePeriodic e b (u a))
    {α : ℝ} (hα : 0 < α)
    (hlocal : ∀ x, r x ≤ 0 → ∃ δ > 0, ∃ C > 0, ∀ a,
      OAI.Analysis.PDE.Elliptic.HasFourthHolderBound (closedBall x δ ∩ {y | r y ≤ 0}) α (u a) C) :
    ∃ M > 0, ∀ a, OAI.Analysis.PDE.Elliptic.HasFourthHolderBound {x | r x ≤ 0} α (u a) M := by
  let g (a : A) := fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u a))))
  have hg (a : A) : Continuous (g a) := by
    have h₁ : ContDiff ℝ 3 (fderiv ℝ (u a)) := (hu a).fderiv_right (by norm_num)
    have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ (u a))) := h₁.fderiv_right (by norm_num)
    have h₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ (u a)))) := h₂.fderiv_right (by norm_num)
    exact h₃.continuous_fderiv one_ne_zero
  have hgp (a : A) : LatticePeriodic e b (g a) := (hup a).fderiv.fderiv.fderiv.fderiv
  apply exists_uniform_periodic_holder_fields_of_local e b hK hr hrp hbounded g hg hgp hα
  intro x hx
  obtain ⟨δ,hδ,C,hC,hlocal⟩ := hlocal x hx
  refine ⟨δ,hδ,C,hC,?_⟩
  intro a y hy hry
  obtain ⟨T,hT,hTn⟩ := hlocal a
  have hv (z) (hz : z ∈ closedBall x δ ∩ {y | r y ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value T ⟨z,hz⟩ = g a z := hT _
  constructor
  · rw [← hv y ⟨hy,hry⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le T _).trans hTn
  · intro z hz hrz
    rw [← hv y ⟨hy,hry⟩,← hv z ⟨hz,hrz⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le T _ _).trans
      (mul_le_mul_of_nonneg_right hTn (Real.rpow_nonneg dist_nonneg _))

end OAI.Analysis.PDE.Dirichlet
