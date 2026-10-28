import OAI.Analysis.PDE.Dirichlet.Periodic.HigherJet

/-! Fixed smooth periodic fields provide bounded Hölder jets before any
unknown solution is chosen. -/
noncomputable section
open Set Module
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E F P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local instance fieldDataFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance fieldDataFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance fieldDataSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance fieldDataSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance fieldDataThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance fieldDataThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance

theorem exists_periodic_field_four_jets
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (f : E → F) (hf : ContDiff ℝ 4 f) (hfp : LatticePeriodic e b f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ R > 0,
      ∃ (V0 : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
        (V1 : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] F) α)
        (V2 : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] F) α)
        (V3 : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) α),
        ‖V0‖ ≤ R ∧ ‖V1‖ ≤ R ∧ ‖V2‖ ≤ R ∧ ‖V3‖ ≤ R ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V0 x = f x) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V1 x = fderiv ℝ f x) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V2 x = fderiv ℝ (fderiv ℝ f) x) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V3 x = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x) := by
  have h1 : ContDiff ℝ 3 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ f)) := h1.fderiv_right (by norm_num)
  have h3 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ f))) := h2.fderiv_right (by norm_num)
  obtain ⟨V0,hV0⟩ := exists_periodic_holder_field e b hK hr hrp hbounded f
    (hf.of_le (by norm_num)) hfp hα hα1
  obtain ⟨V1,hV1⟩ := exists_periodic_holder_field e b hK hr hrp hbounded _
    (h1.of_le (by norm_num)) hfp.fderiv hα hα1
  obtain ⟨V2,hV2⟩ := exists_periodic_holder_field e b hK hr hrp hbounded _
    (h2.of_le (by norm_num)) hfp.fderiv.fderiv hα hα1
  obtain ⟨V3,hV3⟩ := exists_periodic_holder_field e b hK hr hrp hbounded _ h3
    hfp.fderiv.fderiv.fderiv hα hα1
  refine ⟨1+‖V0‖+‖V1‖+‖V2‖+‖V3‖,by positivity,V0,V1,V2,V3,?_,?_,?_,?_,hV0,hV1,hV2,hV3⟩
  all_goals linarith [norm_nonneg V0,norm_nonneg V1,norm_nonneg V2,norm_nonneg V3]

end OAI.Analysis.PDE.Dirichlet
