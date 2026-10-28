import OAI.Analysis.PDE.Nonlinear.FirstJetExtension
import OAI.Analysis.Normed.Function.Holder.Banach.Composition

/-! Smooth maps preserve genuine bounded C¹,α jets. -/

noncomputable section
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

local instance jetCompEFGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance jetCompEFSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance jetCompFGGroup : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
local instance jetCompFGSpace : NormedSpace ℝ (F →L[ℝ] G) := inferInstance
local instance jetCompEGGroup : NormedAddCommGroup (E →L[ℝ] G) := inferInstance
local instance jetCompEGSpace : NormedSpace ℝ (E →L[ℝ] G) := inferInstance

theorem exists_C1_holder_composition {α : ℝ} (hα : 0 ≤ α)
    (f : E → F) (hf : ContDiff ℝ 1 f) (g : F → G) (hg : ContDiff ℝ 2 g)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (D : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] F) α)
    (hV : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = f x) (hD : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ f x) :
    ∃ (W : OAI.Analysis.Normed.Function.Holder.HolderMap E G α) (DW : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] G) α),
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value W x = g (f x)) ∧
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DW x = fderiv ℝ (g ∘ f) x) := by
  obtain ⟨C, hC, hcomp⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound
    (X := E) (f := g) (hg.of_le (by norm_num)) hα (norm_nonneg V)
  obtain ⟨W, hW, _⟩ := hcomp V le_rfl
  obtain ⟨B, hB, hcompD⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound
    (X := E) (f := fderiv ℝ g) (hg.fderiv_right (m := 1) (by norm_num)) hα (norm_nonneg V)
  obtain ⟨DG, hDG, _⟩ := hcompD V le_rfl
  let DW := OAI.Analysis.Normed.Function.Holder.HolderMap.bilinear hα (ContinuousLinearMap.compL ℝ E F G) DG D
  refine ⟨W, DW, ?_, ?_⟩
  · intro x
    rw [hW x, hV x]
  · intro x
    change (OAI.Analysis.Normed.Function.Holder.HolderMap.value DG x).comp (OAI.Analysis.Normed.Function.Holder.HolderMap.value D x) = _
    rw [hDG x, hV x, hD x]
    exact (fderiv_comp x (hg.differentiable (by norm_num) (f x))
      (hf.differentiable one_ne_zero x)).symm

end OAI.Analysis.PDE.Nonlinear
