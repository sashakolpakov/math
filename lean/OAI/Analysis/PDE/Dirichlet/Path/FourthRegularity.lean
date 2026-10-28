import OAI.Analysis.PDE.Dirichlet.Closed.FourthRegularity
import OAI.Analysis.PDE.Dirichlet.Path.ThirdLimit
import OAI.Analysis.PDE.Dirichlet.Path.FourthLimit

open Set Module Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance pathFourthRegFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathFourthRegFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathFourthRegSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthRegSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthRegThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthRegThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthRegFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthRegFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Uniform closed third/fourth jet estimates upgrade the actual Banach
path limit to C⁴ on the entire closed physical domain. -/
theorem BanachPathLimit.contDiffOn_four_closed
    (hn : 1 ≤ n) {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {β t : ℝ}
    {s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁}
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩD β s t)
    (hr : ContDiff ℝ 3 r) (hB₀ : ContDiff ℝ 4 B₀)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {α C₃ C₄ M₀ M₁ M₂ M₃ M₄ : ℝ} (hα : 0 < α)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃) (hM₄ : 0 ≤ M₄)
    (h₀ : ∀ j x, r x ≤ 0 → ‖B₀ x+(s j).u x‖ ≤ M₀)
    (h₁ : ∀ j x, r x ≤ 0 → ‖fderiv ℝ (fun y => B₀ y+(s j).u y) x‖ ≤ M₁)
    (h₂ : ∀ j x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y)) x‖ ≤ M₂)
    (h₃ : ∀ j x, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y))) x‖ ≤ M₃)
    (h₄ : ∀ j x, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y)))) x‖ ≤ M₄)
    (hholder₃ : ∀ j x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z))) y‖ ≤ C₃*dist x y^α)
    (hholder₄ : ∀ j x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z)))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z)))) y‖ ≤ C₄*dist x y^α) :
    ContDiffOn ℝ 4 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) {x | r x ≤ 0} := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨T, _, hT⟩ := L.exists_closed_third_derivative hn hr
    (hB₀.of_le (by norm_num)) hreg hα hM₁ hM₂ hM₃ h₀ h₁ h₂ h₃ hholder₃
  obtain ⟨hv, Q, _, hQ⟩ := L.exists_closed_fourth_derivative hn hr hB₀ hreg
    hα hM₁ hM₂ hM₃ hM₄ h₀ h₁ h₂ h₃ h₄ hholder₄
  exact OAI.Analysis.PDE.Dirichlet.C2Holder.contDiffOn_four_closed_of_traces hr hreg L.value hv
    (OAI.Analysis.Normed.Function.Holder.HolderMap.value T) (OAI.Analysis.Normed.Function.Holder.HolderMap.value Q) hT hQ

end OAI.Analysis.PDE.Dirichlet
