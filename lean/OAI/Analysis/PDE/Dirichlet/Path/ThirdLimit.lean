import OAI.Analysis.PDE.Dirichlet.Closed.ThirdLimit
import OAI.Analysis.PDE.Dirichlet.Path.LimitData

open Set Module Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance pathThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Uniform bounds on the retained smooth solutions give a genuine
closed-domain third-derivative trace for the existing Banach path limit.
No convergence of third derivatives is assumed. -/
theorem BanachPathLimit.exists_closed_third_derivative
    (hn : 1 ≤ n) {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {β t : ℝ}
    {s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁}
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩD β s t)
    (hr : ContDiff ℝ 3 r) (hB₀ : ContDiff ℝ 3 B₀)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {α C M₀ M₁ M₂ M₃ : ℝ} (hα : 0 < α)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (h₀ : ∀ j x, r x ≤ 0 → ‖B₀ x+(s j).u x‖ ≤ M₀)
    (h₁ : ∀ j x, r x ≤ 0 → ‖fderiv ℝ (fun y => B₀ y+(s j).u y) x‖ ≤ M₁)
    (h₂ : ∀ j x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y)) x‖ ≤ M₂)
    (h₃ : ∀ j x, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y))) x‖ ≤ M₃)
    (hholder : ∀ j x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z))) y‖ ≤ C*dist x y^α) :
    ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      ‖T‖ ≤ max M₃ C ∧ ∀ x (hx : r x < 0),
        OAI.Analysis.Normed.Function.Holder.HolderMap.value T ⟨x, hx.le⟩ =
          fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)))) x := by
  let : NeZero n := ⟨by omega⟩
  have hu (j : ℕ) : ContDiff ℝ 3 (fun x => B₀ x+(s (L.subsequence j)).u x) :=
    hB₀.add ((s (L.subsequence j)).smooth.of_le (by norm_num))
  have hv (x : E) (hx : r x < 0) :
      Tendsto (fun j => B₀ x+(s (L.subsequence j)).u x) atTop
        (𝓝 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value) x)) := by
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value) (x := x) hx.le]
    exact L.converges ⟨x, hx.le⟩
  exact (exists_closed_third_derivative_of_uniform_bound hr hreg _ hu _ hv hα
    hM₁ hM₂ hM₃ (fun j => h₀ (L.subsequence j)) (fun j => h₁ (L.subsequence j))
    (fun j => h₂ (L.subsequence j)) (fun j => h₃ (L.subsequence j))
    (fun j => hholder (L.subsequence j))).2

end OAI.Analysis.PDE.Dirichlet
