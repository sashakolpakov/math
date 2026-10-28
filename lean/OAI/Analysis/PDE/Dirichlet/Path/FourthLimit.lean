import OAI.Analysis.PDE.Dirichlet.Closed.FourthLimit
import OAI.Analysis.PDE.Dirichlet.Path.LimitData

open Set Module Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

@[instance_reducible]
private def fourthPathHolderNorm (X Y : Type*) [MetricSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (α : ℝ) : Norm (OAI.Analysis.Normed.Function.Holder.HolderMap X Y α) :=
  inferInstance

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance pathFourthFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathFourthFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathFourthSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathFourthHolderNorm {r : E → ℝ} {α : ℝ} :
    Norm (OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α) :=
  fourthPathHolderNorm _ _ α

/-- The existing Banach path limit has interior C⁴ regularity and an actual
closed-domain fourth-derivative Hölder trace whenever the retained smooth
solutions have uniform fourth-jet bounds. No derivative convergence is assumed. -/
theorem BanachPathLimit.exists_closed_fourth_derivative
    (hn : 1 ≤ n) {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {β t : ℝ}
    {s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁}
    (L : BanachPathLimit e lat r B₀ F₀ F₁ hΩD β s t)
    (hr : ContDiff ℝ 3 r) (hB₀ : ContDiff ℝ 4 B₀)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {α C M₀ M₁ M₂ M₃ M₄ : ℝ} (hα : 0 < α)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃) (hM₄ : 0 ≤ M₄)
    (h₀ : ∀ j x, r x ≤ 0 → ‖B₀ x+(s j).u x‖ ≤ M₀)
    (h₁ : ∀ j x, r x ≤ 0 → ‖fderiv ℝ (fun y => B₀ y+(s j).u y) x‖ ≤ M₁)
    (h₂ : ∀ j x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y)) x‖ ≤ M₂)
    (h₃ : ∀ j x, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y))) x‖ ≤ M₃)
    (h₄ : ∀ j x, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+(s j).u y)))) x‖ ≤ M₄)
    (hholder : ∀ j x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z)))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+(s j).u z)))) y‖ ≤ C*dist x y^α) :
    ContDiffOn ℝ 4 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value)) {x | r x < 0} ∧
    ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      ‖Q‖ ≤ max M₄ C ∧ ∀ x (hx : r x < 0),
        OAI.Analysis.Normed.Function.Holder.HolderMap.value Q ⟨x, hx.le⟩ =
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value))))) x := by
  let : NeZero n := ⟨by omega⟩
  have hu (j : ℕ) : ContDiff ℝ 4 (fun x => B₀ x+(s (L.subsequence j)).u x) :=
    hB₀.add ((s (L.subsequence j)).smooth.of_le (by norm_num))
  have hv (x : E) (hx : r x < 0) :
      Tendsto (fun j => B₀ x+(s (L.subsequence j)).u x) atTop
        (𝓝 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value) x)) := by
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.value L.value) (x := x) hx.le]
    exact L.converges ⟨x, hx.le⟩
  exact exists_closed_fourth_derivative_of_uniform_bound hr hreg _ hu _ hv hα
    hM₁ hM₂ hM₃ hM₄ (fun j => h₀ (L.subsequence j)) (fun j => h₁ (L.subsequence j))
    (fun j => h₂ (L.subsequence j)) (fun j => h₃ (L.subsequence j))
    (fun j => h₄ (L.subsequence j)) (fun j => hholder (L.subsequence j))

end OAI.Analysis.PDE.Dirichlet
