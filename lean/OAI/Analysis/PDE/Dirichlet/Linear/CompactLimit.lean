import OAI.Analysis.Normed.Function.Holder.C2HolderStrongLimit
import OAI.Analysis.Normed.Function.Holder.C2HolderLattice

open Set Module Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α M : ℝ}

local instance linearLimitFirstNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance linearLimitFirstNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance linearLimitSecondNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance linearLimitSecondNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [Fintype ι] in
/-- Passing to an approximating-data limit preserves the actual linear
equation, zero boundary values, periodicity, and the original Schauder bound.
Only convergence uses the lower exponent. -/
theorem exists_linear_dirichlet_solution_of_lowerHalf_limit
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) (hα : 0 ≤ α) (hM : 0 ≤ M)
    (A : K → (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (f : ℕ → K → ℝ) (f₀ : K → ℝ)
    (hf : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (f₀ x)))
    (Φ : ℕ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hΦ : ∀ j, ‖Φ j‖ ≤ M)
    (hmem : ∀ j, Φ j ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat)
    (heq : ∀ j x, A x (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ j) x) = f j x)
    (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (α / 2))
    (hlim : Tendsto (fun j ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα (Φ j)) atTop (𝓝 g)) :
    ∃ u : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ‖u‖ ≤ M ∧
      u ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      (∀ x, A x (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative u x) = f₀ x) ∧
      OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα u = g := by
  obtain ⟨u, hu, hug⟩ :=
    OAI.Analysis.Normed.Function.Holder.C2Holder.exists_original_exponent_of_lowerHalf_limit hα hM Φ g hΦ hlim
  have hmem' : ∀ j, OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα (Φ j) ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat := by
    intro j
    exact hmem j
  have hg : g ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat :=
    (OAI.Analysis.Normed.Function.Holder.C2Holder.isClosed_latticeDirichlet e lat).mem_of_tendsto hlim
      (Eventually.of_forall hmem')
  have humem : u ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat := by
    rw [← hug] at hg
    exact hg
  refine ⟨u, hu, humem, ?_, hug⟩
  intro x
  have hH : Tendsto (fun j ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ j) x) atTop
      (𝓝 (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x)) := by
    simpa only [OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_lowerHalf] using OAI.Analysis.Normed.Function.Holder.C2Holder.jet_second_tendsto hlim x
  have hA := ((A x).continuous.tendsto (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x)).comp hH
  have heqg : A x (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x) = f₀ x := by
    apply tendsto_nhds_unique hA
    simpa only [Function.comp_def, heq] using hf x
  simpa only [← hug, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_lowerHalf] using heqg

end OAI.Analysis.PDE.Dirichlet
