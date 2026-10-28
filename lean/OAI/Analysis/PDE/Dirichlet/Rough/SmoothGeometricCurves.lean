import OAI.Analysis.PDE.Dirichlet.Rough.GeometricCurves

noncomputable section
open Set Filter Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

def HasSmoothGeometricSolutionCurves
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (r ψ B : E → ℝ)
    (hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}) (α : ℝ) : Prop :=
  ∀ D : PeriodicDomainDeformation e b r,
    ∃ U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ContDiffAt ℝ ∞ U 0 ∧
      ∀ᶠ t in 𝓝 0, ∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) x = ψ (D.map (t,x)) - B (D.map (t,x))

omit [Fintype ι] in
theorem HasSmoothGeometricSolutionCurves.to_two
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r ψ B : E → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (h : HasSmoothGeometricSolutionCurves e b r ψ B hΩD α) :
    HasGeometricSolutionCurves e b r ψ B hΩD α := by
  intro D
  obtain ⟨U,hU,he⟩ := h D
  exact ⟨U,hU.of_le (by simp),he⟩

end OAI.Analysis.PDE.Dirichlet
