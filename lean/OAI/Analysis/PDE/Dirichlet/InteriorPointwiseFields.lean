import OAI.Analysis.PDE.Schauder.Dirichlet.EuclideanChartEquation
import OAI.Analysis.PDE.Nonlinear.Average

open Set Metric
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bounded Hölder datum on a closed ball has a global representative
with the same norm bound. Continuity is derived from the Hölder estimate. -/
theorem exists_closedBall_holder_field (x₀ : E) {ρ α N : ℝ}
    (hρ : 0 ≤ ρ) (hα : 0 < α) (hN : 0 ≤ N) (f : E → F)
    (hn : ∀ x ∈ closedBall x₀ ρ, ‖f x‖ ≤ N)
    (hh : ∀ x ∈ closedBall x₀ ρ, ∀ y ∈ closedBall x₀ ρ,
      ‖f x - f y‖ ≤ N * ‖x-y‖^α) :
    ∃ g : OAI.Analysis.Normed.Function.Holder.HolderMap E F α,
      (∀ x ∈ closedBall x₀ ρ, OAI.Analysis.Normed.Function.Holder.HolderMap.value g x = f x) ∧ ‖g‖ ≤ N := by
  let S := closedBall x₀ ρ
  have hholder (x y : S) : ‖f x - f y‖ ≤ N * dist x y ^ α := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using hh x x.property y y.property
  obtain ⟨g, hg, hgn⟩ := OAI.Analysis.PDE.Elliptic.exists_convex_holder_extension_of_bounds
    (show S.Nonempty from ⟨x₀, mem_closedBall_self hρ⟩)
    (isClosed_closedBall.isComplete) (convex_closedBall x₀ ρ) hα.le hN
    (fun x : S => f x) (OAI.Analysis.PDE.Nonlinear.continuous_of_holder_bound hα hholder)
    (fun x => hn x x.property) hholder
  exact ⟨g, fun x hx => hg ⟨x, hx⟩, hgn⟩

/-- Extend the actual real coefficient and then take its matrix in the
Hessian-contraction convention, without increasing the Hölder bound. -/
theorem exists_closedBall_matrix_field {m : ℕ}
    (x₀ : EuclideanSpace ℝ (Fin m)) {ρ α N : ℝ}
    (hρ : 0 ≤ ρ) (hα : 0 < α) (hN : 0 ≤ N)
    (A : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hn : ∀ x ∈ closedBall x₀ ρ, ‖A x‖ ≤ N)
    (hh : ∀ x ∈ closedBall x₀ ρ, ∀ y ∈ closedBall x₀ ρ,
      ‖A x - A y‖ ≤ N * ‖x-y‖^α) :
    ∃ g : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
      (∀ x ∈ closedBall x₀ ρ, OAI.Analysis.Normed.Function.Holder.HolderMap.value g x = OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (A x)) ∧ ‖g‖ ≤ N := by
  obtain ⟨B, hB, hBn⟩ := exists_closedBall_holder_field x₀ hρ hα hN A hn hh
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrixCLM B, ?_,
    (OAI.Analysis.PDE.Schauder.norm_euclideanCoefficientHolder_le B).trans hBn⟩
  intro x hx
  change OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.Normed.Function.Holder.HolderMap.value B x) = _
  rw [hB x hx]

end OAI.Analysis.PDE.Dirichlet
