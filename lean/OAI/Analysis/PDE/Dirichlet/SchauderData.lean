import OAI.Analysis.PDE.Dirichlet.Boundary.ChartData
import OAI.Analysis.PDE.Dirichlet.PointwiseSchauderAbsorption

open Set Module InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Data for a genuine periodic elliptic equation. This record indexes
all admissible equations at once, so the global constant is uniform in
the coefficient field, forcing, and solution. -/
structure PeriodicSchauderData
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (r : E → ℝ)
    (hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}) (α ell Λ N : ℝ) where
  coefficient : E → E →L[ℝ] E
  coefficient_continuous : Continuous coefficient
  coefficient_symmetric : ∀ x, r x ≤ 0 → (coefficient x).toLinearMap.IsSymmetric
  elliptic_lower : ∀ x, r x ≤ 0 → ∀ v : E,
    ell*‖v‖^2 ≤ inner ℝ v (coefficient x v)
  elliptic_upper : ∀ x, r x ≤ 0 → ∀ v : E,
    inner ℝ v (coefficient x v) ≤ Λ*‖v‖^2
  coefficient_norm : ∀ x, r x ≤ 0 → ‖coefficient x‖ ≤ N
  coefficient_holder : ∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 →
    ‖coefficient x-coefficient y‖ ≤ N*dist x y^α
  solution : E → ℝ
  solution_smooth : ContDiff ℝ 3 solution
  solution_periodic : LatticePeriodic e b solution
  solution_zero : ∀ x, r x = 0 → solution x = 0
  forcing : E → ℝ
  forcingBound : ℝ
  forcingBound_nonneg : 0 ≤ forcingBound
  forcing_norm : ∀ x, r x ≤ 0 → |forcing x| ≤ forcingBound
  forcing_holder : ∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 →
    |forcing x-forcing y| ≤ forcingBound*dist x y^α
  equation : ∀ x, r x ≤ 0 → OAI.Analysis.PDE.Elliptic.ellipticTrace coefficient solution x = forcing x
  jets : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α
  jets_value : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value jets x = solution x
  jets_first : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative jets x = fderiv ℝ solution x
  jets_second : ∀ x : {x | r x ≤ 0},
    OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative jets x = fderiv ℝ (fderiv ℝ solution) x

omit [Fintype ι] in
theorem PeriodicSchauderData.solution_bound
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r : E → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α ell Λ N : ℝ}
    (d : PeriodicSchauderData e b r hΩD α ell Λ N)
    (x : E) (hx : r x ≤ 0) : |d.solution x| ≤ ‖OAI.Analysis.Normed.Function.Holder.C2Holder.value d.jets‖ := by
  have hv := (OAI.Analysis.Normed.Function.Holder.C2Holder.value d.jets).norm_coe_le_norm ⟨x, hx⟩
  simpa only [d.jets_value, Real.norm_eq_abs] using hv

end OAI.Analysis.PDE.Dirichlet
