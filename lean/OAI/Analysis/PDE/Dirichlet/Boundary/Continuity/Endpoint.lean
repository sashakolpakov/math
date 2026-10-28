import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Method
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Base

noncomputable section
open Set Module
open scoped ContDiff ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4

/-- Extract the actual classical potential at the final parameter, including
the equation and positivity on the physical boundary. -/
theorem SmoothPathSolvable.classical_endpoint
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} {r B₀ F₀ F₁ : E → ℝ}
    (hs : SmoothPathSolvable e lat r B₀ F₀ F₁ 1)
    (hr : ContDiff ℝ 1 r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : Continuous F₀) (hF₁ : Continuous F₁)
    (hBp : LatticePeriodic e lat B₀)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    ∃ ψ : E → ℝ, ContDiff ℝ 4 ψ ∧ LatticePeriodic e lat ψ ∧
      (∀ x, r x = 0 → ψ x = B₀ x) ∧
      (∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) ∧
      (∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F₁ x) := by
  obtain ⟨s,hs⟩ := hs
  refine ⟨fun x => B₀ x+s.u x, hB₀.add s.smooth,
    hBp.add s.periodic, (fun x hx => by dsimp only; rw [s.zero x hx,add_zero]), ?_, ?_⟩
  · exact s.closed_positive hr hreg (hB₀.of_le (by norm_num)) hF₀ hF₁ hpos₀ hpos₁
  · intro x hx
    have heq := s.closed_equation hr hreg (hB₀.of_le (by norm_num)) hF₀ hF₁ x hx
    rw [hs] at heq
    simpa [densityPath] using heq

end OAI.Analysis.PDE.Dirichlet
