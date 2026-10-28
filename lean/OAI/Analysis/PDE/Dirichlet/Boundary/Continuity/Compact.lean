import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Closed
import OAI.Analysis.PDE.Dirichlet.Fourth.UniformLimit

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Elliptic

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace (n+1) 4

/-- The actual fourth-order a priori estimate closes the smooth solution
class under the Banach subsequential limits used by the continuity method. -/
theorem hasC4PathLimits_of_uniform_fourth
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : LatticePeriodic e lat r) (hBp : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hfourth : ∃ M > 0, ∀ a : SmoothPathSolution e lat r B₀ F₀ F₁,
      OAI.Analysis.PDE.Elliptic.HasFourthHolderBound {x | r x ≤ 0} (d.exponent/2) (fun y => B₀ y+a.u y) M) :
    HasC4PathLimits e lat d := by
  intro s t L
  exact L.contDiffOn_four_closed_of_uniform_fourth (by omega) hK d hr hB₀ hF₀ hF₁
    hrp hBp hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁ hfourth

end OAI.Analysis.PDE.Dirichlet
