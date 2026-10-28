import OAI.Analysis.PDE.Schauder.Dirichlet.PathInteriorFourth
import OAI.Analysis.PDE.Schauder.Dirichlet.PathFourthBoundary
import OAI.Analysis.PDE.Dirichlet.Uniform.FourthLocal

noncomputable section
open Set Module
open scoped ContDiff ComplexOrder
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+1) 4

/-- A data-dependent global fourth-order Hölder estimate for every smooth
solution of the nonlinear density path. No higher-order estimate is assumed. -/
theorem InteriorThirdPathData.uniform_fourth_holder
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 5 B₀)
    (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    ∃ C > 0, ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      OAI.Analysis.PDE.Elliptic.HasFourthHolderBound {x | r x ≤ 0} (d.exponent/2) (fun y => B₀ y+s.u y) C := by
  apply OAI.Analysis.PDE.Dirichlet.uniform_fourth_holder_of_local e lat hK hr.continuous hrp hbounded
    (fun s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁ => fun y => B₀ y+s.u y)
    (fun s => (hB₀.of_le (by norm_num)).add s.smooth)
    (fun s => hBp.add s.periodic) (half_pos d.exponent_pos)
  intro x hx
  rcases eq_or_lt_of_le hx with hboundary | hinterior
  · exact d.boundary_fourth_estimate e lat hK hr hB₀ hF₀ hF₁ hrp hBp hp₀ hp₁
      hbounded hreg hrpos hpos₀ hpos₁ hboundary
  · exact d.interior_fourth_estimate e lat hK hr hB₀ hF₀ hF₁ hrp hBp hp₀ hp₁
      hbounded hreg hrpos hpos₀ hpos₁ hinterior

end OAI.Analysis.PDE.Schauder
