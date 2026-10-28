import OAI.Analysis.PDE.Schauder.Boundary.PathThird
import OAI.Analysis.PDE.Dirichlet.Path.ThirdRegularity

noncomputable section
open Set Module
open scoped ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance uniformThird1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance uniformThird1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance uniformThird2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformThird2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformThird3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformThird3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Discharge the boundary input using the original fixed densities and
the actual nonlinear path, at the exponent already chosen by the C² estimate. -/
theorem InteriorThirdPathData.boundary_third_estimate
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) (hn : 3 ≤ n*4)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r)
    (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    BoundaryThirdPathEstimate d := by
  obtain ⟨b⟩ := nonempty_boundaryThirdPathData e lat hK d (hr.of_le (by simp)) hB₀ hF₀ hF₁
    hrper hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁
  exact b.boundary_estimate hn hr hB₀ hF₀ hF₁ hreg

/-- Uniform global third derivatives, including the physical boundary,
without a local-estimate or a higher-derivative hypothesis. -/
theorem InteriorThirdPathData.uniform_third_bounds
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) (hn : 3 ≤ n*4)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    ∃ M > 0, ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      (∀ x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x‖ ≤ M) ∧
      (∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) x-
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) y‖ ≤ M*dist x y^d.exponent) := by
  exact d.uniform_third_bounds_of_boundary e lat hK hn hr.continuous hB₀ hF₀ hF₁
    hrper hBper hbounded (d.boundary_third_estimate e lat hK hn hr hB₀ hF₀ hF₁
      hrper hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁)

/-- The complete third-order a priori estimate from the manuscript's
fixed geometric hypotheses. No analytic estimates are supplied as inputs. -/
theorem uniform_third_bounds_densityPath_lattice
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+1) 4 → ℝ} (hr : ContDiff ℝ ∞ r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hp₀ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₀) (hp₁ : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n+1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x-r₀ •
        (1 : Matrix (Fin (n+1)) (Fin (n+1)) (Quaternion ℝ)))).PosSemidef) :
    ∃ α M : ℝ, 0 < α ∧ α < 1 ∧ 0 < M ∧
      ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
        (∀ x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x‖ ≤ M) ∧
        (∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 →
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) x-
            fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) y‖ ≤ M*dist x y^α) := by
  have hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0} := by
    intro x hx
    change r x ≤ 0
    exact (show r x < 0 from hx).le
  obtain ⟨d⟩ := nonempty_interiorThirdPathData (hΩK := hΩK)
    e lat hK (hr.of_le (by simp)) hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg
    hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨M,hM,hbound⟩ := d.uniform_third_bounds e lat hK (by omega) hr hB₀ hF₀ hF₁
    hrper hBper hp₀ hp₁ hbounded hne hreg hpos₀ hpos₁
  exact ⟨d.exponent,M,d.exponent_pos,d.exponent_lt_one,hM,hbound⟩

end OAI.Analysis.PDE.Schauder
