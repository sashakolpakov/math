import OAI.Analysis.PDE.Dirichlet.Path.ClosedHolder
import OAI.Analysis.PDE.Dirichlet.LatticeHolder

open Set Module Metric
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- Data-only Hölder control of the actual Hessian on the entire closed
periodic domain, not merely on compact subsets or in its interior. -/
theorem uniform_global_holder_densityPath_lattice {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : CoordinateSpace (n + 1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ α D : ℝ, 0 < α ∧ α < 1 ∧ 0 < D ∧
      ∀ s : SmoothPathSolution e lat r B₀ F₀ F₁, ∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 →
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + s.u z)) x -
          fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + s.u z)) y‖ ≤ D * (dist x y) ^ α := by
  let S := cthickening 1 (latticeSublevelCell e lat K r) ∩ {x | r x ≤ 0}
  have hS : IsCompact S :=
    (isCompact_latticeSublevelCell e lat hK hr.continuous).cthickening.inter_right
      (isClosed_le hr.continuous continuous_const)
  obtain ⟨α, D, hα, hα1, hD, hholder⟩ := uniform_closed_holder_densityPath_lattice e lat hK
    hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
    hS inter_subset_right
  obtain ⟨M, hM, hhess⟩ := uniform_hessian_bound_densityPath_lattice e lat hK
    hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  refine ⟨α, D + 2 * M, hα, hα1, by positivity, ?_⟩
  exact lattice_holder_of_thickened_cell e lat hrper hbounded
    (fun s : SmoothPathSolution e lat r B₀ F₀ F₁ ↦ fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + s.u z)))
    (fun s ↦ (hBper.add s.periodic).fderiv.fderiv) hα.le hD.le hM.le
    (fun s x hx ↦ hhess s.t s.parameter s.u s.smooth s.periodic s.zero s.positive s.equation x hx)
    hholder

end OAI.Analysis.PDE.Dirichlet
