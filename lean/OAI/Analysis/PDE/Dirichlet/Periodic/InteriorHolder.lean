import OAI.Analysis.PDE.Dirichlet.CompactInterior
import OAI.Analysis.PDE.Dirichlet.Periodic.Ellipticity

open Set Module
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The periodic Dirichlet problem has a data-only interior C²,α bound.
Neither uniform ellipticity nor a C² estimate is assumed for its solutions:
both are supplied by the previous a priori estimates for this same equation. -/
theorem uniform_interior_holder_lattice {n : ℕ}
    (e : CoordinateSpace (n + 1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF : ContDiff ℝ 2 F)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hFper : LatticePeriodic e lat F)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hFpos : ∀ x, r x ≤ 0 → 0 < F x) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef)
    {K' : Set (CoordinateSpace (n + 1) 4)} (hK' : IsCompact K')
    (hK'int : K' ⊆ {x | r x < 0}) :
    ∃ α B : ℝ, 0 < α ∧ α < 1 ∧ 0 < B ∧
      ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 u →
      LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x ∈ K', ∀ y ∈ K',
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + u z)) x -
          fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + u z)) y‖ ≤ B * (dist x y) ^ α := by
  obtain ⟨M, hM, hnorm⟩ := uniform_hessian_bound_lattice e lat hK hr hB₀ hF
    hrper hBper hFper hbounded hne hreg hFpos hr₀ hbase hdet hconvex
  obtain ⟨c, C, hc, hC, hell⟩ := uniform_solution_ellipticity_lattice e lat hK hr hB₀ hF
    hrper hBper hFper hbounded hne hreg hFpos hr₀ hbase hdet hconvex
  obtain ⟨α, B, hα, hα1, hB, hholder⟩ := log_equation_holder_on_compact
    (n := n) hc (show c ≤ c + C by linarith) hM.le
    (isOpen_lt hr.continuous continuous_const) hK' hK'int F hF
    (fun x hx ↦ hFpos x hx.le)
  refine ⟨α, B, hα, hα1, hB, ?_⟩
  intro u hu huper huz hup hueq
  apply hholder (fun y ↦ B₀ y + u y) (hB₀.add hu) hup hueq
  · intro x hx v
    obtain ⟨hl, hh⟩ := hell u hu huper huz hup hueq x hx.le v
    refine ⟨hl, hh.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  · intro x hx
    exact hnorm u hu huper huz hup hueq x hx.le

end OAI.Analysis.PDE.Dirichlet
