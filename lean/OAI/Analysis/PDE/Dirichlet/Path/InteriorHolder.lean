import OAI.Analysis.PDE.Dirichlet.Path.Ellipticity
import OAI.Analysis.PDE.Dirichlet.LogGradientBound
import OAI.Analysis.PDE.Dirichlet.CompactInterior

open Set Module Metric
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Uniform interior Hessian Hölder estimate along the positive affine density path.
The same constant works for every path parameter and every solution. -/
theorem uniform_interior_holder_densityPath_lattice {n : ℕ}
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
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef)
    {K' : Set (CoordinateSpace (n + 1) 4)} (hK' : IsCompact K')
    (hK'int : K' ⊆ {x | r x < 0}) :
    ∃ α B : ℝ, 0 < α ∧ α < 1 ∧ 0 < B ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 u →
      LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = densityPath F₀ F₁ t x) →
      ∀ x ∈ K', ∀ y ∈ K',
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + u z)) x -
          fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + u z)) y‖ ≤ B * (dist x y) ^ α := by
  obtain ⟨M, hM, hnorm⟩ := uniform_hessian_bound_densityPath_lattice e lat hK hr hB₀ hF₀ hF₁
    hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨c, C, hc, hC, hell⟩ := uniform_ellipticity_densityPath_lattice e lat hK hr hB₀ hF₀ hF₁
    hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨m, U, L₁, hm, hU, hL₁, hb⟩ := densityPath_uniform_bounds_lattice e lat hK
    hr.continuous hrper hbounded hne hF₀ hF₁ hp₀ hp₁ hpos₀ hpos₁
  obtain ⟨L₂, hL₂, hlog₂⟩ := densityPath_uniform_log_second_lattice e lat hK
    hr.continuous hrper hbounded hF₀ hF₁ hp₀ hp₁ hpos₀ hpos₁
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  obtain ⟨R, hR, hthick⟩ := hK'.exists_cthickening_subset_open hΩ hK'int
  obtain ⟨α, B, hα, hα1, hB, hholder⟩ := log_equation_holder_on_interior_set
    (n := n) hc (show c ≤ c + C by linarith)
    (show 0 ≤ L₁ / m by positivity) hL₂.le hM.le hR
  refine ⟨α, B, hα, hα1, hB, ?_⟩
  intro t ht u hu huper huz hup hueq
  have hballs : ∀ z ∈ K', closedBall z R ⊆ {x | r x < 0} := by
    intro z hz
    exact ((closedBall_subset_cthickening_singleton z R).trans
      (cthickening_subset_of_subset R (singleton_subset_iff.mpr hz))).trans hthick
  apply hholder {x | r x < 0} K' (fun y ↦ B₀ y + u y) (densityPath F₀ F₁ t)
    hballs (hB₀.add hu) hup hueq
  · intro x hx v
    obtain ⟨hl, hh⟩ := hell t ht u hu huper huz hup hueq x hx.le v
    exact ⟨hl, hh.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))⟩
  · intro x hx
    exact hnorm t ht u hu huper huz hup hueq x hx.le
  · intro x hx
    exact ((contDiff_densityPath hF₀ hF₁ t).differentiable (by norm_num) x).log
      (densityPath_pos (hpos₀ x hx.le) (hpos₁ x hx.le) ht).ne'
  · intro x hx
    exact norm_fderiv_log_le_of_bounds
      ((contDiff_densityPath hF₀ hF₁ t).differentiable (by norm_num) x)
      hm hL₁.le (hb t ht x hx.le).1 (hb t ht x hx.le).2.2
  · intro x hx v
    exact hlog₂ t ht x hx.le v

end OAI.Analysis.PDE.Dirichlet
