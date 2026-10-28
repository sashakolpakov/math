import OAI.Analysis.PDE.Dirichlet.Path.BanachBound
import OAI.Analysis.PDE.Dirichlet.Path.BanachCompactness

open Set Module Filter
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

/-- The closedness limit along the density path exists in an actual
C²,β space up to the boundary. It retains the equation, strict positivity,
periodicity and the prescribed boundary values. No smoothness of the
limit or linear Dirichlet inverse is assumed here. -/
theorem exists_densityPath_closed_banach_limit {n : ℕ} {P V ι : Type*}
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
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef)
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hslim : Tendsto (fun k ↦ (s k).t) atTop (𝓝 t)) :
    ∃ β : ℝ, 0 < β ∧ β < 1 ∧
      Nonempty (BanachPathLimit e lat r B₀ F₀ F₁ hΩK β s t) := by
  have hb := uniform_banach_bound_densityPath_lattice (n := n)
    (P := P) (V := V) (ι := ι) (r := r) (B₀ := B₀) (F₀ := F₀) (F₁ := F₁)
    (hΩK := hΩK)
    e lat hK hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀
    hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨α, N, hα, hα1, hN, Φ, hΦ⟩ := hb
  refine ⟨α / 2, half_pos hα, by linarith, ?_⟩
  exact nonempty_densityPath_banach_limit_of_bound
    (e := e) (lat := lat) (hK := hK) (hr := hr) (hB₀ := hB₀)
    (hF₀ := hF₀) (hF₁ := hF₁) (hrper := hrper) (hBper := hBper)
    (hbounded := hbounded) (hreg := hreg) (hpos₀ := hpos₀) (hpos₁ := hpos₁)
    (hα := hα) (hN := hN.le) (s := s) (ht := ht) (hslim := hslim) (Φ := Φ) (hΦ := hΦ)

end OAI.Analysis.PDE.Dirichlet
