import OAI.Analysis.PDE.Dirichlet.Path.InteriorHolder
import OAI.Analysis.PDE.Dirichlet.Path.C1
import OAI.Analysis.PDE.Dirichlet.CompactLimit

open Set Module Metric Filter
open scoped Topology
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Local sequential closedness along the density path. All a priori bounds
are derived from the fixed data; no derivative convergence or bound is assumed. -/
theorem exists_densityPath_solution_limit_on_compact {n : ℕ}
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
    (hK'int : K' ⊆ {x | r x < 0}) (hK'conv : Convex ℝ K')
    (t : ℕ → ℝ) {t₀ : ℝ} (ht : ∀ k, t k ∈ Icc (0 : ℝ) 1)
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (htlim : Tendsto t atTop (𝓝 t₀))
    (u : ℕ → CoordinateSpace (n + 1) 4 → ℝ) (hu : ∀ k, ContDiff ℝ 4 (u k))
    (huper : ∀ k, LatticePeriodic e lat (u k))
    (huz : ∀ k x, r x = 0 → u k x = 0)
    (hup : ∀ k x, r x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u k y) x)).PosDef)
    (hueq : ∀ k x, r x < 0 →
      OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u k y) x) =
        densityPath F₀ F₁ (t k) x) :
    ∃ ψ : CoordinateSpace (n + 1) 4 → ℝ, ContDiffOn ℝ 2 ψ (interior K') ∧
      (∀ x ∈ interior K', OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) =
          densityPath F₀ F₁ t₀ x ∧ (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformlyOn (fun k x ↦ B₀ x + u (φ k) x) ψ atTop K' ∧
        TendstoUniformlyOn (fun k ↦ fderiv ℝ (fun x ↦ B₀ x + u (φ k) x))
          (fderiv ℝ ψ) atTop (interior K') ∧
        TendstoUniformlyOn (fun k ↦ fderiv ℝ (fderiv ℝ (fun x ↦ B₀ x + u (φ k) x)))
          (fderiv ℝ (fderiv ℝ ψ)) atTop (interior K') := by
  obtain ⟨M₀, M₁, _, _, h01⟩ := uniform_value_gradient_densityPath_lattice e lat hK hr hB₀ hF₀ hF₁
    hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨M₂, _, h2⟩ := uniform_hessian_bound_densityPath_lattice e lat hK hr hB₀ hF₀ hF₁
    hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨α, B, hα, _, _, hholder⟩ := uniform_interior_holder_densityPath_lattice e lat hK hr hB₀ hF₀ hF₁
    hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex hK' hK'int
  have hbound01 (k x) (hx : x ∈ K') := h01 (t k) (ht k) (u k) (hu k) (huper k)
    (huz k) (hup k) (hueq k) x (hK'int hx).le
  have hbound2 (k x) (hx : x ∈ K') := h2 (t k) (ht k) (u k) (hu k) (huper k)
    (huz k) (hup k) (hueq k) x (hK'int hx).le
  have hboundH (k) := hholder (t k) (ht k) (u k) (hu k) (huper k) (huz k) (hup k) (hueq k)
  apply exists_local_solution_limit_on_compact hK' hK'conv
    (fun k x ↦ B₀ x + u k x) (fun k ↦ (hB₀.add (hu k)).of_le (by norm_num)) hα
    (fun k x hx ↦ (hbound01 k x hx).1) (fun k x hx ↦ (hbound01 k x hx).2)
    hbound2 hboundH
  · intro x hx
    have hc : Continuous (fun s : ℝ ↦ densityPath F₀ F₁ s x) := by
      unfold densityPath
      fun_prop
    exact hc.continuousAt.tendsto.comp htlim
  · intro x hx
    exact densityPath_pos (hpos₀ x (hK'int (interior_subset hx)).le)
      (hpos₁ x (hK'int (interior_subset hx)).le) ht₀
  · intro k x hx
    exact hueq k x (hK'int (interior_subset hx))
  · intro k x hx
    exact hup k x (hK'int (interior_subset hx))

end OAI.Analysis.PDE.Dirichlet
