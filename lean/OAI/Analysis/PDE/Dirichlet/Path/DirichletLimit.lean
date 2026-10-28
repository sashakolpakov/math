import OAI.Analysis.PDE.Dirichlet.Path.LocalCompactness
import OAI.Analysis.PDE.Dirichlet.Path.Barriers
import OAI.Analysis.PDE.Dirichlet.ZeroBoundaryLimit
import OAI.Analysis.PDE.Dirichlet.LimitCongruence

open Set Module Metric Filter
open scoped Topology
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- A path sequence has an actual periodic solution limit, continuous with zero
boundary values and C² in the interior. Smooth boundary regularity is a separate step. -/
theorem exists_densityPath_dirichlet_limit {n : ℕ}
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
    ∃ u₀ : CoordinateSpace (n + 1) 4 → ℝ, Continuous u₀ ∧
      LatticePeriodic e lat u₀ ∧ ContDiffOn ℝ 2 u₀ {x | r x < 0} ∧
      (∀ x, r x = 0 → u₀ x = 0) ∧
      (∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1)
          (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u₀ y) x) = densityPath F₀ F₁ t₀ x ∧
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u₀ y) x)).PosDef) ∧
      (∃ b B : ℝ, 0 < b ∧ b ≤ B ∧
        ∀ x, r x ≤ 0 → B * r x ≤ u₀ x ∧ u₀ x ≤ b * r x) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ x, r x ≤ 0 → Tendsto (fun k ↦ u (φ k) x) atTop (𝓝 (u₀ x))) ∧
        TendstoLocallyUniformlyOn (fun k x ↦ B₀ x + u (φ k) x)
          (fun x ↦ B₀ x + u₀ x) atTop {x | r x < 0} ∧
        TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (fun x ↦ B₀ x + u (φ k) x))
          (fderiv ℝ (fun x ↦ B₀ x + u₀ x)) atTop {x | r x < 0} ∧
        TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (fderiv ℝ (fun x ↦ B₀ x + u (φ k) x)))
          (fderiv ℝ (fderiv ℝ (fun x ↦ B₀ x + u₀ x))) atTop {x | r x < 0} := by
  obtain ⟨ψ, hψ, heq, φ, hφ, hlim, hD, hD₂⟩ :=
    exists_densityPath_solution_limit_on_domain e lat hK hr hB₀ hF₀ hF₁
      hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
      t ht ht₀ htlim u hu huper huz hup hueq
  obtain ⟨b, B, hb, hbB, hbar⟩ := uniform_barriers_densityPath_lattice e lat hK
    hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀
    hpos₀ hpos₁ hbase hdet hconvex
  let v := fun x ↦ ψ x - B₀ x
  let u₀ := zeroBoundaryExtension r v
  have hpoint (x) (hx : r x < 0) : Tendsto (fun k ↦ u (φ k) x) atTop (𝓝 (v x)) := by
    simpa only [v, add_sub_cancel_left] using (hlim.tendsto_at hx).sub_const (B₀ x)
  have hvbar (x) (hx : r x < 0) : B * r x ≤ v x ∧ v x ≤ b * r x := by
    have hh (k) := hbar (t (φ k)) (ht (φ k)) (u (φ k))
      ((hu (φ k)).of_le (by norm_num)) (huper (φ k)) (huz (φ k))
      (hup (φ k)) (hueq (φ k)) x hx.le
    exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds (hpoint x hx)
        (Eventually.of_forall (fun k ↦ (hh k).1)),
      le_of_tendsto (hpoint x hx) (Eventually.of_forall (fun k ↦ (hh k).2))⟩
  have hvreg : ContDiffOn ℝ 2 v {x | r x < 0} :=
    hψ.sub ((hB₀.of_le (by norm_num)).contDiffOn)
  have hucont : Continuous u₀ := continuous_zeroBoundaryExtension_of_barriers
    hr.continuous hvreg.continuousOn hb.le hbB hvbar
  have hureg : ContDiffOn ℝ 2 u₀ {x | r x < 0} :=
    hvreg.congr (fun x hx ↦ zeroBoundaryExtension_of_neg hx)
  have huper₀ : LatticePeriodic e lat u₀ :=
    latticePeriodic_zeroBoundaryExtension_of_limit hrper (fun k ↦ huper (φ k)) hpoint
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  have hψeq : EqOn (fun x ↦ B₀ x + u₀ x) ψ {x | r x < 0} := by
    intro x hx
    dsimp only [u₀]
    rw [zeroBoundaryExtension_of_neg hx]
    dsimp only [v]
    ring
  have hH := quaternionHessian_eqOn_of_open OAI.Analysis.Calculus.Quaternion.fourSlots hΩ hψeq
  refine ⟨u₀, hucont, huper₀, hureg, ?_, ?_, ⟨b, B, hb, hbB, ?_⟩, φ, hφ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact zeroBoundaryExtension_of_nonneg hx.ge
  · intro x hx
    rw [hH hx]
    exact heq x hx
  · intro x hx
    exact zeroBoundaryExtension_barriers hvbar hx
  · intro x hx
    exact tendsto_zeroBoundaryExtension hpoint (fun k ↦ huz (φ k)) hx
  · exact locally_uniform_limit_congr_on hlim hψeq
  · exact locally_uniform_limit_congr_on hD (fderiv_eqOn_of_open hΩ hψeq)
  · exact locally_uniform_limit_congr_on hD₂
      (fderiv_eqOn_of_open hΩ (fderiv_eqOn_of_open hΩ hψeq))

end OAI.Analysis.PDE.Dirichlet
