import OAI.Analysis.PDE.Dirichlet.BoundedC2
import OAI.Analysis.PDE.Dirichlet.DensityPath

open Set Module
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Uniform scalar barriers along the entire affine density path. -/
theorem uniform_barriers_densityPath_lattice {n : ℕ}
    (e : CoordinateSpace (n + 1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hne : {x | r x ≤ 0}.Nonempty)
    (_ : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ b B : ℝ, 0 < b ∧ b ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 2 u →
      LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1)
        (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = densityPath F₀ F₁ t x) →
      ∀ x, r x ≤ 0 → B * r x ≤ u x ∧ u x ≤ b * r x := by
  have hn : 1 ≤ n + 1 := by omega
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by norm_num)
  have hB2 : ContDiff ℝ 2 B₀ := hB₀.of_le (by norm_num)
  have hR : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef := by
    intro x hx
    have hu : (OAI.LinearAlgebra.Moore.complexify (r₀ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosDef := by
      rw [OAI.LinearAlgebra.Moore.complexify_real_smul, OAI.LinearAlgebra.Moore.complexify_one]
      exact Matrix.PosDef.one.smul hr₀
    simpa only [← OAI.LinearAlgebra.Moore.complexify_add, sub_add_cancel] using
      Matrix.PosDef.posSemidef_add (hconvex x hx) hu
  obtain ⟨m, U, L, hm, hU, hL, hdata⟩ := densityPath_uniform_bounds_lattice e lat hK
    hr.continuous hrper hbounded hne hF₀ hF₁ hp₀ hp₁ hpos₀ hpos₁
  obtain ⟨b, B, hb, hbB, hbar⟩ := uniform_solution_barriers_bounded_density_lattice hn e lat hK hne
    hB2 hr2 hbounded hBper hrper hbase hR hdet (U := U) hm
  refine ⟨b, B, hb, hbB, ?_⟩
  intro t ht u hu huper huz hup hueq
  exact hbar (densityPath F₀ F₁ t) (fun x hx ↦ (hdata t ht x hx).1)
    (fun x hx ↦ (hdata t ht x hx).2.1) u hu huper hup hueq huz

end OAI.Analysis.PDE.Dirichlet
