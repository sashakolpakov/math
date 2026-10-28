import OAI.Analysis.PDE.Dirichlet.BoundedC2
import OAI.Analysis.PDE.Dirichlet.DensityPath

open Set Module
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Uniform value and gradient estimates along the positive affine density path.
The same constant works for every path parameter and every solution. -/
theorem uniform_value_gradient_densityPath_lattice {n : ℕ}
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
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 u →
      LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = densityPath F₀ F₁ t x) →
      ∀ x, r x ≤ 0 → ‖B₀ x + u x‖ ≤ C₀ ∧
        ‖fderiv ℝ (fun y ↦ B₀ y + u y) x‖ ≤ C₁ := by
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
  have hB : 0 < B := hb.trans_le hbB
  obtain ⟨G, hG, hgrad⟩ := uniform_gradient_bound_from_bounded_densities_lattice hn e lat hK
    hr2 (hB₀.of_le (by norm_num)) hrper hBper hbounded hreg hb.le hbB hr₀
    (fun x hx ↦ hconvex x hx.le) hm hU.le hL.le
  obtain ⟨A₀, hA₀, hval⟩ := exists_lattice_norm_bound e lat hK hr.continuous
    hrper hbounded hB₀.continuous.continuousOn hBper
  obtain ⟨A₁, hA₁, hder⟩ := exists_lattice_norm_bound e lat hK hr.continuous
    hrper hbounded (hB₀.fderiv_right (m := 0) (by norm_num)).continuous.continuousOn hBper.fderiv
  obtain ⟨R, hRpos, hrval⟩ := exists_lattice_norm_bound e lat hK hr.continuous
    hrper hbounded hr.continuous.continuousOn hrper
  refine ⟨A₀ + B * R, A₁ + G, by positivity, by positivity, ?_⟩
  intro t ht u hu huper huz hup hueq x hx
  have hf := contDiff_densityPath hF₀ hF₁ t
  have hmin := fun z hz ↦ (hdata t ht z hz).1
  have hmax := fun z hz ↦ (hdata t ht z hz).2.1
  have hDF := fun z hz ↦ (hdata t ht z hz).2.2
  have hub := hbar (densityPath F₀ F₁ t) hmin hmax u
    (hu.of_le (by norm_num)) huper hup hueq huz
  have hug := hgrad (densityPath F₀ F₁ t) (hf.of_le (by norm_num)) hmin hmax hDF
    u (hu.of_le (by norm_num)) huper huz hub hup hueq
  have huneg : u x ≤ 0 := (hub x hx).2.trans (mul_nonpos_of_nonneg_of_nonpos hb.le hx)
  have hrnorm : -r x ≤ R := (neg_le_abs _).trans (hrval x hx)
  have hunorm : ‖u x‖ ≤ B * R := by
    rw [Real.norm_eq_abs, abs_of_nonpos huneg]
    nlinarith [(hub x hx).1, mul_le_mul_of_nonneg_left hrnorm hB.le]
  refine ⟨(norm_add_le _ _).trans (add_le_add (hval x hx) hunorm), ?_⟩
  change ‖fderiv ℝ (B₀ + u) x‖ ≤ A₁ + G
  rw [fderiv_add (hB₀.differentiable (by norm_num) x) (hu.differentiable (by norm_num) x)]
  exact (norm_add_le _ _).trans (add_le_add (hder x hx) (hug x hx))

end OAI.Analysis.PDE.Dirichlet
