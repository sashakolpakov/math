import OAI.Analysis.PDE.Dirichlet.Path.C2
import OAI.Analysis.PDE.Dirichlet.Periodic.Ellipticity
import OAI.Analysis.PDE.Dirichlet.DensityPath

open Set Module
open scoped Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Uniform ellipticity estimate along the positive affine density path.
The same constant works for every path parameter and every solution. -/
theorem uniform_ellipticity_densityPath_lattice {n : ℕ}
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
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 u →
      LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = densityPath F₀ F₁ t x) →
      ∀ x, r x ≤ 0 → ∀ v : CoordinateSpace (n + 1) 4,
        c * ‖v‖ ^ 2 ≤ logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) v ∧
        logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) v ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨B, hB, hnorm⟩ := uniform_hessian_bound_densityPath_lattice e lat hK hr hB₀ hF₀ hF₁
    hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨m, U, L, hm, _, _, hmin⟩ := densityPath_uniform_bounds_lattice e lat hK
    hr.continuous hrper hbounded hne hF₀ hF₁ hp₀ hp₁ hpos₀ hpos₁
  let R := hessianMapBound (n := n + 1) OAI.Analysis.Calculus.Quaternion.fourSlots * B
  obtain ⟨c, C, hc, hC, hell⟩ := logPrincipalSymbol_uniform_of_bounded_data
    (by omega : 1 ≤ n + 1) R m hm
  refine ⟨c, C, hc, hC, ?_⟩
  intro t ht u hu huper huz hup hueq x hx v
  have hψ : ContDiff ℝ 2 (fun y ↦ B₀ y + u y) := (hB₀.add hu).of_le (by norm_num)
  have hr1 : ContDiff ℝ 1 r := hr.of_le (by norm_num)
  have heq := equality_on_regular_sublevel_of_interior hr1 hreg
    (continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots hψ) (contDiff_densityPath hF₀ hF₁ t).continuous
    (fun z hz ↦ hueq z (neg_of_mem_interior_regular_sublevel hreg hz))
  have hpsd := quaternionHessian_posSemidef_on_regular_sublevel hr1 hreg hψ
    (fun z hz ↦ hup z (neg_of_mem_interior_regular_sublevel hreg hz)) x hx
  have hbound : ‖quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x‖ ≤ R :=
    (quaternionHessian_norm_le_second_derivative OAI.Analysis.Calculus.Quaternion.fourSlots _ x).trans
      (mul_le_mul_of_nonneg_left (hnorm t ht u hu huper huz hup hueq x hx) (hessianMapBound_nonneg OAI.Analysis.Calculus.Quaternion.fourSlots))
  apply hell _ ⟨hbound, quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hψ.contDiffAt,
    (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hψ.contDiffAt)).mp hpsd, ?_⟩ v
  rw [heq x hx]
  exact (hmin t ht x hx).1

end OAI.Analysis.PDE.Dirichlet
