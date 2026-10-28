import OAI.Analysis.PDE.Dirichlet.Periodic.C2
import OAI.Analysis.PDE.Dirichlet.SolutionEllipticity

open Set Module
open scoped Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Uniform ellipticity of the actual logarithmic equation on a periodic
domain, with constants depending only on fixed data, valid up to the boundary. -/
theorem uniform_solution_ellipticity_lattice {n : ℕ}
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
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 u →
      LatticePeriodic e lat u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x, r x < 0 →
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x, r x < 0 →
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x ≤ 0 → ∀ v : CoordinateSpace (n + 1) 4,
        c * ‖v‖ ^ 2 ≤ logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) v ∧
        logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) v ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨B, hB, hnorm⟩ := uniform_hessian_bound_lattice e lat hK hr hB₀ hF
    hrper hBper hFper hbounded hne hreg hFpos hr₀ hbase hdet hconvex
  obtain ⟨m, hm, hmin⟩ := exists_lattice_positive_lower e lat hK hr.continuous
    hrper hbounded hne hF.continuous.continuousOn hFper hFpos
  let R := hessianMapBound (n := n + 1) OAI.Analysis.Calculus.Quaternion.fourSlots * B
  obtain ⟨c, C, hc, hC, hell⟩ := logPrincipalSymbol_uniform_of_bounded_data
    (by omega : 1 ≤ n + 1) R m hm
  refine ⟨c, C, hc, hC, ?_⟩
  intro u hu huper huz hup hueq x hx v
  have hψ : ContDiff ℝ 2 (fun y ↦ B₀ y + u y) := (hB₀.add hu).of_le (by norm_num)
  have hr1 : ContDiff ℝ 1 r := hr.of_le (by norm_num)
  have heq := equality_on_regular_sublevel_of_interior hr1 hreg
    (continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots hψ) hF.continuous
    (fun z hz ↦ hueq z (neg_of_mem_interior_regular_sublevel hreg hz))
  have hpsd := quaternionHessian_posSemidef_on_regular_sublevel hr1 hreg hψ
    (fun z hz ↦ hup z (neg_of_mem_interior_regular_sublevel hreg hz)) x hx
  have hbound : ‖quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x‖ ≤ R :=
    (quaternionHessian_norm_le_second_derivative OAI.Analysis.Calculus.Quaternion.fourSlots _ x).trans
      (mul_le_mul_of_nonneg_left (hnorm u hu huper huz hup hueq x hx) (hessianMapBound_nonneg OAI.Analysis.Calculus.Quaternion.fourSlots))
  apply hell _ ⟨hbound, quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hψ.contDiffAt,
    (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hψ.contDiffAt)).mp hpsd, ?_⟩ v
  rw [heq x hx]
  exact hmin x hx

end OAI.Analysis.PDE.Dirichlet
