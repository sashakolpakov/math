import OAI.Analysis.PDE.Dirichlet.DataC2
import OAI.Analysis.PDE.Dirichlet.EllipticData
import OAI.Analysis.PDE.Dirichlet.SublevelClosure

open Set
open scoped Matrix ComplexOrder Matrix.Norms.Elementwise

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem realHessian_norm_le_second_derivative {n s : ℕ}
    (ψ : CoordinateSpace n s → ℝ) (x : CoordinateSpace n s) :
    ‖realHessian ψ x‖ ≤ ‖fderiv ℝ (fderiv ℝ ψ) x‖ := by
  apply (Matrix.norm_le_iff (ContinuousLinearMap.opNorm_nonneg _)).mpr
  intro i j
  simpa only [realHessian, Real.norm_eq_abs, norm_coordinateVector, mul_one] using
    bilinear_abs_le (fderiv ℝ (fderiv ℝ ψ) x) (coordinateVector i) (coordinateVector j)

theorem quaternionHessian_norm_le_second_derivative {n s : ℕ} (e : Fin s → Q)
    (ψ : CoordinateSpace n s → ℝ) (x : CoordinateSpace n s) :
    ‖quaternionHessian e ψ x‖ ≤ hessianMapBound (n := n) e * ‖fderiv ℝ (fderiv ℝ ψ) x‖ := by
  exact (hessianMap_norm_le e (realHessian ψ x)).trans
    (mul_le_mul_of_nonneg_left (realHessian_norm_le_second_derivative ψ x) (hessianMapBound_nonneg e))

theorem logPrincipalSymbol_eq_inverse {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) Q) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef)
    (hAC : A * C = 1) (hCA : C * A = 1) (v : CoordinateSpace n 4) :
    logPrincipalSymbol A v = inversePrincipalSymbol OAI.Analysis.Calculus.Quaternion.fourSlots C v := by
  have hd := OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef A hA
  unfold logPrincipalSymbol inversePrincipalSymbol
  rw [OAI.LinearAlgebra.Moore.mooreDifferential_inverse n A _ C (OAI.LinearAlgebra.Moore.isHermitian_of_complexify hA.isHermitian)
    (OAI.Analysis.Calculus.Quaternion.outer_isHermitian _) hAC hCA, quaternionRealTrace_outer]
  exact mul_div_cancel_left₀ _ hd.ne'

/-- The actual logarithmic Monge–Ampère linearization is uniformly elliptic
over every smooth solution, including the boundary, with constants depending
only on the prescribed data. The equation is required only in the interior. -/
theorem uniform_solution_ellipticity {n : ℕ}
    {r B₀ F : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF : ContDiff ℝ 2 F)
    (hK : IsCompact {x | r x ≤ 0}) (hKne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hFpos : ∀ x, r x ≤ 0 → 0 < F x) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ u : CoordinateSpace (n + 1) 4 → ℝ, ContDiff ℝ 4 u →
      (∀ x, r x = 0 → u x = 0) →
      (∀ x ∈ interior {x | r x ≤ 0},
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x)).PosDef) →
      (∀ x ∈ interior {x | r x ≤ 0},
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) = F x) →
      ∀ x, r x ≤ 0 → ∀ v : CoordinateSpace (n + 1) 4,
        c * ‖v‖ ^ 2 ≤ logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) v ∧
        logPrincipalSymbol (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) v ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨B, hB, hnorm⟩ := uniform_hessian_bound hr hB₀ hF hK hKne hreg hFpos hr₀ hbase hdet hconvex
  obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn hKne hF.continuous.continuousOn
  let R := hessianMapBound (n := n + 1) OAI.Analysis.Calculus.Quaternion.fourSlots * B
  obtain ⟨c, C, hc, hC, hell⟩ := logPrincipalSymbol_uniform_of_bounded_data
    (by omega : 1 ≤ n + 1) R (F y) (hFpos y hy)
  refine ⟨c, C, hc, hC, ?_⟩
  intro u hu huz hup hueq x hx v
  have hψ : ContDiff ℝ 2 (fun y ↦ B₀ y + u y) := (hB₀.add hu).of_le (by norm_num)
  have hr1 : ContDiff ℝ 1 r := hr.of_le (by norm_num)
  have heq := equality_on_regular_sublevel_of_interior hr1 hreg
    (continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots hψ) hF.continuous hueq
  have hpsd := quaternionHessian_posSemidef_on_regular_sublevel hr1 hreg hψ hup x hx
  have hbound : ‖quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x‖ ≤ R :=
    (quaternionHessian_norm_le_second_derivative OAI.Analysis.Calculus.Quaternion.fourSlots _ x).trans
      (mul_le_mul_of_nonneg_left (hnorm u hu huz hup heq x hx) (hessianMapBound_nonneg OAI.Analysis.Calculus.Quaternion.fourSlots))
  apply hell _ ⟨hbound, quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hψ.contDiffAt,
    (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hψ.contDiffAt)).mp hpsd, ?_⟩ v
  rw [heq x hx]
  exact hmin hx

end OAI.Analysis.PDE.Dirichlet
