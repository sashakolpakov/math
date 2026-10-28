import OAI.Analysis.PDE.Nonlinear.Matrix
import Mathlib.Analysis.Matrix.Order

/-! Strict operator positivity passes to the manuscript's real coordinate matrix. -/

noncomputable section
open Set InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic

theorem operatorCoordinateMatrix_eq_toMatrix {n s : ℕ}
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hA : A.toLinearMap.IsSymmetric) :
    OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix A = A.toLinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin n × Fin s) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n × Fin s) ℝ).toBasis := by
  apply Matrix.ext
  intro i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.basisFun_apply]
  change inner ℝ (A (OAI.Analysis.PDE.Dirichlet.coordinateVector i)) (OAI.Analysis.PDE.Dirichlet.coordinateVector j) =
    inner ℝ (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (A (OAI.Analysis.PDE.Dirichlet.coordinateVector j))
  exact hA _ _

theorem operatorCoordinateMatrix_posSemidef {n s : ℕ}
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hA : A.toLinearMap.IsSymmetric)
    (hpos : ∀ x, 0 ≤ inner ℝ (A x) x) : (OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix A).PosSemidef := by
  rw [operatorCoordinateMatrix_eq_toMatrix A hA]
  exact (LinearMap.posSemidef_toMatrix_iff _).mpr ⟨hA, hpos⟩

theorem operatorCoordinateMatrix_posDef {n s : ℕ}
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hA : A.toLinearMap.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < inner ℝ (A x) x) : (OAI.Analysis.PDE.Dirichlet.operatorCoordinateMatrix A).PosDef := by
  have hn (x) : 0 ≤ inner ℝ (A x) x := by
    by_cases hx : x = 0
    · simp only [hx, map_zero, inner_zero_left]
      exact le_rfl
    · exact (hpos x hx).le
  have hps := operatorCoordinateMatrix_posSemidef A hA hn
  apply hps.posDef_iff_isUnit.mpr
  rw [operatorCoordinateMatrix_eq_toMatrix A hA, LinearMap.isUnit_toMatrix_iff,
    LinearMap.isUnit_iff_ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hne
  have hp := hpos x hne
  change A x = 0 at hx
  rw [hx, inner_zero_left] at hp
  exact (lt_irrefl 0) hp

end OAI.Analysis.PDE.Nonlinear
