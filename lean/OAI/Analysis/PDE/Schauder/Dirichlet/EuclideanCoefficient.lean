import OAI.Analysis.PDE.Nonlinear.MatrixPositive
import OAI.Analysis.Normed.Function.Holder.Banach.Linear

open InnerProductSpace
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance euclideanCoefficientMatrixGroup : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance euclideanCoefficientMatrixSpace : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))

/-- Coordinate matrix in the Hessian contraction convention. -/
def euclideanCoefficientMatrix : (E →L[ℝ] E) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ where
  toFun A i j := inner ℝ (A (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)
  map_add' A B := by
    ext i j
    exact inner_add_left _ _ _
  map_smul' c A := by
    ext i j
    exact real_inner_smul_left _ _ _

theorem euclideanCoefficientMatrix_eq_toMatrix (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) :
    euclideanCoefficientMatrix A = A.toLinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis := by
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.basisFun_apply]
  exact hA _ _

theorem euclideanCoefficientMatrix_posDef (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < inner ℝ (A x) x) :
    (euclideanCoefficientMatrix A).PosDef := by
  have hn (x) : 0 ≤ inner ℝ (A x) x := by
    by_cases hx : x = 0
    · simp only [hx, map_zero, inner_zero_left]
      exact le_rfl
    · exact (hpos x hx).le
  have hps : (euclideanCoefficientMatrix A).PosSemidef := by
    rw [euclideanCoefficientMatrix_eq_toMatrix A hA]
    exact (LinearMap.posSemidef_toMatrix_iff _).mpr ⟨hA, hn⟩
  apply hps.posDef_iff_isUnit.mpr
  rw [euclideanCoefficientMatrix_eq_toMatrix A hA, LinearMap.isUnit_toMatrix_iff,
    LinearMap.isUnit_iff_ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  by_contra hne
  have hp := hpos x hne
  change A x = 0 at hx
  rw [hx, inner_zero_left] at hp
  exact (lt_irrefl 0) hp

theorem ellipticTrace_eq_nondivergenceOperator
    (A : E → E →L[ℝ] E) (u : E → ℝ) (hu : ContDiff ℝ 2 u) (x : E)
    (hA : (A x).toLinearMap.IsSymmetric) :
    OAI.Analysis.PDE.Elliptic.ellipticTrace A u x =
      nondivergenceOperator (fun y => euclideanCoefficientMatrix (A y)) u x := by
  rw [OAI.Analysis.PDE.Elliptic.ellipticTrace, OAI.Analysis.PDE.Nonlinear.trace_comp_eq_coordinate_contraction
    (EuclideanSpace.basisFun _ _) _ _ hA]
  unfold nondivergenceOperator
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [EuclideanSpace.basisFun_apply]
  rw [OAI.Analysis.PDE.Elliptic.inner_fderiv_gradient hu]
  rfl

end OAI.Analysis.PDE.Schauder
