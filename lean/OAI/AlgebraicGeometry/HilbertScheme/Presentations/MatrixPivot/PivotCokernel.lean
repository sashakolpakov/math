import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.Cokernel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.ColumnCokernel

/-! # Pivot Cokernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.PivotCokernel.Grassmannian

noncomputable section

/-! Pivot equations for an arbitrary rectangular presentation matrix and its actual cokernel. -/

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {μ : Type w} {ν : Type z}
variable [Fintype ι] [Fintype μ]
variable [DecidableEq ι] [DecidableEq μ]

def fullPivotResidual (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν) : Matrix ν μ R :=
  Cokernel.Grassmannian.pivotResidual (A.submatrix b a) (A.submatrix b id) (A.submatrix id a) A

def normalizedPivotColumns (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν) : Matrix ν ι R :=
  A.submatrix id a * (A.submatrix b a)⁻¹

omit [Fintype μ] [DecidableEq μ] in
theorem normalizedPivotColumns_rows (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν)
    (h : IsUnit (A.submatrix b a).det) :
    (normalizedPivotColumns A a b).submatrix b id = 1 := by
  ext i j
  exact congrArg (fun M : Matrix ι ι R => M i j) (Matrix.mul_nonsing_inv (A.submatrix b a) h)

omit [Fintype μ] [DecidableEq μ] in
theorem fullPivotResidual_factorization (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν)
    (h : IsUnit (A.submatrix b a).det) (hres : fullPivotResidual A a b = 0) :
    A = normalizedPivotColumns A a b * A.submatrix b id :=
  sub_eq_zero.mp ((Cokernel.Grassmannian.pivotResidual_zero_iff (A.submatrix b a) (A.submatrix b id)
    (A.submatrix id a) A h).mp hres)

omit [Fintype μ] [DecidableEq μ] in
theorem fullPivotResidual_zero_of_factorization (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν)
    (h : IsUnit (A.submatrix b a).det) (F : Matrix ι μ R) (hF : A = A.submatrix id a * F) :
    fullPivotResidual A a b = 0 := by
  have hrow : A.submatrix b id = A.submatrix b a * F := by
    ext i j
    exact congrArg (fun M : Matrix ν μ R => M (b i) j) hF
  apply (Cokernel.Grassmannian.pivotResidual_zero_iff (A.submatrix b a) (A.submatrix b id) (A.submatrix id a) A h).mpr
  rw [hrow, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ h]
  exact sub_eq_zero.mpr hF

theorem normalizedPivotColumns_range_le (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν) :
    (Matrix.toLin' (normalizedPivotColumns A a b)).range ≤ (Matrix.toLin' A).range := by
  have hC : Matrix.toLin' (A.submatrix id a) = (Matrix.toLin' A).comp (Normalized.Quotients.Grassmannian.selectedBasisMap a) := by
    change Matrix.toLin' (A.submatrix id a) =
      (Matrix.toLin' A).comp (Matrix.toLin' ((1 : Matrix μ μ R).submatrix id a))
    rw [← Matrix.toLin'_mul]
    exact congrArg Matrix.toLin' (Matrix.mul_submatrix_one (Equiv.refl μ) a A).symm
  rw [normalizedPivotColumns, Matrix.toLin'_mul, hC, LinearMap.comp_assoc]
  exact LinearMap.range_comp_le_range _ _

theorem fullPivotResidual_range (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν)
    (h : IsUnit (A.submatrix b a).det) (hres : fullPivotResidual A a b = 0) :
    (Matrix.toLin' A).range = (Matrix.toLin' (normalizedPivotColumns A a b)).range := by
  apply le_antisymm _ (normalizedPivotColumns_range_le A a b)
  have he := congrArg Matrix.toLin' (fullPivotResidual_factorization A a b h hres)
  rw [Matrix.toLin'_mul] at he
  rw [he]
  exact LinearMap.range_comp_le_range _ _

def fullMatrixPivotCokernelEquiv (A : Matrix ν μ R) (a : ι → μ) (b : ι → ν)
    (h : IsUnit (A.submatrix b a).det) (hres : fullPivotResidual A a b = 0) :
    ((ν → R) ⧸ (Matrix.toLin' A).range) ≃ₗ[R] ({j : ν // j ∉ Set.range b} → R) :=
  (Submodule.quotEquivOfEq _ _ (fullPivotResidual_range A a b h hres)).trans
    (Normalized.ColumnCokernel.Grassmannian.normalizedColumnCokernelEquiv b (normalizedPivotColumns A a b) (normalizedPivotColumns_rows A a b h))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.MatrixPivot.PivotCokernel.Grassmannian
