import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameLinearMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.OfErasedProducts
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Determinant Frame Normalizer Determinant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameNormalizerDeterminant

noncomputable section

/-! The determinant normalization map is a diagonal multiple of the
adjugate matrix. Its determinant is the frame discriminant to power r-1. -/
open scoped BigOperators Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {κ : Type v} [Fintype κ]

theorem basisFun_det_update_eq_cramer (b : κ → κ → R) (w : κ → R) (i : κ) :
    (Pi.basisFun R κ).det (Function.update b i w) = Matrix.cramer (Matrix.of b).transpose w i := by
  rw [Pi.basisFun_det_apply, Matrix.cramer_transpose_apply]
  rfl

def determinantFrameNormalizerMatrix (b : κ → κ → R) (v : κ → R) : Matrix κ κ R :=
  Matrix.diagonal (fun i => ∏ j ∈ (Finset.univ : Finset κ).erase i,
    (Pi.basisFun R κ).det (Function.update b j v)) * (Matrix.of b).transpose.adjugate

theorem determinantFrameLinearMap_eq_matrix (b : κ → κ → R) (v : κ → R) :
    DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun R κ) b v = Matrix.toLin' (determinantFrameNormalizerMatrix b v) := by
  apply LinearMap.ext
  intro w
  funext i
  rw [DeterminantFrameLinearMap.determinantFrameLinearMap_apply, Matrix.toLin'_apply]
  unfold determinantFrameNormalizerMatrix
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, ← Matrix.cramer_eq_adjugate_mulVec]
  change (Pi.basisFun R κ).det (Function.update b i w) *
      (∏ j ∈ (Finset.univ : Finset κ).erase i, (Pi.basisFun R κ).det (Function.update b j v)) =
    (∏ j ∈ (Finset.univ : Finset κ).erase i, (Pi.basisFun R κ).det (Function.update b j v)) *
      Matrix.cramer (Matrix.of b).transpose w i
  rw [basisFun_det_update_eq_cramer, mul_comm]

theorem determinantFrameLinearMap_det (b : κ → κ → R) (v : κ → R) :
    LinearMap.det (DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun R κ) b v) =
      ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R κ) b v ^ (Fintype.card κ - 1) := by
  rw [determinantFrameLinearMap_eq_matrix, LinearMap.det_toLin']
  unfold determinantFrameNormalizerMatrix
  rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_adjugate, Matrix.det_transpose,
    Product.OfErasedProducts.product_of_erased_products]
  change (∏ j, (Pi.basisFun R κ).det (Function.update b j v)) ^ (Fintype.card κ - 1) *
      (Matrix.of b).det ^ (Fintype.card κ - 1) = _
  rw [ProjectiveFrame.Discriminant.projectiveFrameDiscriminant, Pi.basisFun_det_apply, mul_pow, mul_comm]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameNormalizerDeterminant
