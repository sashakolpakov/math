import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelDimensionOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.KernelScalarEmbedding
import Mathlib.RingTheory.TensorProduct.Free

/-! # Kernel Base Change Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelBaseChangeDimension

noncomputable section

/-! Matrix coefficient extension computes the kernel dimension of the actual base-changed linear map. A residue-field kernel bound of one therefore gives a scalar embedding of the original local-ring matrix kernel. -/

universe u

variable {R : Type u} [CommRing R]
variable {μ ν : Type u} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]

omit [DecidableEq ν] in
theorem matrixKernel_baseChange_finrank {K : Type u} [Field K] [Algebra R K] (B : Matrix ν μ R) :
    Module.finrank K ((Matrix.toLin' B).baseChange K).ker =
      Module.finrank K (Matrix.toLin' (B.map (algebraMap R K))).ker := by
  let bm := Algebra.TensorProduct.basis K (Pi.basisFun R μ)
  let bn := Algebra.TensorProduct.basis K (Pi.basisFun R ν)
  have hb : LinearMap.toMatrix bm bn ((Matrix.toLin' B).baseChange K) = B.map (algebraMap R K) := by
    rw [LinearMap.toMatrix_baseChange]
    congr 1
    exact LinearMap.toMatrix_toLin (Pi.basisFun R μ) (Pi.basisFun R ν) B
  have hr : (B.map (algebraMap R K)).rank = Module.finrank K ((Matrix.toLin' B).baseChange K).range := by
    rw [Matrix.rank_eq_finrank_range_toLin _ bn bm, ← hb, Matrix.toLin_toMatrix]
  have h₁ := LinearMap.finrank_range_add_finrank_ker ((Matrix.toLin' B).baseChange K)
  rw [Module.finrank_eq_card_basis bm] at h₁
  have h₂ := KernelDimensionOpen.field_matrix_kernel_dimension_add_rank (B.map (algebraMap R K))
  omega

omit [DecidableEq ν] in
theorem localMatrixKernel_exists_scalar_embedding [IsLocalRing R] (B : Matrix ν μ R)
    (h : Module.finrank (IsLocalRing.ResidueField R)
      (Matrix.toLin' (B.map (algebraMap R (IsLocalRing.ResidueField R)))).ker ≤ 1) :
    ∃ φ : (Matrix.toLin' B).ker →ₗ[R] R, Function.Injective φ := by
  apply Local.KernelScalarEmbedding.localKernel_exists_scalar_embedding
  rw [matrixKernel_baseChange_finrank]
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelBaseChangeDimension
